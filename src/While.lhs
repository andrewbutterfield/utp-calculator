\HDRa{The ``While'' Language}\label{ha:While}
\begin{code}
module While where
-- import Utilities
-- import qualified Data.Map as M
-- import Data.List
-- import Data.Char
-- import Data.Maybe
-- import Debug.Trace
import PrettyPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
-- import CalcAlphabets
-- import CalcSimplify
-- import CalcRecogniser
-- import CalcRun
-- import StdPredicates
-- import CalcZipper
-- import CalcSteps
import StdLaws
\end{code}

\HDRb{Introduction to ``While''}\label{hb:While-intro}

This is an example of the use of the UTP Calculator,
to help calculate the semantics of a simple ``while'' language.
It illustrates how we can exploit our ability to create laws
in order to skip over tricky aspects of working from basic definitions.

\HDRb{Syntax of ``While''}\label{hb:While-syntax}

We use the fairly standard UTP mathematical syntax,
assuming uninterpreted expressions, with a simple implicit typing system.

\HDRc{Variables of ``While''}\label{hc:While-vars}

\RLEQNS{
   u,v,w &\in& V & \say{Variables}
}
\begin{code}
u = "u" ; vu = Var u
v = "v" ; vv = Var v
w = "w" ; vw = Var w
\end{code}

\HDRc{Expressions of ``While''}\label{hc:While-expr}

\RLEQNS{
   e &\in& E & \say{Expressions}
\\ b,c &\in& E & \say{Boolean Valued}
}
\begin{code}
e = Var "e"
b = Var "b"
c = Var "c"
\end{code}

\HDRc{Statements of ``While''}\label{hc:While-stmt}

We list the composite components in decreasing order
of their precedence, so the first binds tightest.
\RLEQNS{
   p,q &\in& W & \say{While programs}
\\ &\defs& skip & \say{Do nothing}
\\ &|& x:=e  & \say{Assignment}
\\ &|& c * p & \say{Iteration (``While'')}
\\ &|& p ; q & \say{Sequencing}
\\ &|& p \cond c q & \say{Conditional}
}
\begin{code}
pP          =  pvar nP                        ; nP   = "P"
pQ          =  pvar nQ                        ; nQ   = "Q"
skip        =  comp nskp []                   ; nskp = "skip"
x ^= e      =  comp nasg [atm $ Var x, atm e] ; nasg = "asg"
while c p   =  comp nwhl [atm c, p]           ; nwhl = "while"
seqc p q    =  comp nseq [p, q]               ; nseq = "seq"
cond c p q  =  comp ncnd [atm c, p, q]        ; ncnd = "cond"
\end{code}

Pretty printers for the above composites:
\begin{code}
precAsg = precSpacer 9 + 5
precWhl = precSpacer 7 + 5
precSqc = precSpacer 4 + 5
precCnd = precSpacer 3 + 5

-- Dict s -> MarkStyle -> Int -> [MPred s] -> PP

ppSkip _ _ _ _ = ppa nskp

ppAsg :: (Show s, Ord s)
       => Dict s -> MarkStyle -> Int -> [MPred s] -> PP
ppAsg d ms p [mpr1,mpr2]
 = paren p precAsg
     $ ppopen " := " [ mshowp d ms precAsg mpr1
                     , mshowp d ms precAsg mpr2 ]
ppAsg d ms p mprs = pps styleRed $ ppa "invalid-:="

ppSeqc :: (Show s, Ord s)
       => Dict s -> MarkStyle -> Int -> [MPred s] -> PP
ppSeqc d ms p [mpr1,mpr2]
 = paren p precSqc
     $ ppopen " ; " [ mshowp d ms precSqc mpr1
                    , mshowp d ms precSqc mpr2 ]
ppSeqc d ms p mprs = pps styleRed $ ppa "invalid-;"
\end{code}

\HDRb{Alphabet of ``While''}\label{hb:While-alpha}

\HDRb{Semantics of ``While''}\label{hb:While-semantics}

\HDRb{Reductions for ``While''}\label{hb:While-reduce}

\HDRb{Laws of ``While''}\label{hb:While-laws}

\HDRb{Dictionary for ``While''}\label{hb:While-laws}

\begin{code}
dSkip = ( nskp
        , PredEntry
            False
            ppSkip
            (pNoChg nskp)
            (pNoChg nskp)
        )

dAsg :: (Show s, Ord s) => (String,Entry s)
dAsg = ( nasg
        , PredEntry
            False
            ppAsg
            (pNoChg nasg)
            (pNoChg nasg)
        )

dSeqc :: (Show s, Ord s) => (String,Entry s)
dSeqc = ( nseq
        , PredEntry
            False
            ppSeqc
            (pNoChg nseq)
            (pNoChg nseq)
        )

dictWhile :: (Ord s, Show s) => Dict s
dictWhile
 = makeDict
    [ dSkip
    , dAsg
    , dSeqc
    ]

whileDict :: (Ord s, Show s) => Dict s
whileDict
 =  dictWhile
    `dictMrg` stdDict
\end{code}

\HDRb{Tests for ``While''}\label{hb:While-tests}
