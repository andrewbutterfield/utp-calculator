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
import CalcAlphabets
import CalcSimplify
-- import CalcRecogniser
import CalcRun
import StdPredicates
-- import CalcZipper
-- import CalcSteps
import StdUTPLaws
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

We have numbers (integers), basic arithmetic and comparisons
\RLEQNS{
   e &\in& E & \say{Expressions}
\\ &\defs& n & \say{---Numbers}
\\ &  |  & v & \say{---Variables}
\\ &  |  & e + e & \say{---Addition}
\\ &  |  & -e & \say{---Negation}
\\ &  |  & e < e & \say{--Less Than}
\\ b,c &\in& E & \say{Boolean Valued}
}
\begin{code}
e = Var "e";
b = Var "b"
c = Var "c"

add e f = App nadd [e, f] ; nadd = "add"
minus e = App nmns [e]    ; nmns = "minus"
lt e f  = App nlt [e,f]   ; nlt = "lt"
\end{code}

\HDRc{Statements of ``While''}\label{hc:While-stmt}

We list the composite components in decreasing order
of their precedence, so the first binds tightest.
\RLEQNS{
   p,q &\in& W & \say{While programs}
\\ &\defs& skip & \say{---Do nothing}
\\ &|& x:=e  & \say{---Assignment}
\\ &|& c * p & \say{---Iteration (``While'')}
\\ &|& p ; q & \say{---Sequencing}
\\ &|& p \cond c q & \say{---Conditional}
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

\HDRc{Pretty-Printing ``While''}

\begin{code}
precAsg = precSpacer 9 + 5
precWhl = precSpacer 7 + 5
precSqc = precSpacer 4 + 5
precCnd = precSpacer 3 + 5

-- Dict s -> MarkStyle -> Int -> [MPred s] -> PP

ppWSkip _ _ _ _ = ppa nskp

ppAsg :: (Show s, Ord s)
       => Dict s -> MarkStyle -> Int -> [MPred s] -> PP
ppAsg d ms p [mpr1,mpr2]
 = paren p precAsg
     $ ppopen " := " [ mshowp d ms precAsg mpr1
                     , mshowp d ms precAsg mpr2 ]
ppAsg d ms p mprs = pps styleRed $ ppa "invalid-:="

ppWhl :: (Show s, Ord s)
       => Dict s -> MarkStyle -> Int -> [MPred s] -> PP
ppWhl d ms p [mpr1,mpr2]
 = paren p precWhl
     $ ppopen " * " [ mshowp d ms precWhl mpr1
                    , mshowp d ms precWhl mpr2 ]
ppWhl d ms p mprs = pps styleRed $ ppa "invalid-*"

ppSeqc :: (Show s, Ord s)
       => Dict s -> MarkStyle -> Int -> [MPred s] -> PP
ppSeqc d ms p [mpr1,mpr2]
 = paren p precSqc
     $ ppopen " ; " [ mshowp d ms precSqc mpr1
                    , mshowp d ms precSqc mpr2 ]
ppSeqc d ms p mprs = pps styleRed $ ppa "invalid-;"

ppCnd d ms p [mprc,mprt,mpre]
 = paren p precCnd
      $ pplist [ mshowp d ms precCnd mprt
               , ppa " <| "
               , mshowp d ms 0 mprc
               , ppa " |> "
               , mshowp d ms precCnd mpre ]
ppCnd d ms p mprs = pps styleRed $ ppa "invalid-<|>"
\end{code}

\HDRb{Semantics of ``While''}\label{hb:While-semantics}

\HDRc{Alphabet of ``While''}\label{hb:While-alpha}

This is a theory of designs,
so we have $ok$ and $ok'$.
\begin{code}
ok  = "ok"  ; vok  = Var ok
ok' = "ok'" ; vok' = Var ok'
\end{code}

\begin{code}
wAlfDict = stdAlfDictGen [u,v,w]  -- script (dynamic)
                         [ok]     -- model (dynamic)
                         []       -- parameters (static)
\end{code}

\HDRc{Expression Semantics}

\HDRd{Addition}
\begin{code}
showAdd :: Show s => Dict s -> [Expr s] -> String
showAdd d [e,f] = "("++edshow d e++" + "++edshow d f++")"
showAdd d es = "<<BAD-ADD>>"

evalAdd d [Z 0,f] = ("+-lunit",f)
evalAdd d [e,Z 0] = ("+-runit",e)
evalAdd d [Z m,Z n] =  ("add",Z (m+n))
evalAdd d [e,f] = ("", add e f)
evalAdd d es = ("bad-add",App "?+" es)

dAdd :: Show s => (String, Entry s)
dAdd = ( nadd, ExprEntry True showAdd evalAdd )
\end{code}

\HDRd{Negation}
\begin{code}
showMinus :: Show s => Dict s -> [Expr s] -> String
showMinus d [e] = "-("++edshow d e++")"
showMinus d es = "<<BAD-MINUS>>"

evalMinus d [Z m] =  ("minus",Z $ negate m)
evalMinus d [e] = ("", minus e)
evalMinus d es = ("bad-minus",App "?-" es)

dMinus :: Show s => (String, Entry s)
dMinus = ( nmns, ExprEntry True showMinus evalMinus )
\end{code}

\HDRd{Less-Than}
\begin{code}
showLT :: Show s => Dict s -> [Expr s] -> String
showLT d [e,f] = "("++edshow d e++" < "++edshow d f++")"
showLT d es = "<<BAD-LT>>"

evalLT d [Z m,Z n] =  ("lt",B (m < n))
evalLT d [e,f] = ("", lt e f)
evalLT d es = ("bad-lt",App "?<" es)

dLT :: Show s => (String, Entry s)
dLT = ( nlt, ExprEntry True showLT evalLT )
\end{code}

\HDRc{Semantic Predicates}

\RLEQNS{
   P \design Q &\defs& ok \land P \implies ok' \land Q
}
\begin{code}
p |- q = comp ndsgn [p,q] ; ndsgn = "design"

precDsgn = precImp + 5

ppDsgn :: (Show s, Ord s)
       => Dict s -> MarkStyle -> Int -> [MPred s] -> PP
ppDsgn d ms p [mpr1,mpr2]
 = paren p precSqc
     $ ppopen " |- " [ mshowp d ms precSqc mpr1
                     , mshowp d ms precSqc mpr2 ]
ppDsgn d ms p mprs = pps styleRed $ ppa "invalid-|-"

defnDsgn :: Rewrite s
defnDsgn d [mpr1,mpr2]
 = ( "design"
   , mkImp (bAnd [atm vok,mpr1]) (bAnd [atm vok',mpr2]) )
\end{code}

\HDRc{Definitions for ``While''}\label{hb:While-alpha}

\RLEQNS{
}
\begin{code}

\end{code}
\HDRb{Reductions for ``While''}\label{hb:While-reduce}

\HDRb{Laws of ``While''}\label{hb:While-laws}

\HDRb{Dictionary for ``While''}\label{hb:While-laws}

\begin{code}
dSkip = ( nskp
        , PredEntry
            False
            ppWSkip
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

dWhl :: (Show s, Ord s) => (String,Entry s)
dWhl = ( nwhl
        , PredEntry
            False
            ppWhl
            (pNoChg nwhl)
            (pNoChg nwhl)
        )

dSqc :: (Show s, Ord s) => (String,Entry s)
dSqc = ( nseq
        , PredEntry
            False
            ppSeqc
            (pNoChg nseq)
            (pNoChg nseq)
        )

dCnd :: (Show s, Ord s) => (String,Entry s)
dCnd = ( ncnd
        , PredEntry
            False
            ppCnd
            (pNoChg ncnd)
            (pNoChg ncnd)
        )

dDsgn :: (Show s, Ord s) => (String,Entry s)
dDsgn = ( ndsgn
        , PredEntry
            False
            ppDsgn
            (pNoChg ndsgn)
            (pNoChg ndsgn)
        )

dictWhile :: (Ord s, Show s) => Dict s
dictWhile
 = makeDict
    [ dSkip
    , dAsg
    , dWhl
    , dSqc
    , dCnd
    , dDsgn
    , dAdd
    , dMinus
    , dLT
    ]

whileDict :: (Ord s, Show s) => Dict s
whileDict
 =  dictWhile
    `dictMrg` wAlfDict
    `dictMrg` stdDict
\end{code}

\HDRb{Tests for ``While''}\label{hb:While-tests}

\begin{code}
wshow :: (Show s, Ord s) => MPred s -> String
wshow = pmdshow 80 whileDict noStyles

wput :: (Show s, Ord s) => MPred s -> IO ()
wput = putStrLn . wshow


wcalc mpr = calcREPL whileDict mpr
wputcalc :: (Ord s, Show s) => MPred s -> IO ()
wputcalc mpr
  = do res <- wcalc mpr
       putStrLn "\n\nTRANSCRIPT:"
       putStrLn $ calcPrint res

wsimp :: (Show s, Ord s) => MPred s -> (String, MPred s)
wsimp mpr
  = (what,mpr')
  where (_,what,mpr') = simplify whileDict 42 mpr
wsimp2 :: (Show s, Ord s) => (String, MPred s) -> (String, MPred s)
wsimp2 = wsimp . snd
\end{code}
