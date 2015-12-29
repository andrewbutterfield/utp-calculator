\HDRa{The ``While'' Language}\label{ha:While}
\begin{code}
module While where
-- import Utilities
-- import qualified Data.Map as M
-- import Data.List
-- import Data.Char
-- import Data.Maybe
-- import Debug.Trace
-- import PrettyPrint
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
-- import StdLaws
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
p = "P" ; pP = pvar p
q = "Q" ; pQ = pvar q
skip        =  comp "skip"  []
x ^= e      =  comp "asg"   [atm $ Var x, atm e]
while c p   =  comp "while" [atm c, p]
seqc p q    =  comp "seq"   [p, q]
cond c p q  =  comp "cond"  [atm c, p, q]
\end{code}

Pretty printers for the above:
\begin{code}

\end{code}

\HDRb{Alphabet of ``While''}\label{hb:While-alpha}

\HDRb{Semantics of ``While''}\label{hb:While-semantics}

\HDRb{Reductions for ``While''}\label{hb:While-reduce}

\HDRb{Laws of ``While''}\label{hb:While-laws}

\HDRb{Tests for ``While''}\label{hb:While-tests}
