\HDRa{Rely-Guarantee Algebra}\label{ha:RGAlg}
\begin{code}
module RGAlgebra where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import PrettyPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
import CalcAlphabets
import CalcSysTypes
import CalcSimplify
import CalcRecogniser
import CalcRun
-- import StdPredicates
-- import StdLaws
-- import CalcZipper
-- import CalcSteps
import StdUTPPredicates
import StdUTPLaws
import UTCPCReduce
\end{code}

\begin{code}
-- import Debug.Trace
-- dbg str x = trace (str++show x) x
\end{code}

{
\def\rgname#1{\textsf{#1}}

We rapid prototype the emerging Rely-Guarantee Algebra work.

\HDRb{Primitive Atomic Commands}


\RLEQNS{
   r \subseteq \Sigma \times \Sigma
}
\begin{code}
r = Var "r"
\end{code}



\RLEQNS{
     π(r) &=& \Pi(\sigma,\sigma'), (\sigma,\sigma') \in r
}
\begin{code}
n_pi = "\960"  -- pi
_pi r = App n_pi [r]

piEntry :: (Show s) => (String, Entry s)
piEntry
 = ( n_pi
   , ExprEntry
       subAny
       (defEPrint n_pi)
       noDefn
       (justMakes $ App n_pi)
       noEq )
\end{code}



\RLEQNS{
   ϵ(r) &=& \mathcal{E}(\sigma,\sigma'), (\sigma,\sigma') \in r
}
\begin{code}
n_eps = "\x3f5" -- lunate epsilon
eps r = App n_eps [r]

epsEntry :: (Show s) => (String, Entry s)
epsEntry
 = ( n_eps
   , ExprEntry
       subAny
       (defEPrint n_eps)
       noDefn
       (justMakes $ App n_eps)
       noEq )
\end{code}

\def\id{\rgname{id}}
\def\univ{\rgname{univ}}

Simple relations: \id, \univ
\begin{code}
_id = Var "id"
univ = Var "univ"
\end{code}



\def\stutter{ii}

\RLEQNS{
   \stutter &=& \pi(\id)
}
\begin{code}
n_ii = "ii"
ii = App n_ii [] -- we want to define this

iiDefn  =  _pi _id

iiEntry :: (Show s) => (String, Entry s)
iiEntry
 = ( n_ii
   , ExprEntry
       subAny
       (\ _ _ -> n_ii)
       (\_ _ -> Just ("ii", iiDefn))
       (justMakes $ App n_ii)
       noEq )
\end{code}


\RLEQNS{
   \pi &=& \pi(\univ)
}
\RLEQNS{
   \epsilon &=& \epsilon(\univ)
}
\RLEQNS{
   r \subseteq \Sigma \times \Sigma
\\ \stutter &=& \pi(\id)
\\ \pi &=& \pi(\univ)
\\ \epsilon &=& \epsilon(\univ)
}



\HDRb{RG Dictionary}
\begin{code}
rgDict :: (Ord s, Show s) => Dict s
rgDict
 = makeDict
    [ piEntry
    , epsEntry
    , iiEntry
    ]
\end{code}
}

\HDRb{Top Level Support}

\begin{code}
rgshow :: (Show s, Ord s) => Pred s -> String
rgshow = pmdshow 80 rgDict noStyles . buildMarks

rgput :: (Show s, Ord s) => Pred s -> IO ()
rgput = putStrLn . rgshow

rgeput :: (Show s, Ord s) => Expr s -> IO ()
rgeput = rgput . Atm

rgcalc pr = calcREPL rgDict [] $ buildMarks pr
\end{code}
