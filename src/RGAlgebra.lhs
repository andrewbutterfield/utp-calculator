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

\HDRb{Definitions}


\HDRc{Primitive Atomic Commands}


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

piEntry :: (Show s) => Dict s
piEntry
 = entry n_pi
   $ ExprEntry
       subAny
       (defEPrint n_pi)
       noDefn
       (justMakes $ App n_pi)
       noEq
\end{code}



\RLEQNS{
   ϵ(r) &=& \mathcal{E}(\sigma,\sigma'), (\sigma,\sigma') \in r
}
\begin{code}
n_eps = "\x3f5" -- lunate epsilon
eps r = App n_eps [r]

epsEntry :: (Show s) => Dict s
epsEntry
 = entry n_eps
   $ ExprEntry
       subAny
       (defEPrint n_eps)
       noDefn
       (justMakes $ App n_eps)
       noEq
\end{code}

\def\id{\rgname{id}}
\def\univ{\rgname{univ}}
\def\emp{\rgname{$\setof{}$}}

Simple relations and predicates: \id, \univ, $\emp$
\begin{code}
n_id   = "id"   ; _id  = Var n_id
n_univ = "univ" ; univ = Var n_univ
n_emp  = "{}"   ; emp  = Var n_emp
n_top  = "T"    ; top  = Var n_top
\end{code}



\def\stutter{ii}

\RLEQNS{
   \stutter &=& \pi(\id)
}
\begin{code}
n_ii = "ii"
ii = App n_ii [] -- we want to define this
iiPrint _ _ = n_ii
iiDefn _ _  =  edefn n_ii $ _pi _id

iiEntry :: (Show s) => Dict s
iiEntry
 = entry n_ii
   $ ExprEntry
       subAny
       iiPrint
       iiDefn
       (justMakes $ App n_ii)
       noEq
\end{code}


\RLEQNS{
   \pi &=& \pi(\univ)
}
\begin{code}
n_piU = "piU"
piU = App n_piU []
piUPrint _ _ = n_pi
piUDefn _ _ = edefn "\960" $ _pi univ

piUEntry :: (Show s) => Dict s
piUEntry
 = entry n_piU
   $ ExprEntry
       subAny
       piUPrint
       piUDefn
       (justMakes $ App n_piU)
       noEq
\end{code}

\RLEQNS{
   \epsilon &=& \epsilon(\univ)
}
\begin{code}
n_epsU = "epsU"
epsU = App n_epsU []
epsUPrint _ _ = n_eps
epsUDefn _ _ = edefn "\1013" $ eps univ

epsUEntry :: (Show s) => Dict s
epsUEntry
 = entry n_epsU
   $ ExprEntry
       subAny
       epsUPrint
       epsUDefn
       (justMakes $ App n_epsU)
       noEq
\end{code}

\HDRc{Tests as a Boolean Algebra}

\RLEQNS{
   p &\subseteq& \Sigma
}
\begin{code}
p = Var "p"
\end{code}

\RLEQNS{
     τ(p) &=& \mbox{if $p$ then terminate else $\top$}
}
\begin{code}
n_tau = "\964"  -- tau
tau p = App n_tau [p]

tauEntry :: (Show s) => Dict s
tauEntry
 = entry n_tau
   $ ExprEntry
       subAny
       (defEPrint n_tau)
       noDefn
       (justMakes $ App n_tau)
       noEq
\end{code}


\HDRb{Laws}

\HDRc{Reduction Steps}

\begin{code}
rgReduce :: (Ord s, Show s) => RWFun s
         -- Dict s
         -- -> [Pred s]  -- Invariants
         -- -> Pred s    -- Target Predicate
         -- -> Maybe (String, Pred s, Bool)
\end{code}

\RLEQNS{
   \pi(\emp) &=& \top
\\ \epsilon(\emp) &=& \top
}
\begin{code}
rgReduce d _ (Atm (App anm [Var enm]))
 | enm == n_emp && (anm == n_pi || anm == n_eps)
   = Just ( "Empty Rel is infeasible", Atm top, True)
\end{code}

\begin{code}
rgReduce _ _ _ = Nothing
\end{code}

\HDRc{law Entry}

\begin{code}
lawEntry :: (Ord s, Show s) => Dict s
lawEntry = entry laws $ LawEntry [rgReduce] [] []
\end{code}

\HDRb{RG Dictionary}
\begin{code}
rgDict :: (Ord s, Show s) => Dict s
rgDict
 = mergeDicts
    [ dictVersion "RGAlgebra 0.1"
    , piEntry
    , epsEntry
    , iiEntry
    , piUEntry
    , epsUEntry
    , tauEntry
    , lawEntry
    ]
\end{code}
}

\HDRb{Top Level Support}

\begin{code}
rgshow :: (Show s, Ord s) => Pred s -> String
rgshow = pdshow 80 rgDict noStyles

rgput :: (Show s, Ord s) => Pred s -> IO ()
rgput = putStrLn . rgshow

rgeput :: (Show s, Ord s) => Expr s -> IO ()
rgeput = rgput . Atm

rgcalc pr = calcREPL rgDict [] pr
\end{code}
