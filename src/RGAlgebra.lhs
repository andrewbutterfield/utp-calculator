\HDRa{Rely-Guarantee Algebra}\label{ha:RGAlg}
\begin{code}
module RGAlgebra where
--import IOUtil
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import NiceSymbols
import PrettyPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
import DictAbstractions
import CalcAlphabets
import CalcSysTypes
import CalcSimplify
import CalcRecogniser
import CalcRun
import StdSets
import StdPredicates
-- import StdLaws
-- import CalcZipper
-- import CalcSteps
-- import StdUTPPredicates
-- import StdUTPLaws
-- import UTCPCReduce
\end{code}

\begin{code}
-- import Debug.Trace
-- dbg str x = trace (str++show x) x
\end{code}

We rapid prototype the emerging Rely-Guarantee Algebra work.
We organise this based on the FM2016 paper (citation needed).

\HDRb{Concurrent Refinement Algebra}

Concurrent Refinement Algebra (CRA):
\[
(\mathcal C,\sqcap,\sqcup,;,\parallel,\bot,\top,\nil,\Skip)
\]

We have:
\RLEQNS{
       & \top
\\ \nil &      & \alf
\\     & \chaos
\\ & \bot
}
\begin{code}
n_top  = _top    ; top  = PVar n_top
n_bot = _bot ; bot = PVar n_bot
n_nil = mathBold "nil" ; nil = PVar n_nil
n_skip = mathBold "skip"; skip = PVar n_skip
n_alf = _alpha ; alf = PVar n_alf
n_chaos = mathBold "chaos" ; chaos = PVar n_chaos
\end{code}

\begin{center}
\begin{tabular}{|c|c|c|c|c|c|}
  \hline
    & assoc & comm & idem & unit & zero
  \\\hline
  $\sqcap$ & \checkmark & \checkmark & \checkmark & $\top$ & $\bot$
  \\\hline
  $\sqcup$ & \checkmark & \checkmark & \checkmark & $\bot$ & $\top$
  \\\hline
\end{tabular}
\end{center}

\begin{code}
n_meet = _sqcap

meetBundle :: (Ord s, Show s) => ( [Pred s] -> Pred s, Dict s)
meet       :: (Ord s, Show s) =>   [Pred s] -> Pred s
meetEntry  :: (Ord s, Show s) =>                       Dict s

meetBundle = opSemiLattice n_meet bot top precOr
meet = fst meetBundle
meetEntry = snd meetBundle

n_join = _sqcup

joinBundle :: (Ord s, Show s) => ( [Pred s] -> Pred s, Dict s)
join       :: (Ord s, Show s) =>   [Pred s] -> Pred s
joinEntry  :: (Ord s, Show s) =>                       Dict s

joinBundle = opSemiLattice n_join top bot precAnd
join = fst joinBundle
joinEntry = snd joinBundle
\end{code}

\HDRc{Primitive Atomic Commands}


\RLEQNS{
   r \subseteq \Sigma \times \Sigma
}
\begin{code}
n_Sigma = _Sigma ; sigma = Var n_Sigma
r     = Var "r"
\end{code}



\RLEQNS{
     π(r) &=& \Pi(\sigma,\sigma'), (\sigma,\sigma') \in r
}
\begin{code}
n_pi = _pi  -- pi
mkpi r = App n_pi [r]

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
n_eps = _epsilon -- lunate epsilon
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

Simple relations and predicates: \id, \univ, $\emp$
\begin{code}
n_id   = "id"   ; _id  = Var n_id
n_univ = "univ" ; univ = Var n_univ
n_emp  = "{}"   ; emp  = Var n_emp
\end{code}


\RLEQNS{
   \stutter &=& \pi(\id)
}
\begin{code}
n_ii = "ii"
ii = App n_ii [] -- we want to define this
iiPrint _ _ = n_ii
iiDefn _ _  =  edefn n_ii $ mkpi _id

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
n_piU = _pi++"U"
piU = App n_piU []
piUPrint _ _ = n_pi
piUDefn _ _ = edefn _pi $ mkpi univ

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
n_epsU = _epsilon++"U"
epsU = App n_epsU []
epsUPrint _ _ = n_eps
epsUDefn _ _ = edefn _epsilon $ eps univ

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
n_tau = _tau  -- tau
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

We need sequential composition (we keep the ; explicit):
\begin{code}
n_seq = ";" ; mkSeq t1 t2 = Comp n_seq [t1,t2]
ppSeq sCP d p ts
 = paren p precOr  -- we assume join is like or
     $ ppopen (pad n_seq)
     $ ppwalk 1 (sCP precOr) ts

seqEntry :: (Ord s, Show s) => Dict s
seqEntry
 = entry n_seq $ PredEntry subAny ppSeq [] noDefn noDefn
\end{code}

\RLEQNS{
   \pre~ t &=& t \sqcap \lnot t \bot
\\  &=& t \sqcap (\lnot t) \seq \bot
}
\begin{code}
n_pre = mathSansBold "pre"
precPre = precNot -- for now
expandPre d t = meet [ t, mkSeq (mkNot t) bot ]

preBuild :: (Ord s, Show s) => ( Pred s -> Pred s, Dict s )
pre      :: (Ord s, Show s) =>   Pred s -> Pred s
preEntry :: (Ord s, Show s) =>                     Dict s

preBuild = prefixPT n_pre precPre $ Just expandPre
pre      = fst preBuild
preEntry = snd preBuild
\end{code}

\RLEQNS{
   \setof p &=& \pre~\tau(p)
\\ &=& \tau(p) \sqcap \tau(\overline{p})\bot
}
\begin{code}
n_assert = "{}"
assert t = Comp n_assert [t]

precAssert = precNot -- for now
ppAssert sCP d p [t]
 = paren p precAssert
       $ pplist [ppa "{", sCP precPre 0 t, ppa "}" ]
ppAssert sCP d p _ = pps styleRed $ ppa ("invalid-"++n_assert)

assertDefn d [t]
  = Just ( n_assert, pre $ Atm $ tau p, True )

assertEntry :: (Ord s, Show s) => Dict s
assertEntry
 = entry n_assert $ PredEntry subAny ppAssert [] assertDefn noDefn
\end{code}

\RLEQNS{
   !  && \mbox{not sure what this is}
}
\begin{code}
n_bang = "!"
precBang = precNot -- for now

(bang,bangEntry) = prefixPT n_bang precBang Nothing
\end{code}


\RLEQNS{
   \assume~ a &=& a \sqcap (!a) \bot
}
\begin{code}
n_assume = mathSansBold "assume"
assume t = Comp n_assume [t]

precAssume = precNot -- for now
ppAssume sCP d p [t]
 = paren p precAssume
       $ pplist [ppa n_assume, ppa " ", sCP precPre 1 t]
ppAssume sCP d p _ = pps styleRed $ ppa ("invalid-"++n_assume)

assumeDefn d [a]
  = Just ( n_assume, meet [ a, mkSeq (bang a) bot ], True )

assumeEntry :: (Ord s, Show s) => Dict s
assumeEntry
 = entry n_assume $ PredEntry subAny ppAssume [] assumeDefn noDefn
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
\\ \tau(\emp) &=& \top
}
\begin{code}
rgReduce d _ (Atm (App anm [Var enm]))
 | enm == n_emp &&
   (anm == n_pi || anm == n_eps || anm == n_tau)
   = Just ( "Empty Rel is infeasible", top, True)
\end{code}

\RLEQNS{
   \tau(\Sigma) &=& \nil
}
\begin{code}
rgReduce d _ (Atm (App tnm [Var enm]))
 | tnm == n_tau && enm == n_Sigma
   = Just ( n_tau++" of "++n_Sigma, nil, True )
\end{code}
\RLEQNS{
   \tau(p_1) \sqcap \tau(p_2) &=& \tau(p_1 \cup p_2)
\\ \tau(p_1) \sqcup \tau(p_2) &=& \tau(p_1 \cap p_2)
\\                            &=& \tau(p_1)\tau(p_2)
\\                            &=& \tau(p_1)\parallel\tau(p_2)
}
\begin{code}
rgReduce d _ (Atm (App nop [ App tn1 [p1]      --  tau(p1)
                           , App tn2 [p2] ]))  --  tau(p2)
 | nop == n_meet && tn1 == n_tau && tn2 == n_tau
    = Just("meet of "++n_tau, Atm (tau (p1 `u` p2)), True )
 | nop == n_join && tn1 == n_tau && tn2 == n_tau
    = Just("join of "++n_tau, Atm (tau (p1 `i` p2)), True )
\end{code}

\RLEQNS{
   \lnot\tau(p) &=& \tau(\overline p)
}
\begin{code}
rgReduce d _ (Comp nn [Atm (App tnm [p])])
 | nn == nNot && tnm == n_tau
   = Just( nNot++"-"++n_tau, Atm (App tnm [complement p]), True )
\end{code}

\RLEQNS{
   \assume~\pi \sqcap \epsilon(r)
   &=&
   \pi \sqcap \epsilon(r) \sqcap \epsilon(\overline{r})\bot
}


The final catch-all pattern:
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
    , meetEntry
    , joinEntry
    , piEntry
    , epsEntry
    , iiEntry
    , piUEntry
    , epsUEntry
    , tauEntry
    , seqEntry
    , preEntry
    , bangEntry
    , assumeEntry
    , assertEntry
    , lawEntry
    , stdSetDict
    , stdPredDict
    ]
\end{code}



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
