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

{
\def\rgname#1{\textsf{#1}}
\def\rgcomm#1{\mathbf{#1}}

We rapid prototype the emerging Rely-Guarantee Algebra work.

\HDRb{Definitions}

\HDRc{Structure of concurrent program algebra}

\def\nil{\rgcomm{nil}}
\def\alf{\rgcomm{\alpha}}
\def\chaos{\rgcomm{chaos}}


We have:
\RLEQNS{
       & \top
\\ \nil &      & \alf
\\     & \chaos
\\ & \bot
}
\begin{code}
n_top  = _top    ; top  = Var n_top
n_nil = "nil" ; nil = Var n_nil
n_alf = _alpha ; alf = Var n_alf
n_chaos = "chaos" ; chaos = Var n_chaos
n_bot = _bot ; bot = Var n_bot
\end{code}

We have $\sqcap$ and $\sqcup$.
\begin{code}
n_meet = _sqcap ; meet t1 t2 = Comp n_meet [t1,t2]
ppMeet sCP d p ts
 = paren p precOr  -- we assume meet is like or
     $ ppopen (pad n_meet)
     $ ppwalk 1 (sCP precOr) ts

n_join = _sqcup ; join t1 t2 = Comp n_join [t1,t2]
ppJoin sCP d p ts
 = paren p precAnd  -- we assume join is like and
     $ ppopen (pad n_join)
     $ ppwalk 1 (sCP precAnd) ts

meetEntry, joinEntry :: (Ord s, Show s) => Dict s
meetEntry
 = entry n_meet $ PredEntry subAny ppMeet [] noDefn noDefn
joinEntry
 = entry n_join $ PredEntry subAny ppJoin [] noDefn noDefn
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

\def\id{\rgname{id}}
\def\univ{\rgname{univ}}
\def\emp{\rgname{$\setof{}$}}

Simple relations and predicates: \id, \univ, $\emp$
\begin{code}
n_id   = "id"   ; _id  = Var n_id
n_univ = "univ" ; univ = Var n_univ
n_emp  = "{}"   ; emp  = Var n_emp
\end{code}



\def\stutter{ii}

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

\def\pre{\textbf{\textsf{pre}}}
\RLEQNS{
   \pre~ t &=& t \sqcap \lnot t \bot
\\  &=& t \sqcap (\lnot t) \seq \bot
}
\begin{code}
n_pre = mathSansBold "pre"
pre t = Comp n_pre [t]

precPre = precNot -- for now
ppPre sCP d p [t] 
 = paren p precPre
       $ pplist [ppa n_pre, ppa " ", sCP precPre 1 t]
ppPre sCP d p _ = pps styleRed $ ppa ("invalid-"++n_pre)
       
preDefn d [t] 
  = Just ( n_pre, meet t (mkSeq (mkNot t) $ Atm bot), True )

preEntry :: (Ord s, Show s) => Dict s
preEntry
 = entry n_pre $ PredEntry subAny ppPre [] preDefn noDefn
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
n_bang = "!" ; isNot  = isComp nNot

mkBang a = Comp n_bang [a]

precBang = precNot -- for now
ppBang sCP d p [a] -- ignore marking for now
 = paren p precBang
       $ pplist [ppa n_bang, sCP precNot 1 a]
ppBang sCP d p _ = pps styleRed $ ppa ("invalid-"++n_bang)

bangEntry :: (Show s, Ord s) => Dict s
bangEntry
 = entry n_bang
   $ PredEntry anyVars ppBang [] noDefn noDefn
\end{code}


\def\assume{\textbf{\textsf{assume}}}
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
  = Just ( n_assume, meet a (mkSeq (mkBang a) $ Atm bot), True )

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
   = Just ( "Empty Rel is infeasible", Atm top, True)
\end{code}

\RLEQNS{
   \tau(\Sigma) &=& \nil
}
\begin{code}
rgReduce d _ (Atm (App tnm [Var enm]))
 | tnm == n_tau && enm == n_Sigma
   = Just ( n_tau++" of "++n_Sigma, Atm nil, True )
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
   =
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
