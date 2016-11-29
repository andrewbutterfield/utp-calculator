\HDRa{Rely-Guarantee Algebra}\label{ha:RGAlg}
\begin{code}
module RGAlgebra where
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
import StdExpressions
import StdPredicates
\end{code}

\begin{code}
-- import Debug.Trace
-- dbg str x = trace (str++show x) x
\end{code}

We rapid prototype the emerging Rely-Guarantee Algebra work.
We organise this based on the FM2016 paper (citation needed).

\newpage
\HDRb{Concurrent Refinement Algebra}

Commands: $c,d \in \mathcal C$
\begin{code}
carrierC = [_mathcal 'C']
( c, cEntry )  = pvarEntry "c" [carrierC]
( d, dEntry )  = pvarEntry "d" [carrierC]
\end{code}
We use the alphabet parameter to define membership
of variables in various subsets of $\mathcal C$,
as they are defined below.

Concurrent Refinement Algebra (CRA):
\[
(\mathcal C,\sqcap,\sqcup,;,\parallel,\bot,\top,\nil,\Skip)
\]
\begin{code}
n_top  = _top    ; top  = PVar n_top
n_bot = _bot ; bot = PVar n_bot
n_nil = bold "nil" ; nil = PVar n_nil
n_skip = bold "skip"; skip = PVar n_skip
\end{code}

Complete, distributive lattice:
$
(\mathcal C,\sqcap,\sqcup,\bot,\top)
$.
We first setup meet and join as semi-lattice operators
with smart builders that flatten nested usage, remove identities
and collapse it all if any zeros occur.
\begin{code}
n_meet = _sqcap
(meet, meetEntry) = popSemiLattice n_meet bot top precOr

n_join = _sqcup
(join, joinEntry) = popSemiLattice n_join top bot precAnd
\end{code}
All that really remains now are the distributivity laws.
We defer those until we know which one we prefer
(I guess we want to work with meets of joins,
rather than the other way around).


\RLEQNS{
   c \sqsubseteq d &\defs& (c \sqcap d) = c
\\ \bot \quad \sqsubseteq &c& \sqsubseteq \quad \top
}
\begin{code}
n_rfdby = _sqsubseteq

rfdby s p = Comp n_rfdby [s,p]

rfdbyPP sCP d p [pr1,pr2] -- same precedence as implies
 = paren p (precImp-1) -- bracket self
     $ ppopen (pad n_rfdby) [ sCP precImp 1 pr1
                            , sCP precImp 2 pr2 ]
rfdbyPP sCP d p prs = pps styleRed $ ppa ("invalid-"++n_rfdby)

rfdbyDefn d prs@[pr1,pr2]
  = Just ( n_rfdby, mkEqv (meet prs) pr1, True )
rfdbyDefn _ _ = Nothing

rdfBySimp d [pr1,pr2]
 | pr1 == bot  = Just ( n_bot++" refined by all", T, True )
 | pr2 == top  = Just ( n_top++" refines all", T, True )
rdfBySimp _ _ = Nothing

rfdbyEntry
 = entry n_rfdby
   $ PredEntry subAny rfdbyPP [] rfdbyDefn rdfBySimp
\end{code}

Monoid:
$
  (\mathcal C, ;, \nil)
$.
\begin{code}
n_seq = ";"
(mkSeq, seqEntry) = popMonoid n_seq nil precAnd
\end{code}

\RLEQNS{
   (\bigsqcap C) ; d &=& \bigsqcap_{c \in C}(c;d)
}
\begin{code}
seqReduce d _ (Comp sn [Comp mn mprs, pr])
 | sn == n_seq && mn == n_meet
   = Just ( n_meet++" left-distr thru "++n_seq
          , meet (map distr mprs)
          , True )
 where distr mpr = mkSeq [mpr,pr]
\end{code}

\RLEQNS{
   \top ; c &=& \top
\\ \bot ; c &=& \bot
}
\begin{code}
seqReduce d _ (Comp sn prs)
 | sn == n_seq
   = appLeftZeros [] prs
 where
   appLeftZeros _ []  =  Nothing
   appLeftZeros srp (pr:prs)
    | pr == top  =  Just ( n_top++" is left-zero for "++n_seq
                         , mkSeq $ reverse (pr:srp)
                         , True )
    | pr == bot  =  Just ( n_bot++" is left-zero for "++n_seq
                         , mkSeq $ reverse (pr:srp)
                         , True )
    | otherwise  =  appLeftZeros (pr:srp) prs
\end{code}

Close off this reduction and create a dict entry.
\begin{code}
seqReduce _ _ _ = Nothing

seqRedEntry = entry laws $ LawEntry [seqReduce] [] []
\end{code}
\RLEQNS{
   c^0 &\defs& \nil
\\ c^{i+1} &\defs& c ; c^i
}
\begin{code}
n_repeat = "repeat"
rep c e = Comp n_repeat [c,Atm e]
repn c i = rep c $ Z i
repv c n = rep c $ Var n


precRep = precSub -- keep it tight
ppRep sCP d p [c,Atm ix]
 = paren p precRep
     $ pplist [ sCP precImp 1 c
              , ppa $ ppSuper d ix ]
ppRep sCP d p _ = pps styleRed $ ppa ("invalid-"++n_repeat)

repeatEntry
 = entry n_repeat $ PredEntry subAny ppRep [] noDefn noDefn
\end{code}
\RLEQNS{
   c^\star &\defs& \nu x . \nil \sqcap c ; x
\\ c^\omega &\defs& \mu x . \nil \sqcap c ;x
\\ c^\infty &\defs& c^\omega ; \top
\\ c^\omega &=& \nil \sqcap c ; c^\omega
\\ c^\star &=& \nil \sqcap c ; c^\star
\\ c^\infty &=& c ; c^\infty ~=~ c^i ; c^\infty ~=~ c^\infty ; d
}
We just define these passively for now
but don't implement any laws just yet.
\begin{code}
star c = repv c "*"
omega c = repv c _omega
nostop c = repv c _infty
\end{code}


True in their relational model, but not generally in CCS or CSP:
\RLEQNS{
   D \neq \setof{} &\implies& c;(\bigsqcap D) = \bigsqcap_{d \in D}(c;d)
}
It says that ; is \emph{conjunctive}.
We put this and consequent laws their own dictionary ``laws'' entry,
so it can used or ommitted as required.
\begin{code}
conjSeqReduce d _ (Comp sn [pr, Comp mn mprs])
 | sn == n_seq && mn == n_meet
   = Just ( n_meet++" right-distr thru "++n_seq
          , meet (map distr mprs)
          , True )
 where distr mpr = mkSeq [pr, mpr]
\end{code}
Needed for the following:
\RLEQNS{
   c^\omega &=& c^\star \sqcap c^\infty
\\ c^\star &=& \bigsqcap_{i \in \Nat} c^i
\\ c^\omega ; d &=& c^\star;d \sqcap c^\infty
\\ c;c^\omega;d &=& c;c^\star;d \sqcap c^\infty
}
For now we don't encode these laws as it is not clear
which direction is most useful.
\begin{code}
conjSeqReduce _ _ _ = Nothing

conjSeqRedEntry = entry laws $ LawEntry [conjSeqReduce] [] []
\end{code}

\HDRb{The Boolean Sub-algebra of Tests}

Test commands: $t \in \mathcal B \subseteq C$.
\begin{code}
carrierB = [_mathcal 'B']

isTest d (PVar t)
 = case plookup t d of
    Just (PredEntry _ _ [carrier] _ _) -> carrier == carrierB
    _                                  -> False
isTest _ _ = False

( t, tEntry )  = pvarEntry "t" [carrierB]
( t', t'Entry )  = pvarEntry "t'" [carrierB]
\end{code}
Extended algebra:
\[
(\mathcal C,\mathcal B,\sqcap,\sqcup,;,\parallel,\bot,\top,\nil,\Skip,\lnot)
\]
Test Boolean algebra --- sub-lattice of CRA:
$
(\mathcal B,\sqcap,\sqcup,\lnot,\top,\nil)
$

$\mathcal B$ closed under $\sqcap, \sqcup, ;, \parallel$.
\begin{code}
n_par = _parallel
( par, parEntry ) = popSemiG n_par precOr
\end{code}

Assume $t \in \mathcal B$, arbitrary test.
\RLEQNS{
   t;t' &=& t \sqcup t'
\\ t\parallel t' &=& t \sqcup t'
}
\begin{code}
testReduce d _ (Comp sn [t, t'])
 | (sn == n_seq || sn == n_par) && isTest d t && isTest d t'
   = Just ( "test-"++n_seq++" is "++n_join
          , join [t,t']
          , True )
\end{code}

\RLEQNS{
   (t;c) \parallel (t;d) &=& t;(c\parallel d)
\\ (t;c) \sqcup (t';d) &=& (t \sqcup t') ; (c \sqcup d)
}
\begin{code}
testReduce rgd _ (Comp pn [Comp sn1 [t,c], Comp sn2 [t',d]])
 | t == t' && pn == n_par && sn1 == n_seq && sn2 == n_seq
   && isTest rgd t
   = Just ( "test-"++n_par++"-distr"
          , mkSeq [t,par [c,d]]
          , True
          )
\end{code}
\RLEQNS{
   \Assert~t &\defs& t \sqcap \lnot t ; \bot
\\ \lnot \top &=& \nil
}
\begin{code}
-- to come
\end{code}

\begin{code}
testReduce _ _ _ = Nothing

testRedEntry = entry laws $ LawEntry [testReduce] [] []
\end{code}

\HDRb{Abstract Atomic Steps}

\HDRb{Relational Atomic Steps}

\HDRb{Relies and  Guarantees}

\HDRb{Abstract Communication in Process Algebras}



TO BE MOVED ELSEWHERE!!!
\begin{code}
n_alf = _alpha ; alf = PVar n_alf
n_chaos = bold "chaos" ; chaos = PVar n_chaos
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

tauEntry
 = entry n_tau
   $ ExprEntry
       subAny
       (defEPrint n_tau)
       noDefn
       (justMakes $ App n_tau)
       noEq
\end{code}


\RLEQNS{
   \pre~ t &=& t \sqcap \lnot t \bot
\\  &=& t \sqcap (\lnot t) \seq \bot
}
\begin{code}
n_pre = bold "pre"
precPre = precNot -- for now
expandPre d t = meet [ t, mkSeq [mkNot t, bot] ]

(pre, preEntry) = prefixPT n_pre precPre $ Just expandPre
\end{code}

\RLEQNS{
   \setof p &=& \pre~\tau(p)
\\ &=& \tau(p) \sqcap \tau(\overline{p})\bot
}
\begin{code}
n_assert = bold "{}"
assert t = Comp n_assert [t]

precAssert = precNot -- for now
ppAssert sCP d p [t]
 = paren p precAssert
       $ pplist [ ppa (bold "{")
                , sCP precPre 0 t
                , ppa (bold "}")
                ]
ppAssert sCP d p _ = pps styleRed $ ppa ("invalid-"++n_assert)

assertDefn d [t]
  = Just ( n_assert, pre $ Atm $ tau p, True )

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
n_assume = bold "assume"
assume t = Comp n_assume [t]

precAssume = precNot -- for now
ppAssume sCP d p [t]
 = paren p precAssume
       $ pplist [ppa n_assume, ppa " ", sCP precPre 1 t]
ppAssume sCP d p _ = pps styleRed $ ppa ("invalid-"++n_assume)

assumeDefn d [a]
  = Just ( n_assume, meet [ a, mkSeq [bang a, bot] ], True )

assumeEntry
 = entry n_assume $ PredEntry subAny ppAssume [] assumeDefn noDefn
\end{code}

\HDRb{Laws}

\HDRc{Reduction Steps}

\begin{code}
rgReduce :: RWFun
         -- Dict
         -- -> [Pred]  -- Invariants
         -- -> Pred    -- Target Predicate
         -- -> Maybe (String, Pred, Bool)
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
lawEntry :: Dict
lawEntry = entry laws $ LawEntry [rgReduce] [] []
\end{code}

\HDRb{RG Dictionary}
\begin{code}
rgDict :: Dict
rgDict
 = mergeDicts
    [ dictVersion "RGAlgebra 0.1"
    , cEntry, dEntry
    , meetEntry
    , joinEntry
    , rfdbyEntry
    , seqEntry
    , seqRedEntry
    , conjSeqRedEntry -- omit if doing CSP/CCS !!
    , repeatEntry
    , tEntry, t'Entry
    , parEntry
    , testRedEntry
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
    , stdExprDict
    , stdSetDict
    , stdPredDict
    ]
\end{code}



\HDRb{Top Level Support}

\begin{code}
rgshow :: Pred -> String
rgshow = pdshow 80 rgDict noStyles

rgput :: Pred -> IO ()
rgput = putStrLn . rgshow

rgeput :: Expr -> IO ()
rgeput = rgput . Atm

rgcalc pr = calcREPL rgDict [] pr
\end{code}
