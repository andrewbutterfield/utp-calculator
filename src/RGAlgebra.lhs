\HDRa{Rely-Guarantee Algebra}\label{ha:RGAlg}
\begin{code}
module RGAlgebra where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import NiceSymbols
import CalcPPrint
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
We organise this based on the FM2016 paper and related material (citation needed).

\begin{code}
rgVersion = "0.4"
\end{code}
\newpage
\HDRb{Concurrent Refinement Algebra}

Commands: $c,d \in \mathcal C$
\begin{code}
carrierC = _mathcal "C"
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
n_meet = _sqcap ; precMeet = precOr + 1
(meet, meetEntry) = popSemiLatticeAI n_meet bot top precMeet

n_join = _sqcup; precJoin = precAnd + 1
(join, joinEntry) = popSemiLatticeAI n_join top bot precJoin
\end{code}
All that really remains now are the distributivity laws.
We defer those until we know which one we prefer
(I guess we want to work with meets of joins,
rather than the other way around).

\RLEQNS{
   c \sqsubseteq d &\defs& (c \sqcap d) = c
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
\end{code}
\RLEQNS{
   \bot \quad \sqsubseteq &c& \sqsubseteq \quad \top
}
\begin{code}
rdfBySimp d [pr1,pr2]
 | pr1 == bot  = Just ( n_bot++" refined by all", T, True )
 | pr2 == top  = Just ( n_top++" refines all", T, True )
rdfBySimp _ _ = Nothing

rfdbyEntry
 = entry n_rfdby
   $ PredEntry subAny rfdbyPP [] noDefn noDefn
    -- rfdbyDefn rdfBySimp  -- ommitted for now....
\end{code}
Monoid:
$
  (\mathcal C, ;, \nil)
$.
\begin{code}
n_seq = ";" ; precSeq = precJoin+1
(mkSeq, seqEntry) = popMonoid n_seq nil precSeq
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
   appLeftZeros _ []    =  Nothing
   appLeftZeros _ [pr]  =  Nothing
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
     $ pplist [ sCP precRep 1 c
              , ppa $ ppSuper d ix ]
ppRep sCP d p _ = pps styleRed $ ppa ("invalid-"++n_repeat)

repeatEntry
 = entry n_repeat $ PredEntry subAny ppRep [] noDefn noDefn
\end{code}
It can be useful to be able to assess if we have
a repeat, and to access its parts.
\begin{code}
isRep (Comp nr [_,_]) = nr == n_repeat
isRep _               = False

repFactor (Comp nr [a,Atm f])
 | nr == n_repeat  =  f
repFactor _        =  Z 1

repBody (Comp nr [a,_])
 | nr == n_repeat  =  a
repBody p          =  p
\end{code}

Given an repeat index,
is it finite (will terminate)
or fixed (always terminates after the same number of repeats)?
\begin{code}

isFiniteRep (Z i)    =  i >= 0
isFiniteRep (Var v)  =  not (v `elem` [_omega,_infty])
isFiniteRep _        =  False

isFixedRep (Z i)    =  i >= 0
isFixedRep (Var v)  =  not (v `elem` [_star,_omega,_infty])
isFixedRep _        =  False
\end{code}
The ability to terminate immediately is also useful:
\begin{code}
canDoZero (Comp nr [a,Atm (Var v)])
 | nr == n_repeat && v `elem` [_star,_omega]  =  True
canDoZero _                                   = False
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
star c = repv c _star
omega c = repv c _omega
nostop c = repv c _infty
infty = nostop
\end{code}

\newpage
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

\newpage
\HDRb{The Boolean Sub-algebra of Tests}

Test commands: $t \in \mathcal B \subseteq C$.
$\mathcal B$ closed under $\sqcap, \sqcup, ;, \parallel$.
\begin{code}
carrierB = _mathcal "B"

isTest d (PVar t)
 = case plookup t d of
    Just (PredEntry _ _ [carrier] _ _) -> carrier == carrierB
    _                                  -> False
isTest d (Comp n prs)
 | n `elem` [n_meet,n_join,n_seq,n_par] = all (isTest d) prs
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

\begin{code}
n_par = _parallel ; precPar = precOr
( par, parEntry ) = popSemiG n_par precPar
\end{code}


\RLEQNS{
   \Assert~t &\defs& t \sqcap \lnot t ; \bot
}
\begin{code}
n_assert = bold "assert" ; precAssert = precNot

defnAssert d t = join [ t,  mkSeq [ mkNot t, bot ] ]
-- !!!! might only be valid if isTest t

( assert, assertEntry ) = prefixPT n_assert precAssert $ Just defnAssert
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
}
\begin{code}
testReduce rgd _ (Comp pn [Comp sn1 [t,c], Comp sn2 [t',d]])
 | t == t' && pn == n_par && sn1 == n_seq && sn2 == n_seq
   && isTest rgd t
   = Just ( "test-"++n_par++"-distr"
          , mkSeq [ t, par [c,d] ]
          , True
          )
\end{code}

\newpage
\RLEQNS{
   (t;c) \sqcup (t';d) &=& (t \sqcup t') ; (c \sqcup d)
}
\begin{code}
testReduce rgd _ (Comp jn [Comp sn1 [t,c], Comp sn2 [t',d]])
 | jn == n_join && sn1 == n_seq && sn2 == n_seq
   && isTest rgd t && isTest rgd t'
   = Just ( "test-"++n_join++"-distr"
          , mkSeq [ join [t,t'], join [c,d] ]
          , True
          )
\end{code}

\RLEQNS{
   \lnot \top &=& \nil
}
\begin{code}
testReduce d _ (Comp nn [tp])
 | nn == nNot && tp == top
   = Just ( nNot++" "++n_top++" is "++n_nil
          , nil
          , True )
\end{code}

\begin{code}
testReduce _ _ _ = Nothing

testRedEntry = entry laws $ LawEntry [testReduce] [] []
\end{code}

\newpage
\HDRb{Abstract Atomic Steps}

Atomic Step commands: $a,b \in \mathcal A \subseteq C$.

$\mathcal A$ closed under $\sqcap, \sqcup, \parallel$, but not $;$.
\begin{code}
carrierA = _mathcal "A"

isAtmStep d (PVar a)
 = case plookup a d of
    Just (PredEntry _ _ [carrier] _ _) -> carrier == carrierA
    _                                  -> False
isAtmStep d (Comp n [Atm _]) -- n_pi/eps_fun defined later on
 | n  `elem` [n_pi_fun,n_eps_fun]  =  True
isAtmStep d (Comp n prs)
 | n `elem` [n_meet,n_join,n_par] = all (isAtmStep d) prs
isAtmStep _ _ = False

isAtmRep d (Comp nr [a,i])
 | nr == n_repeat && isAtmStep d a  =  True
isAtmRep _ _                        =  False

( a, aEntry ) = pvarEntry "a" [carrierA]
( b, bEntry ) = pvarEntry "b" [carrierA]
\end{code}

We want special handling for sequential compostions
that start with an atomic action, followed by at least one command
\begin{code}
isAtomStartSeq d (Comp ns (a:_:_)) = ns == n_seq && isAtmStep d a
isAtomStartSeq _ _ = False

-- we assume the above is true
splitAtomicStartSeq (Comp ns [a,c]) = (a,c)
splitAtomicStartSeq (Comp ns (a:cs)) = (a,mkSeq cs)
\end{code}
Atomic Action Boolean algebra --- sub-lattice of CRA:
$
(\mathcal A,\sqcap,\sqcup,!,\top,\alf)
$
\begin{code}
n_bang = "!"
precBang = precNot -- for now

(bang,bangEntry0) = prefixPT n_bang precBang Nothing

bangbangGone :: Rewrite
bangbangGone _ [Comp nb [pr]]
 | nb == n_bang
   = Just ( n_bang++"-involution"
          , pr
          , True )
bangbangGone _ _ = Nothing

bangEntry = updateDict n_bang (prsimpUpdate bangbangGone) bangEntry0

n_alf = bold _alpha
( alf, alfEntry ) = pvarEntry n_alf [carrierA]
\end{code}

\RLEQNS{
  \wait &\defs& \mbox{atomic parallel identity}
}
\begin{code}
n_atmParId = _mathcal "E"
( atmParId, atmParIdEntry ) = pvarEntry n_atmParId [carrierA]
\end{code}

We don't implement this now---not sure this is always useful
\RLEQNS{
   \Skip &=& \wait^\omega
}
\begin{code}
skipDef = rep atmParId (Var _omega)
\end{code}

\newpage

\RLEQNS{
   \assume~ a &=& a \sqcap (!a) \bot
}
\begin{code}
n_assume = bold "assume"
assume t = Comp n_assume [t]

precAssume = precNot -- for now
ppAssume sCP d p [t]
 = paren p precAssume
       $ pplist [ppa n_assume, ppa " ", sCP precAssume 1 t]
ppAssume sCP d p _ = pps styleRed $ ppa ("invalid-"++n_assume)

assumeDefn d [a]
  = Just ( n_assume, meet [ a, mkSeq [bang a, bot] ], True )

assumeEntry
 = entry n_assume $ PredEntry subAny ppAssume [] assumeDefn noDefn
\end{code}



\HDRc{Atomic Step Reductions}

\begin{code}
atmReduce :: RWFun
\end{code}

\RLEQNS{
   \alf \sqcup \nil &=& \top
}
\begin{code}
atmReduce d _ (Comp nj [a1,a2])
 | nj == n_join
   && (a1 == alf && a2 == nil || a1 == nil && a2 == alf)
   = Just ( "joining "++n_alf++","++n_nil++" yields "++n_top
          , top
          , True )
\end{code}

\RLEQNS{
   a \parallel \wait &=& a
\\ \wait \parallel \wait &=& \wait \qquad \mbox{--- we assume !!!}
}
\begin{code}
atmReduce d _ (Comp np as)
 | np == n_par && all (someOf [(== atmParId), isAtmStep d]) as
   && as' /= as
   = Just ( "atomic-step "++n_par++"-unit"
          , apar as'
          , True )
 where
   as' = filter (/= atmParId) as
   apar [] = atmParId
   apar as = par as
\end{code}

\newpage
\RLEQNS{
   a;c \parallel b;d &=& (a \parallel b);(c\parallel d)
\\ a;c \sqcup b;d &=& (a \sqcup b);(c \sqcup d)
}
\begin{code}
atmReduce d _ (Comp np acs)
 | np == n_par && all (isAtomStartSeq d) acs
  = Just( "atomic-"++n_seq++"-"++n_par++"-distr"
        , mkSeq [par as,par css]
        , True )
 where
   (as,css) = unzip $ map splitAtomicStartSeq acs
atmReduce d _ (Comp nj acs)
 | nj == n_join && all (isAtomStartSeq d) acs
  = Just( "atomic-"++n_seq++"-"++n_join++"-distr"
        , mkSeq [join as,join css]
        , True )
 where
   (as,css) = unzip $ map splitAtomicStartSeq acs
\end{code}

\RLEQNS{
   a;c \parallel \nil &=& \top
\\ a;c \sqcup \nil &=& \top
}
\begin{code}
atmReduce d _ (Comp nm [c1,c2])
 | nm == n_par
   &&
   ( isAtomStartSeq d c1 && c2 == nil
     ||
     isAtomStartSeq d c2 && c1 == nil )
   = Just ( "atom-seq-"++n_par++"-zero"
          , top
          , True )
 | nm == n_meet
   &&
   ( isAtomStartSeq d c1 && c2 == nil
     ||
     isAtomStartSeq d c2 && c1 == nil )
   = Just ( "atom-seq-"++n_meet++"-zero"
          , top
          , True )
\end{code}

what
\RLEQNS{
   a \sqcup !a &=& \top
\\ a \sqcap !a &=& \alf
}
\begin{code}
atmReduce d _ (Comp nm [a, Comp nb [b]])
 | nm == n_join && nb == n_bang && isAtmStep d a && a == b
   = Just ( "atomic-"++n_join++"-!-inv"
          , top
          , True )
 | nm == n_meet && nb == n_bang && isAtmStep d a && a == b
   = Just ( "atomic-"++n_meet++"-!-inv"
          , alf
          , True )
atmReduce d _ (Comp nm [Comp nb [b], a])
 | nm == n_join && nb == n_bang && isAtmStep d a && a == b
   = Just ( "atomic-"++n_join++"-!-inv"
          , top
          , True )
 | nm == n_meet && nb == n_bang && isAtmStep d a && a == b
   = Just ( "atomic-"++n_meet++"-!-inv"
          , alf
          , True )
\end{code}

\RLEQNS{
  !\top &=& \alf
}
\begin{code}
atmReduce d _ (Comp nb [t])
 | nb == n_bang && t == top
   = Just ( "!"++n_top++" is "++n_alf
          , alf
          , True )
\end{code}


\RLEQNS{
   \Skip \parallel c &=& c
\\ \wait^\omega \parallel c &=& c
   & \mbox{atomic identity iteration}
}
\begin{code}
atmReduce d _ (Comp np [c1,c2])
 | np == n_par && c1 == skip
   = Just ( n_par++"-unit", c2, True )
 | np == n_par && c2 == skip
   = Just ( n_par++"-unit", c1, True )
 | np == n_par && c1 == skipDef
   = Just ( "atomic-identity-iteration", c2, True )
 | np == n_par && c2 == skipDef
   = Just ( "atomic-identity-iteration", c1, True )
\end{code}

\RLEQNS{
\\ a^* \parallel \nil &=& \nil
   & \mbox{atomic iteration nil}
\\ a^\omega \parallel \nil &=& \nil
   & \mbox{atomic iteration nil}
}
\begin{code}
atmReduce d _ (Comp np [a1,a2])
 | np == n_par && isAtmRep d a1 && canDoZero a1
   && a2 == nil
     = Just ( "atomic-iteration-nil", nil, True )
 | np == n_par && isAtmRep d a2 && canDoZero a2
   && a1 == nil
     = Just ( "atomic-iteration-nil", nil, True )
\end{code}

\RLEQNS{
   a^\infty \parallel \nil &=& \top
   & \mbox{atomic iteration nil}
}
\begin{code}
atmReduce d _ (Comp np [a1,a2])
 | np == n_par && isAtmRep d a1 && repFactor a1 == (Var _infty)
   && a2 == nil
     = Just ( "atomic-iteration-nil", top, True )
 | np == n_par && isAtmRep d a2 && repFactor a2 == (Var _infty)
   && a1 == nil
     = Just ( "atomic-iteration-nil", top, True )
\end{code}
An open question: is  $a^i \parallel \nil = \top$ for all $i \neq 0$?

\RLEQNS{
a^i ; c \parallel b^i ; d
   &=&
   (a \parallel b)^i ; (c \parallel d)
}
\begin{code}
atmReduce d _ (Comp np [ (Comp ns1 (ai:cs))
                       , (Comp ns2 (bi:ds))])
 | np == n_par
   && ns1 == n_seq && ns2 == n_seq
   && isAtmRep d ai && isAtmRep d bi
   && isFixedRep i && i == repFactor bi
   = Just ( "atomic-sync"
          , mkSeq [ rep (par [a,b]) i
                  , par [ mkSeq cs, mkSeq ds] ]
          , True )
 where i = repFactor ai
\end{code}


Now we wrap up atomic action reduction.
\begin{code}
atmReduce _ _ _ = Nothing

atmRedEntry = entry laws $ LawEntry [atmReduce] [] []
\end{code}

We need to define the notion of an \emph{action}:
\RLEQNS{
   \action a &=& \wait^\omega ; a ; \wait^\omega
}
\begin{code}
n_action = _langle++_rangle ; precAction = precNot
action a = Comp n_action [a]

ppAction sCP d p [a]
 = pplist [ppa _langle, sCP 0 1 a, ppa _rangle ]

defnAction d [a]
 = Just ( n_action
        , mkSeq [ omega atmParId, a, omega atmParId ]
        , True )

actionEntry = entry n_action
              $ PredEntry subAny ppAction [] defnAction noDefn
\end{code}


\newpage
Assuming $;$ is conjunctive (use a seperate reduction function).
\begin{code}
conjAtmReduce :: RWFun
\end{code}

\RLEQNS{
   a^* \parallel b^* &=& (a \parallel b)^*
\\ a^\infty \parallel b^\infty &=& (a \parallel b)^\infty
}
\begin{code}
conjAtmReduce d _ (Comp np [ai, bi])
 | np == n_par
   && isAtmRep d ai && isAtmRep d bi
   && (s == Var _star || s == Var _infty)
   && s == repFactor bi
   = Just ( "parallel-"++sym, rep (par [a,b]) s, True )
 where
   s = repFactor ai
   (Var sym) = s
\end{code}

\RLEQNS{
   a^* ; c \parallel b^* ; d
   &=&
   (a \parallel b)^*
   ;
   ( (c \parallel d)
     \sqcap
     (c \parallel b;b^*;d)
     \sqcap
     (a;a^*;c \parallel d)
   )
   & \mbox{atomic iteration finite}
\\ a^\omega ; c \parallel b^\omega ; d
   &=&
   (a \parallel b)^\omega
   ;
   ( (c \parallel d)
     \sqcap
     (c \parallel b;b^\omega;d)
     \sqcap
     (a;a^\omega;c \parallel d)
   )
   & \mbox{atomic iteration either}
}
\begin{code}
conjAtmReduce d _ (Comp np [ Comp ns1 (ai:cs)
                           , Comp ns2 (bi:ds) ])
 | np==n_par && ns1==n_seq && ns2==n_seq
   && isAtmRep d ai && isAtmRep d bi
   && (s == Var _star || s == Var _omega)
   && s == repFactor bi
   = Just ( "atomic-iteration-"++sym
          , mkSeq
             [ rep (par [a,b]) s
             , meet
                [ par [cs',ds']
                , par [cs', mkSeq (b:bi:ds)]
                , par [mkSeq (a:ai:cs), ds']
                ]
             ]
          , True )
 where
   s = repFactor ai
   (Var sym) = s
   cs' = mkSeq cs
   ds' = mkSeq ds
   a = repBody ai
   b = repBody bi
\end{code}

\newpage
\RLEQNS{
   a^* ; c \parallel b^\infty
   &=& (a \parallel b)^* ; (c \parallel b^\infty)
\\ && \mbox{atomic iteration finite infinite}
}
\begin{code}
conjAtmReduce d _ (Comp np [Comp ns (ai:cs), bi])
 | np == n_par
   && isAtmRep d ai && isAtmRep d bi
   && repFactor ai == Var _star
   && repFactor bi == Var _infty
   = Just ( "atomic-iteration-finite-infinite"
          , mkSeq [ star (par [a,b])
                  , par [mkSeq cs, infty b]
                  ]
          , True )
 where
   s = repFactor ai
   a = repBody ai
   b = repBody bi
\end{code}

\RLEQNS{
   \action a \parallel \action b
   &=&
   \action{a \parallel b}
   \sqcap
   \action a ; \action b
   \sqcap
   \action b ; \action a
   & \mbox{atomic interleaving}
}
\begin{code}
conjAtmReduce d _ (Comp np [ acta@(Comp na1 [a])
                           , actb@(Comp na2 [b]) ])
 | np==n_par && na1==n_action && na2==n_action
   =  Just ( "atomic-interleaving"
           , meet [ action $ par [a,b]
                  , mkSeq [ acta, actb ]
                  , mkSeq [ actb, acta ] ]
           , True )
\end{code}

\RLEQNS{
   a \ileave b &=& a;b \sqcap b;a
}
We leave this for now

Now we wrap up conjunctive atomic action reduction.
\begin{code}
conjAtmReduce _ _ _ = Nothing

conjAtmRedEntry = entry laws $ LawEntry [conjAtmReduce] [] []
\end{code}

\newpage
\HDRb{Relational Atomic Steps}

\RLEQNS{
   r &\subseteq& \Sigma \times \Sigma
\\ \varnothing &\in& \Sigma \times \Sigma
\\ \varnothing &\subseteq& r
}
\begin{code}
n_Sigma = _Sigma ; sigma = Var n_Sigma
r = Var "r"
n_emptyrel = _varnothing ; emptyrel = Var _varnothing
\end{code}
We can also get the negation of a relation: $\overline r$:
\begin{code}
n_negrel = _overline " " ; negrel r = App n_negrel [r]
\end{code}

\RLEQNS{
   \boldpi, \boldsymbol\epsilon
   &:& \power(\Sigma\times\Sigma) \fun \mathcal A
}
These are defined as atomic steps in \texttt{isAtmStep} above.
\begin{code}
n_pi_fun = bold _pi ; pi_fun r = Atm $ App n_pi_fun [r]
n_eps_fun = bold _epsilon ; eps_fun r = Atm $ App n_eps_fun [r]
\end{code}

\begin{code}
relAtmReduce :: RWFun
\end{code}

\RLEQNS{
   \boldpi(\varnothing)
   & = ~~ \top ~~ = &
   \boldsymbol\epsilon(\varnothing)
}
\begin{code}
relAtmReduce d _ (Atm (App nm [r]))
 | (nm==n_pi_fun || nm==n_eps_fun) && r == emptyrel
   = Just ( "infeasible-empty-rel", top, True )
\end{code}

\RLEQNS{
   \boldpi(r_1) \sqcup \boldsymbol\epsilon(r_2) &=& \top
}
\begin{code}
relAtmReduce d _ (Comp nj [Atm (App n1 [_]), Atm (App n2 [_])])
 | nj==n_join &&
   ( n1==n_pi_fun && n2==n_eps_fun
    ||
     n2==n_pi_fun && n1==n_eps_fun
   )
   = Just ( "disjoint-"++n_pi_fun++"-"++n_eps_fun++"-images"
          , top, True )
\end{code}

\RLEQNS{
   r_1 = r_2 &\Leftrightarrow& \boldpi(r_1) = \boldpi(r_2)
\\ \boldpi(r_1 \cup r_2) &=& \boldpi(r_1) \sqcap \boldpi(r_2)
\\ \boldpi(r_1 \cap r_2) &=& \boldpi(r_1) \sqcup \boldpi(r_2)
\\ r_1 \subseteq r_2 &\implies& \boldpi(r_2) \sqsubseteq \boldpi(r_1)
}
and similarly for $\boldsymbol\epsilon$.
We don't implement these right now, until we get a better feel for which way
round works best, in what scenarios.

\begin{code}
relAtmReduce _ _ _ = Nothing

relAtmRedEntry = entry laws $ LawEntry [relAtmReduce] [] []
\end{code}

\HDRb{Relies and  Guarantees}


\HDRc{The guarantee command}

\begin{code}
g = Var "g"
\end{code}

\RLEQNS{
   (\piRestrict~g) &\defs& \boldpi(g) \sqcap \wait
}
\begin{code}
n_pirestrict = _pi++'-':bold "restrict"
pirestrict g = Comp n_pirestrict [Atm g]

ppPiR sCP d _ [gpr]
 = ppclosed "(" ")" " " [ppa n_pirestrict, sCP 0 1 gpr]

piRDefn d [Atm g]
 = Just ( n_pirestrict, meet [pi_fun g, atmParId], True )
piRDefn _ _ = Nothing

piResEntry
 = entry n_pirestrict $ PredEntry subAny ppPiR [] piRDefn noDefn
\end{code}


\RLEQNS{
   \guar~g &\defs& (\piRestrict~g)^\omega
}
\begin{code}
n_guar = bold "guar"
guar g = Comp n_guar [Atm g]

precGuar = precSub -- keep it tight
ppGuar sCP d p [gpr]
 = paren p precGuar
    $ ppopen " " [ppa n_guar, sCP precGuar 1 gpr]

guarDefn d [Atm g]
 = Just ( n_guar, omega $ pirestrict g, True )
guarDefn _ _ = Nothing

guarEntry
 = entry n_guar $ PredEntry subAny ppGuar [] guarDefn noDefn
\end{code}

First, we define $\chaos$:
\RLEQNS{
  \chaos &\defs& \alf^\omega
}
We won't support expanding its definition right now.
\begin{code}
n_chaos = bold "chaos" ; chaos = PVar n_chaos
\end{code}

Weak conjunction on commands $\Cap$:
\RLEQNS{
   c_1 \Cap (c_2 \Cap c_3) &=& (c_1 \Cap c_2) \Cap c_3
\\ c \Cap d &=& d \Cap c
\\ c \Cap c &=& c
\\ c \Cap \bot &=& \bot
\\ c \Cap \chaos &=& c
}

\begin{code}
n_wkconj = _Cap ; precWkConj = precJoin - 1
(wkconj, wkconjEntry)
          = popSemiLatticeAI n_wkconj bot chaos precWkConj
\end{code}

We now define some weak-conjunction laws:
\begin{code}
wkconjRed :: RWFun
\end{code}

For non-empty $D$:
\RLEQNS{
   c \Cap (\bigsqcap D) &=& (\bigsqcap_{d \in D} c \Cap d)
}
\begin{code}
wkconjRed d _ (Comp nwc [ c
                        , Comp nm ds@(_:_) ])
 | nwc==n_wkconj && nm==n_meet
   = Just ( n_wkconj++"-"++n_meet++"-distr"
          , meet $ map (conj c) ds
          , True )
 where conj c d = wkconj [c,d]
\end{code}

\RLEQNS{
   a \Cap \alf &=& a
}
\begin{code}
wkconjRed d _ (Comp nwc [a1, a2])
 | nwc==n_wkconj
   && ( isAtmStep d a1 && a2==alf)
      =  Just ( n_wkconj++"-step-unit", a1, True )
 | nwc==n_wkconj
   && ( isAtmStep d a2 && a1==alf)
      =  Just ( n_wkconj++"-step-unit", a2, True )
\end{code}

\RLEQNS{
   (a;c) \Cap \nil &=& \top
}
\begin{code}
wkconjRed d _ (Comp nwc [Comp ns (a:c), nl])
 | nwc==n_wkconj && ns==n_seq && isAtmStep d a && nl==nil
     = Just ( "step-"++n_wkconj++"-"++n_nil++"-infeasible"
            , top, True )
wkconjRed d _ (Comp nwc [nl, Comp ns (a:c)])
 | nwc==n_wkconj && ns==n_seq && isAtmStep d a && nl==nil
     = Just ( "step-"++n_wkconj++"-"++n_nil++"-infeasible"
            , top, True )
\end{code}

\RLEQNS{
   (\guar~g) \Cap (c;d) &=& ((\guar~g)\Cap c);((\guar~g)\Cap d)
}
\begin{code}
wkconjRed d _ (Comp nwc [gg@(Comp ng [Atm _]), Comp ns (c:ds)])
 | nwc==n_wkconj && ng==n_guar && ns==n_seq
   = Just ( "weak-"++n_guar++"-;-distr"
          , Comp ns [ wkconj [gg,c]
                    , wkconj [gg,mkSeq ds] ]
          , True )
wkconjRed d _ (Comp nwc [Comp ns (c:ds), gg@(Comp ng [Atm _])])
 | nwc==n_wkconj && ng==n_guar && ns==n_seq
   = Just ( "weak-"++n_guar++"-;-distr"
          , Comp ns [ wkconj [gg,c]
                    , wkconj [gg,mkSeq ds] ]
          , True )
\end{code}



Laws yet to be implemented:
\RLEQNS{
   a \Cap b &=& a \sqcup b
\\ t \Cap t' &=& t \sqcup t'
\\ (a;c) \Cap (b;d) &=& (a \Cap b) ; (c \Cap d)
\\ a^\infty \Cap b^\infty &=& (a \Cap b)^\infty
\\ a^\omega \Cap b^\omega &=& (a \Cap b)^\omega
   & \mbox{atomic-iteration-conjunction}
\\ a^\omega \Cap (c;d) &=& (a^\omega \Cap c);(a^\omega \Cap d)
   & \mbox{atomic-infinite-distribution}
}

\begin{code}
wkconjRed _ _ _ = Nothing

wkconjRedEntry = entry laws $ LawEntry [wkconjRed] [] []
\end{code}

\newpage
\HDRc{The rely command}

\RLEQNS{
   (\epsAssm~r) &\defs& \assume(!\boldeps(\overline r))
\\ &=& !\boldeps(\overline r) \sqcap \boldeps(\overline r);\bot
}

\begin{code}
n_epsassume = _epsilon++'-':bold "assm"
epsassume r = Comp n_epsassume [Atm r]

ppEpsA sCP d _ [rpr]
 = ppclosed "(" ")" " " [ppa n_epsassume, sCP 0 1 rpr]

epsADefn d [Atm r]
 = Just ( n_epsassume, assume $ bang $ eps_fun $ negrel r, True )
epsADefn _ _ = Nothing

epsAsmEntry
 = entry n_epsassume $ PredEntry subAny ppEpsA [] epsADefn noDefn
\end{code}

\RLEQNS{
   \rely~r &\defs& (\epsAssm~r)^\omega
}
\begin{code}
n_rely = bold "rely"
rely r = Comp n_rely [Atm r]

precRely = precSub -- keep it tight
ppRely sCP d p [rpr]
 = paren p precRely
    $ ppopen " " [ppa n_rely, sCP precRely 1 rpr]

relyDefn d [Atm r]
 = Just ( n_rely, omega $ epsassume r, True )
relyDefn _ _ = Nothing

relyEntry
 = entry n_rely $ PredEntry subAny ppRely [] relyDefn noDefn
\end{code}

Now some laws/calcs:
\RLEQNS{
   (\epsAssm~r_1) \Cap (\epsAssm~r_2)
   &=& \assume(!\boldeps(\overline{r_1}) \sqcup !\boldeps(\overline{r_2}))
\\ &=& \assume(!\boldeps(\overline{r_1 \cap r_2}))
\\ &=& (\epsAssm(r_1 \cap r_2))
\\ (\rely~r) \Cap (c;d)
   &=&
   (\rely~r \Cap c) ; (\rely~r \Cap d)
}

\newpage
\HDRc{Rely/Guarantee Logic}

\RLEQNS{
   \setof{p,r}c\setof{g,q}
   &=&
   (\Assert~ p)((\rely~ r)\Cap(\guar~g)\Cap[q]) \sqsubseteq c
}
\begin{code}
n_5 = "5"
quintuple p r c g q = Comp n_5 [p,Atm r,c,Atm g,q]

pp5 sCP d _ [p,r,c,g,q]
 = pplist [ ppAssertions [sCP 0 1 p, sCP 0 2 r ]
          , sCP 0 3 c
          , ppAssertions [sCP 0 4 g, sCP 0 5 q ]
          ]
 where ppAssertions = ppclosed "{" "}" ","

defn5 d  [p, Atm r, c, Atm g, q]
 = Just ( "quintuple"
        , mkSeq [ assert  p
                ,  wkconj [rely r, guar g, sat q]
                ]
          `rfdby`
          c
        , True )

quinEntry = entry n_5 $ PredEntry subAny pp5 [] defn5 noDefn
\end{code}
We note that the notation $[q]$ is not used or defined elsewhere!
\begin{code}
n_sat = "[]" ;  sat q = Comp n_sat [q]

ppSat sCP d p [q]
 = ppclosed "[" "]" "" [sCP 0 1 q]

satEntry = entry n_sat $ PredEntry subAny ppSat [] noDefn noDefn
\end{code}

\newpage

\HDRb{Abstract Communication in Process Algebras}

\HDRc{Communication in CCS}

\HDRc{Communication in CSP}

\HDRc{Communication in SCCS}

\newpage
\HDRb{Material from FM2016 Tutorial}

T o be reconciled with the above.

\RLEQNS{
     π(r) &=& \Pi(\sigma,\sigma'), (\sigma,\sigma') \in r
}
%\begin{code}
%n_pi = _pi  -- pi
%mkpi r = App n_pi [r]
%
%piEntry
% = entry n_pi
%   $ ExprEntry
%       subAny
%       (defEPrint n_pi)
%       noDefn
%       (justMakes $ App n_pi)
%       noEq
%\end{code}
%
%
%
\RLEQNS{
   ϵ(r) &=& \mathcal{E}(\sigma,\sigma'), (\sigma,\sigma') \in r
}
%\begin{code}
%n_eps = _epsilon -- lunate epsilon
%eps r = App n_eps [r]
%
%epsEntry
% = entry n_eps
%   $ ExprEntry
%       subAny
%       (defEPrint n_eps)
%       noDefn
%       (justMakes $ App n_eps)
%       noEq
%\end{code}

Simple relations and predicates: \id, \univ, $\emp$
%\begin{code}
%n_id   = "id"   ; _id  = Var n_id
%n_univ = "univ" ; univ = Var n_univ
%n_emp  = "{}"   ; emp  = Var n_emp
%\end{code}
%
%
\RLEQNS{
   \stutter &=& \pi(\id)
}
%\begin{code}
%n_ii = "ii"
%ii = App n_ii [] -- we want to define this
%iiPrint _ _ = n_ii
%iiDefn _ _  =  edefn n_ii $ mkpi _id
%
%iiEntry
% = entry n_ii
%   $ ExprEntry
%       subAny
%       iiPrint
%       iiDefn
%       (justMakes $ App n_ii)
%       noEq
%\end{code}
%
%
\RLEQNS{
   \pi &=& \pi(\univ)
}
%\begin{code}
%n_piU = _pi++"U"
%piU = App n_piU []
%piUPrint _ _ = n_pi
%piUDefn _ _ = edefn _pi $ mkpi univ
%
%piUEntry
% = entry n_piU
%   $ ExprEntry
%       subAny
%       piUPrint
%       piUDefn
%       (justMakes $ App n_piU)
%       noEq
%\end{code}
%
\RLEQNS{
   \epsilon &=& \epsilon(\univ)
}
%\begin{code}
%n_epsU = _epsilon++"U"
%epsU = App n_epsU []
%epsUPrint _ _ = n_eps
%epsUDefn _ _ = edefn _epsilon $ eps univ
%
%epsUEntry
% = entry n_epsU
%   $ ExprEntry
%       subAny
%       epsUPrint
%       epsUDefn
%       (justMakes $ App n_epsU)
%       noEq
%\end{code}
%
%\HDRc{Tests as a Boolean Algebra}
%
\RLEQNS{
   p &\subseteq& \Sigma
}
%\begin{code}
%p = Var "p"
%\end{code}
%
\RLEQNS{
     τ(p) &=& \mbox{if $p$ then terminate else $\top$}
}
%\begin{code}
%n_tau = _tau  -- tau
%tau p = App n_tau [p]
%
%tauEntry
% = entry n_tau
%   $ ExprEntry
%       subAny
%       (defEPrint n_tau)
%       noDefn
%       (justMakes $ App n_tau)
%       noEq
%\end{code}
%
%
\RLEQNS{
   \pre~ t &=& t \sqcap \lnot t \bot
\\  &=& t \sqcap (\lnot t) \seq \bot
}
%\begin{code}
%n_pre = bold "pre"
%precPre = precNot -- for now
%expandPre d t = meet [ t, mkSeq [mkNot t, bot] ]
%
%(pre, preEntry) = prefixPT n_pre precPre $ Just expandPre
%\end{code}
%
\RLEQNS{
   \setof p &=& \pre~\tau(p)
\\ &=& \tau(p) \sqcap \tau(\overline{p})\bot
}
%\begin{code}
%xxn_assert = bold "{}"
%xxassert t = Comp n_assert [t]
%
%xxprecAssert = precNot -- for now
%ppAssert sCP d p [t]
% = paren p xxprecAssert
%       $ pplist [ ppa (bold "{")
%                , sCP precPre 0 t
%                , ppa (bold "}")
%                ]
%ppAssert sCP d p _ = pps styleRed $ ppa ("invalid-"++n_assert)
%
%assertDefn d [t]
%  = Just ( xxn_assert, pre $ Atm $ tau p, True )
%
%xxassertEntry
% = entry xxn_assert $ PredEntry subAny ppAssert [] assertDefn noDefn
%\end{code}
%
%



%\HDRb{Laws}
%
%\HDRc{Reduction Steps}
%
%\begin{code}
%rgReduce :: RWFun
%         -- Dict
%         -- -> [Pred]  -- Invariants
%         -- -> Pred    -- Target Predicate
%         -- -> Maybe (String, Pred, Bool)
%\end{code}
%
\RLEQNS{
   \pi(\emp) &=& \top
\\ \epsilon(\emp) &=& \top
\\ \tau(\emp) &=& \top
}
%\begin{code}
%rgReduce d _ (Atm (App anm [Var enm]))
% | enm == n_emp &&
%   (anm == n_pi || anm == n_eps || anm == n_tau)
%   = Just ( "Empty Rel is infeasible", top, True)
%\end{code}
%
\RLEQNS{
   \tau(\Sigma) &=& \nil
}
%\begin{code}
%rgReduce d _ (Atm (App tnm [Var enm]))
% | tnm == n_tau && enm == n_Sigma
%   = Just ( n_tau++" of "++n_Sigma, nil, True )
%\end{code}
\RLEQNS{
   \tau(p_1) \sqcap \tau(p_2) &=& \tau(p_1 \cup p_2)
\\ \tau(p_1) \sqcup \tau(p_2) &=& \tau(p_1 \cap p_2)
\\                            &=& \tau(p_1)\tau(p_2)
\\                            &=& \tau(p_1)\parallel\tau(p_2)
}
%\begin{code}
%rgReduce d _ (Atm (App nop [ App tn1 [p1]      --  tau(p1)
%                           , App tn2 [p2] ]))  --  tau(p2)
% | nop == n_meet && tn1 == n_tau && tn2 == n_tau
%    = Just("meet of "++n_tau, Atm (tau (p1 `u` p2)), True )
% | nop == n_join && tn1 == n_tau && tn2 == n_tau
%    = Just("join of "++n_tau, Atm (tau (p1 `i` p2)), True )
%\end{code}
%
\RLEQNS{
   \lnot\tau(p) &=& \tau(\overline p)
}
%\begin{code}
%rgReduce d _ (Comp nn [Atm (App tnm [p])])
% | nn == nNot && tnm == n_tau
%   = Just( nNot++"-"++n_tau, Atm (App tnm [complement p]), True )
%\end{code}
%
\RLEQNS{
   \assume~\pi \sqcap \epsilon(r)
   &=&
   \pi \sqcap \epsilon(r) \sqcap \epsilon(\overline{r})\bot
}
%
%
%The final catch-all pattern:
%\begin{code}
%rgReduce _ _ _ = Nothing
%\end{code}
%
%\HDRc{law Entry}
%
%\begin{code}
%lawEntry :: Dict
%lawEntry = entry laws $ LawEntry [rgReduce] [] []
%\end{code}

\HDRb{RG Dictionary}
\begin{code}
rgDict :: Dict
rgDict
 = mergeDicts
    [ dictVersion ("RGAlgebra "++rgVersion)

    -- Concurrent Refinement Algebra
    , cEntry, dEntry
    , meetEntry
    , joinEntry
    , rfdbyEntry
    , seqEntry
    , seqRedEntry
    , conjSeqRedEntry -- omit if doing CSP/CCS !!
    , repeatEntry

    -- Test Sub-algebra
    , tEntry, t'Entry
    , parEntry
    , assertEntry
    , testRedEntry

    -- Abstract Atomic Steps
    , aEntry, bEntry
    , alfEntry
    , assumeEntry
    , bangEntry
    , atmParIdEntry
    , actionEntry
    , atmRedEntry
    , conjAtmRedEntry -- omit if doing CSP/CCS !!

    -- Relational Atomic Steps
    , relAtmRedEntry

    -- Relies and Guarantees
    , piResEntry
    , guarEntry
    , wkconjEntry
    , wkconjRedEntry
    , epsAsmEntry
    , relyEntry
    , satEntry
    , quinEntry

    --, piEntry
    --, epsEntry
--     , iiEntry
--     , piUEntry
--     , epsUEntry
--     , tauEntry
--     , seqEntry
--     , preEntry
--     , assumeEntry
    -- , assertEntry
    -- , lawEntry

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

rglog = putStrLn . calcPrint

rgcalcput pr = (rgcalc pr) >>= rglog
\end{code}
