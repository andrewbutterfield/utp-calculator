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

\HDRb{Definitions}

\HDRc{Structure of concurrent program algebra}

We have:
\RLEQNS{
       & \top
\\ \nil &      & \alf
\\     & \chaos
\\ & \bot
}
\begin{code}
n_top  = _top    ; top  = PVar n_top
n_nil = "nil" ; nil = PVar n_nil
n_alf = _alpha ; alf = PVar n_alf
n_chaos = "chaos" ; chaos = PVar n_chaos
n_bot = _bot ; bot = PVar n_bot
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

\newpage
\HDRb{Algebra Redux}


\HDRc{From the FM2016 Tutorial}
\RLEQNS{
       & \top
\\ \nil &      & \alf
\\     & \chaos
\\ & \bot
}

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

\RLEQNS{
   r \subseteq \Sigma \times \Sigma
\\ π(r) &=& \Pi(\sigma,\sigma'), (\sigma,\sigma') \in r
\\ ϵ(r) &=& \mathcal{E}(\sigma,\sigma'), (\sigma,\sigma') \in r
\\ \stutter &=& \pi(\id)
\\ \pi &=& \pi(\univ)
\\ \epsilon &=& \epsilon(\univ)
\\ p &\subseteq& \Sigma
\\ τ(p) &=& \mbox{if $p$ then terminate else $\top$}
\\ \pre~ t &=& t \sqcap \lnot t \bot
\\  &=& t \sqcap (\lnot t) \seq \bot
\\ \setof p &=& \pre~\tau(p)
\\ &=& \tau(p) \sqcap \tau(\overline{p})\bot
\\ !  && \mbox{not sure what this is}
\\ \assume~ a &=& a \sqcap (!a) \bot
\\ \pi(\emp) &=& \top
\\ \epsilon(\emp) &=& \top
\\ \tau(\emp) &=& \top
\\ \tau(\Sigma) &=& \nil
\\ \tau(p_1) \sqcap \tau(p_2) &=& \tau(p_1 \cup p_2)
\\ \tau(p_1) \sqcup \tau(p_2) &=& \tau(p_1 \cap p_2)
\\                            &=& \tau(p_1)\tau(p_2)
\\                            &=& \tau(p_1)\parallel\tau(p_2)
\\ \lnot\tau(p) &=& \tau(\overline p)
\\ \assume~\pi \sqcap \epsilon(r)
   &=&
   \pi \sqcap \epsilon(r) \sqcap \epsilon(\overline{r})\bot
}

\newpage
\HDRb{From the FM2016 (joint-Best) Paper}

\HDRc{Introduction}

Assume $a$, $b$ atomic, $c$, $d$ arbitrary processes.
\RLEQNS{
   (a;c)\parallel(b;d) &=& (a\parallel b);(c\parallel d)
\\ (a;c)\ileave(b;d) &=& a;(c\ileave b;d) \sqcap b;(a;c\ileave d)
}

\HDRc{Concurrent Refinement Algebra}~

Concurrent Refinement Algebra (CRA):
\[
(\mathcal C,\sqcap,\sqcup,;,\parallel,\bot,\top,\nil,\Skip)
\]
Complete, distributive lattice:
$
(\mathcal C,\sqcap,\sqcup,\bot,\top)
$.
\RLEQNS{
   c \sqsubseteq d &\defs& (c \sqcap d) = c
\\ \bot \subseteq &c& \subseteq \top
}
Monoid:
$
  (\mathcal C, ;, \nil)
$.
\RLEQNS{
   \top ; c &=& \top
\\ \bot ; c &=& \bot
\\ c ; \top &\neq& \top
\\ c ;\bot &\neq& \bot
\\ (\bigsqcap C) ; d &=& \bigsqcap_{c \in C}(c;d)
\\ c^0 &\defs& \nil
\\ c^{i+1} &\defs& c ; c^i
\\ c^\star &\defs& \nu x . \nil \sqcap c ; x
\\ c^\omega &\defs& \mu x . \nil \sqcap c ;x
\\ c^\infty &\defs& c^\omega ; \top
\\ c^\omega &=& \nil \sqcap c ; c^\omega
\\ c^\star &=& \nil \sqcap c ; c^\star
\\ c^\infty &=& c ; c^\infty ~=~ c^i ; c^\infty ~=~ c^\infty ; d
}
True in their relational model, but generally in CCS or CSP:
\RLEQNS{
   D \neq \setof{} &\implies& c;(\bigsqcap D) = \bigsqcap_{d \in D}(c;d)
}
It says that ; is \emph{conjunctive}.
Needed for the following:
\RLEQNS{
   c^\omega &=& c^\star \sqcap c^\infty
\\ c^\star &=& \bigsqcap_{i \in \Nat} c^i
\\ c^\omega ; d &=& c^\star;d \sqcap c^\infty
\\ c;c^\omega;d &=& c;c^\star;d \sqcap c^\infty
}

\HDRc{The Boolean Sub-algebra of Tests}~

Test commands: $t \in \mathcal B \subseteq C$, extended algebra:
\[
(\mathcal C,\mathcal B,\sqcap,\sqcup,;,\parallel,\bot,\top,\nil,\Skip,\lnot)
\]
Test Boolean algebra --- sub-lattice of CRA:
$
(\mathcal B,\sqcap,\sqcup,\lnot,\top,\nil)
$

$\mathcal B$ closed under $\sqcap, \sqcup, ;, \parallel$.

Assume $t \in \mathcal B$, arbitrary test.
\RLEQNS{
   t;t' &=& t \sqcup t'
\\ t\parallel t' &=& t \sqcup t'
\\ (t;c) \parallel (t;d) &=& t;(c\parallel d)
\\ (t;c) \sqcup (t';d) &=& (t \sqcup t') ; (c \sqcup d)
\\ \Assert~t &\defs& t \sqcap \lnot t ; \bot
\\ \lnot \top &=& \nil
}

\HDRc{Abstract Atomic Steps}~

Atomic Steps commands: $a,b \in \mathcal A \subseteq C$.

Atomic Action Boolean algebra --- sub-lattice of CRA:
$
(\mathcal A,\sqcap,\sqcup,!,\top,\alf)
$
\RLEQNS{
   \alf \sqcup \nil &=& \top
}

$\mathcal A$ closed under $\sqcap, \sqcup, \parallel$, but not $;$.

\RLEQNS{
   a \parallel \wait &=& a
\\ a;c \parallel b;d &=& (a \parallel b);(c\parallel d)
\\ a;c \sqcup b;d &=& (a \sqcup b);(c \sqcup d)
\\ a;c \parallel \nil &=& \top
\\ a;c \sqcup \nil &=& \top
\\ a \sqcup !a &=& \top
\\ a \sqcap !a &=& \alf
\\ !\top &=& \alf
\\ \assume~a &\defs& a \sqcap (!a);\bot
}

Given any $c$ there are $t$, $t'$, $I$, $a_i$ and $c_i$ such that:
\RLEQNS{
   c &=& t \sqcap t';\bot \sqcap \bigsqcap_{i \in I}(a_i ; c_i)
\\ \Skip &\defs& \wait^\omega
\\ \wait^\omega \parallel c &=& c
\\ a^\star\parallel \nil &=& \nil
\\ a^\omega\parallel \nil &=& \nil
\\ a^\infty\parallel \nil &=& \top
\\ a^i;c \parallel b^i;d &=& (a\parallel b)^i ; (c \parallel d)
}
If ; is conjunctive:
\RLEQNS{
   a^\star \parallel b^\star &=& (a \parallel b)^\star
\\ a^\infty \parallel b^\infty &\defs?& (a \parallel b)^\infty
\\ a^\star;c \parallel b^\star;d
   &=&
   (a \parallel b)^\star
   ;
   ( (c \parallel d)
     \sqcap
     (c \parallel b;b^\star;d)
     \sqcap
     (a;a^\star;c \parallel d) )
\\ a^\star;c \parallel b^\infty
   &=&
   (a\parallel b)^\star; (c\parallel b^\infty)
\\ a^\omega;c \parallel b^\omega;d
   &=&
   (a \parallel b)^\omega
   ;
   ( (c \parallel d)
     \sqcap
     (c \parallel b;b^\omega;d)
     \sqcap
     (a;a^\omega;c \parallel d) )
\\ \action a &\defs& \wait^\omega ; a; \wait^\omega
\\ \action a \parallel \action b
   &=&
   \action{a\parallel b}
   \sqcap \action a ; \action b
   \sqcap \action b ; \action a
\\ a \ileave b &=& a;b \sqcap b;a
}


\HDRc{Relational Atomic Steps}~

\RLEQNS{
   \sigma &\in& \Sigma
\\ r &\in& \Set(\Sigma\times\Sigma)
\\ \pi &:& \Set(\Sigma\times\Sigma) \fun \mathcal A
\\ \epsilon &:& \Set(\Sigma\times\Sigma) \fun \mathcal A
\\ \pi(\emptyset) ~~= &\top& =~~ \epsilon(\emptyset)
\\ \pi(r_1) \sqcup \epsilon(r_2) &=& \top
}
For $s \in \setof{\pi,\epsilon}$:
\RLEQNS{
   r_1=r_2 &\Leftrightarrow& s(r_1)=s(r_2)
\\ s(r_1 \cup r_2) &=& s(r_1) \sqcap s(r_2)
\\ s(r_1 \cap r_2) &=& s(r_1) \sqcup s(r_2)
\\ r_1 \subseteq r_2 &\implies& s(r_2) \sqsubseteq s(r_1)
}

\RLEQNS{
   p &\in& \Set\Sigma
\\ \tau &:& \Set\Sigma \fun \mathcal B
\\ \tau(\emptyset) &=& \top
\\ \tau(\Sigma) &=& \nil
\\ \{p\} &\defs& \Assert~\tau(p)
\\     &  =  & \tau(p) \sqcap \tau(\lnot p);\bot
\\ \{\emptyset\} &=& \bot
\\ \{\Sigma\} &=& \nil
}

\HDRc{Relies and Guarantees}~

\RLEQNS{
   g &\in& \Set(\Sigma\times\Sigma)
\\ (\piRestrict~g) &\defs& \pi(g) \sqcap \wait
\\ \guar~g &\defs& (\piRestrict~g)^\omega
\\ g_1 \subseteq q_2 &\implies& (\piRestrict~g_2) \sqsubseteq (\piRestrict~g_1)
}

\RLEQNS{
   c \Cap \bot &=& \bot
\\ (c \Cap c') \Cap c'' &=& c \Cap (c' \Cap c'')
\\ c \Cap d &=& d \Cap c
\\ c \Cap c &=& c
\\ c \Cap (\bigsqcap D) &=& (\bigsqcap_{d \in D} c \Cap d), D \neq \setof{}
\\ a \Cap b &=& a \sqcup b
\\ t \Cap t' &=& t \sqcup t'
\\ (a;c) \Cap (b;d) &=& (a \Cap b);(c \Cap d)
\\ (a;c) \Cap \nil &=& \top
\\ a^\infty \Cap b^\infty &=& (a \Cap b)^\infty
\\ a \Cap \alf &=& a
\\ \chaos &\defs& \alf^\omega
\\ a^\omega \Cap b^\omega &=& (a \Cap b)^\omega
\\ (\piRestrict~ g_1) \Cap (\piRestrict~g_2) &=& (\piRestrict(g_1 \cap g_2))
\\ a^\omega \Cap (c;d) &=& (a^\omega \Cap c);(a^\omega \Cap d)
\\ (guar~g) \Cap (c;d) &=& (\guar~g \Cap c) ; (\guar~g \Cap d)
}

\RLEQNS{
   (\epsAssm~r) &\defs& \assume(!\epsilon(\overline r))
\\ &=& !\epsilon(\overline r) \sqcap \epsilon(\overline r);\bot
\\ \rely~r &\defs& (\epsAssm~r)^\omega
\\ \assume~a \Cap \assume~b &=& \assume(a \sqcup b)
\\ (\rely~r) \Cap (c;d) &=& (\rely~r \Cap c);(\rely~r \Cap d)
}

Rely-Guarantee quintuple: $\setof{p,r}c\setof{g,q}$

\RLEQNS{
   \term &\defs& \epsilon^\omega (\pi;\epsilon^\omega)^\star
\\ ~[q] 
   &\defs& 
   \bigsqcap_{\sigma\in\Sigma}
    \tau(\setof{\sigma}) 
    ; \term 
    ; \tau(\setof{\sigma'\in\Sigma|(\sigma,\sigma')\in q})
\\ \setof{p,r}c\setof{g,q}
   &\defs&
   \{p\}(\rely~r \Cap \guar~g \Cap [q]) \sqsubseteq c
}

\HDRc{Abstract Communication in Process Algebras}~
