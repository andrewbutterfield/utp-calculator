\HDRa{Standard Laws}\label{ha:std-laws}
\begin{code}
module StdLaws where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcPredicates
\end{code}


\HDRb{Introduction}

A failed step returns a null string,
and the predicate part is generally considered undefined.
\begin{code}
nope :: CalcResult s
nope = ( "", error "calc. step failed" )
\end{code}
Given a decision, we can resolve a conditional step
into a completed one:
\begin{code}
cconvert :: (Ord s, Show s)
         => Dict s -> Int -> CCalcResult s -> CalcResult s
cconvert d i ( nm, outcomes ) -- i is typically obtained from user
 = ( nm ++ ", given "++ pdshow d cnd, res )
 where (cnd, res) = outcomes !! (i-1)
\end{code}
We split the steps into the following categories:
\begin{description}
  \item[Theory Independent]
     These are steps based on basic laws of predicate calculus,
     and common (almost) standard UTP constructs.
    \begin{description}
      \item[Simplify]
        Apply a range of usual predicate simplifications
\begin{code}
simplify :: (Eq s, Ord s, Show s) => Dict s -> CalcStep s
\end{code}
      \item[Unroll]
        Loop unrolling is best not done as part of simplification or reducing,
        as it could simply run forever, so we keep it as a separate action
        to be invoked by the user.
\begin{code}
unroll :: Ord s => CalcStep s
\end{code}
    \end{description}
  \newpage
  \item[Theory Dependent]
    These are proof steps tailored to a specific UTP theory,
    which we shall capture using a record.
\begin{code}
data ThSteps s
 = TS{
\end{code}
    \begin{description}
      \item[Reduce]
        Apply a law of predicate calculus in a direction that ``makes progress''.
\begin{code}
   reduce :: Dict s -> CalcStep s
\end{code}
      \item[Definition]
        Expand a definition
\begin{code}
 , defn :: CalcStep s
\end{code}
      \item[Conditional]
        Apply a conditional law, also in a direction that makes progress.
\begin{code}
 , creduce :: Dict s -> CCalcStep s
\end{code}
    \end{description}
\begin{code}
}
\end{code}
 \end{description}

\HDRb{Supporting Calculation Steps}

We rely upon two key mechanisms to support our calculator,
common to most of the step categories above.
The first is a general search procedure that takes a targetted rule
as a parameter, and searches systematically through a predicate
until, and if, it finds a point where it can be applied.
The second is the use of Haskell pattern matching
to make rules easy to implement,
along with a generalisation that goes beyond ordinary pattern matching.

Simple pattern matching is very useful,
as exemplified by the implementation of the following simplication
rule:
\RLEQNS{
   \true \implies P &=& P
}
which is rendered in Haskell as
\begin{verbatim}
sImp T pr = pr
\end{verbatim}

Lifting predicates
\begin{code}
(|||) p q x = p x || q x
(&&&) p q x = p x && q x
\end{code}


Dictionary-based variable properties:
\begin{code}
isDyn, isDyn', isDynObs, notDynObs :: Dict s -> String -> Bool
isDyn d v = v `elem` (fromJust $ alookup aDyn d)
isDyn' d v' = v' `elem` (fromJust $ alookup aDyn' d)
isDynObs d = isDyn d ||| isDyn' d
notDynObs d = not . isDynObs d
\end{code}

Lifting variable functions to expressions:
\begin{code}
allEV :: Ord s => (String -> Bool) -> Expr s -> Bool
allEV vp  (Var v) = vp v
allEV vp  (App _ es) = all (allEV vp) es
allEV vp  (Set es) = all (allEV vp) es
allEV vp  (Sub e sub) = allEV vp $ esubst sub e
allEV vp  _ = True

mapEV :: Ord s => (String -> String) -> Expr s -> Expr s
mapEV f (Var v) = Var $ f v
mapEV f (App fn es) = App fn $ map (mapEV f) es
mapEV f (Sub e sub) = mapEV f $ esubst sub e
mapEV _ e = e
\end{code}

Lifting variable functions to predicates:
\begin{code}
allPV :: Ord s => (String -> Bool) -> Pred s -> Bool
allPV vp T = True
allPV vp F = True
allPV vp (Equal e1 e2) = allEV vp e1 && allEV vp e2
allPV vp (Atm e) = allEV vp e
allPV vp (Not pr) = allPV vp pr
allPV vp (And prs) = all (allPV vp) prs
allPV vp (Or prs) = all (allPV vp) prs
allPV vp (Imp pr1 pr2) = allPV vp pr1 && allPV vp pr2
allPV vp pr = False
\end{code}

We also want to know when an expression is ``ground'',
i.e., has no (free) dynamic observation variables:
\begin{code}
isDashed, notDashed :: Ord s => Expr s -> Bool
isDashed = allEV isDash
notDashed = allEV notDash

isGround, notGround :: Ord s => Dict s -> Expr s -> Bool
isGround d = allEV (notDynObs d)
notGround d = allEV (isDynObs d)

unDash, dash :: Ord s => Expr s -> Expr s
unDash = mapEV remDash
dash = mapEV addDash

isCondition :: Ord s => Pred s -> Bool
isCondition = allPV notDash
\end{code}


\newpage
\HDRb{Predicate Building utilities}

We have some  functions that build predicates
in smart and/or useful ways.

We  have smart builders that optimise on the fly:
\begin{code}
mkAnd []   = T
mkAnd [pr] = pr
mkAnd prs   = mkAssoc And isAnd [] prs

mkOr []   = F
mkOr [pr] = pr
mkOr prs  = mkAssoc Or isOr [] prs

mkAssoc op isOp srp [] = op $ reverse srp
mkAssoc op isOp srp (pr:prs)
 | isOp pr = mkAssoc op isOp (reverse (predPrs pr)++srp) prs
 | otherwise  = mkAssoc op isOp (pr:srp) prs

predPrs (And prs) = prs
predPrs (Or prs) = prs
predPrs _ = []

mkPSub pr []  = pr
mkPSub pr sub = PSub pr $ sort sub
\end{code}

Next we define some predicate builders
that take a list of sub-components,
rather than as seperate arguments.
This facilitates a uniform way of dealing with predicate constructors
of varying arity:
\begin{code}
lnot [p]      = Not p
imp [p,q]     = Imp p q
cond [c,p,q]  = Cond c p q
psub sub [p]  = mkPSub p sub
seqs [p,q]    = Seq p q
iter [p,q]    = Iter p q
patm [p]      = PAtm p
pseq [p,q]    = PSeq p q
ppar [p,q]    = PPar p q
pcond [c,p,q] = PCond c p q
piter [p,q]   = PIter p q
\end{code}


\newpage
\HDRb{Recursive Predicate Search}


We now look at applying calculation steps by recursively exploring
a predicate, and returning when we succeed.

\begin{code}
apply :: Ord s => CalcStep s -> Pred s -> CalcResult s
apply step pr -- check top-level first
 = case step pr of
     ( "", _ ) ->  rapply step pr  -- look deeper
     res       ->  res

-- recursive descent
rapply :: Ord s => CalcStep s -> Pred s -> CalcResult s
rapply step (Not p) = mapplies lnot step [p]
rapply step (And prs) = mapplies And step prs
rapply step (Or prs) = mapplies Or step prs
rapply step (Imp p1 p2) = mapplies imp step [p1,p2]
rapply step (Cond p1 p2 p3) = mapplies cond step [p1,p2,p3]
rapply step (PSub p sub) = mapplies (psub sub) step [p]
rapply step (Seq p1 p2) = mapplies seqs step [p1,p2]
rapply step (Iter p1 p2) = mapplies iter step [p1,p2]
rapply step (PFun f prs) = mapplies (PFun f) step prs
rapply step (PAtm p) = mapplies patm step [p]
rapply step (PSeq p1 p2) = mapplies pseq step [p1,p2]
rapply step (PPar p1 p2) = mapplies ppar step [p1,p2]
rapply step (PCond p1 p2 p3) = mapplies pcond step [p1,p2,p3]
rapply step (PIter p1 p2) = mapplies piter step [p1,p2]
rapply step pr = ( "", pr )

-- calls pred-list handler below, then applies the constructor
mapplies :: Ord s
 => ([Pred s] -> Pred s) -> CalcStep s -> [Pred s] -> CalcResult s
mapplies cons step prs
 = ( comment, cons prs' )
 where ( comment, prs' ) = rapplies step prs

-- process a list of predicates, stopping if success occurs
rapplies :: Ord s => CalcStep s -> [Pred s] -> ( String, [Pred s] )
rapplies _ [] = ( "", [] )
rapplies step [pr]
 = ( comment, [pr']) where ( comment, pr' ) = apply step pr
rapplies step (pr:prs)
 = case apply step pr of
     (  "", _ ) -- no success yet, keep looking!
       -> ( comment, pr:prs' )
          where ( comment, prs' ) = rapplies step prs
     ( comment, pr' ) -- success ! Stop here.
       -> ( comment, pr':prs )
\end{code}

\newpage
Now, doing it conditionally%
\footnote{
  It should be possible to implement both \texttt{apply} and \texttt{capply}
  as a single traverse function with appropriate higher
  function parameters, but right now my head hurts!
}
\begin{code}
capply :: Ord s => CCalcStep s -> Pred s -> CCalcResult s
capply cstep pr
 = case cstep pr of
     ( "", _ ) ->  crapply cstep pr
     res       ->  res

crapply :: Ord s => CCalcStep s -> Pred s -> CCalcResult s
crapply cstep (Not p) = cmapplies lnot cstep [p]
crapply cstep (And prs) = cmapplies And cstep prs
crapply cstep (Or prs) = cmapplies Or cstep prs
crapply cstep (Imp p1 p2) = cmapplies imp cstep [p1,p2]
crapply cstep (Cond p1 p2 p3) = cmapplies cond cstep [p1,p2,p3]
crapply cstep (PSub p sub) = cmapplies (psub sub) cstep [p]
crapply cstep (Seq p1 p2) = cmapplies seqs cstep [p1,p2]
crapply cstep (Iter p1 p2) = cmapplies iter cstep [p1,p2]
crapply cstep (PFun f prs) = cmapplies (PFun f) cstep prs
crapply cstep (PAtm p) = cmapplies patm cstep [p]
crapply cstep (PSeq p1 p2) = cmapplies pseq cstep [p1,p2]
crapply cstep (PPar p1 p2) = cmapplies ppar cstep [p1,p2]
crapply cstep (PCond p1 p2 p3) = cmapplies pcond cstep [p1,p2,p3]
crapply cstep (PIter p1 p2) = cmapplies piter cstep [p1,p2]
crapply cstep p = ( "", [] )

cmapplies :: Ord s
          => ([Pred s] -> Pred s) -> CCalcStep s -> [Pred s]
          -> CCalcResult s
cmapplies cons cstep prs
 = ( comment, mapsnd cons crps )
 where ( comment, crps ) = crapplies cstep prs

crapplies :: Ord s => CCalcStep s -> [Pred s]
                   -> ( String, [(Pred s,[Pred s])] )
crapplies _ [] = ( "", [] )
crapplies cstep [pr]
 = ( comment, mapsnd (:[]) crps' )
 where ( comment, crps' ) = capply cstep pr
crapplies cstep (pr:prs)
 = case capply cstep pr of
     (  "", _ )
       -> ( comment, mapsnd (pr:) crps' )
          where ( comment, crps' ) = crapplies cstep prs
     ( comment, crps' )
       -> ( comment, mapsnd (:prs) crps' )
\end{code}

\HDRb{Simplification}

Predicate simplification
does not use the recursive predicate search just described,
but instead is a recursive descent,
where sub-components at any level are simplified first,
and then that level is simplified using predicate variant-specific rules
(like (\texttt{sImp} mentioned above).
\begin{code}
simplify d pr
 | pr' == pr  =  ( "", pr )
 | otherwise  =  ( "simplify",  pr' )
 where pr' = psimp d pr
\end{code}

\HDRc{Predicate Simplification}

Predicate simplification:
\begin{code}
psimp :: (Eq s, Ord s, Show s) => Dict s -> Pred s -> Pred s
psimp d (Equal e1 e2) = sEqual (esimp d e1) (esimp d e2)
psimp d (Atm e)
 = case esimp d e of
    B True   ->  T
    B False  ->  F
    e'       ->  Atm e'
psimp d (Not (Not pr)) = psimp d pr
psimp d (Not pr) = sNot $ psimp d pr
psimp d (And prs) = sLattice mkAnd F T $ map (psimp d) prs
psimp d (Or prs)  = sLattice  mkOr T F $ map (psimp d) prs
psimp d (Imp pr1 pr2) = sImp (psimp d pr1) (psimp d pr2)
psimp d (Cond pr1 pr2 pr3)
      = sCond (psimp d pr1) (psimp d pr2) (psimp d pr3)
psimp d (PSub (PVar p) sub) = pvsubst d p (ssimp d sub)
psimp d (PSub pr1 sub) = psubst (ssimp d sub) $ psimp d pr1
psimp d (Seq pr1 pr2) = Seq (psimp d pr1) (psimp d pr2)
psimp d (Iter pr1 pr2) = Iter (psimp d pr1) (psimp d pr2)
psimp d (PFun str prs) = PFun str $ map (psimp d) prs
psimp d (PAtm pr) = PAtm $ psimp d pr
psimp d (PSeq pr1 pr2) = PSeq (psimp d pr1) (psimp d pr2)
psimp d (PPar pr1 pr2) = PPar (psimp d pr1) (psimp d pr2)
psimp d (PCond pr1 pr2 pr3)
       = PCond (psimp d pr1) (psimp d pr2) (psimp d pr3)
psimp d (PIter pr1 pr2) = PIter (psimp d pr1) (psimp d pr2)
psimp d pr = pr
\end{code}

\newpage
\HDRd{Equality Simplification}~
\begin{code}
sEqual (St s1) (St s2)
 | s1 == s2     = T
 | otherwise    = F
sEqual (St _) _ = F
sEqual _ (St _) = F

sEqual e1 e2
 | e1 == e2   =  T
 | otherwise  =  Equal e1 e2
\end{code}

\HDRd{Not Simplification}~
\begin{code}
sNot T = F
sNot F = T
sNot pr = Not pr
\end{code}

\HDRd{And/Or Simplification}~
\begin{code}
sLattice op zero unit prs
 = zcheck $ filter (/= unit) prs
 where
   zcheck prs
    | any (==zero) prs  =  zero
    | otherwise = op prs
\end{code}


\HDRd{Implication Simplification}~
\begin{code}
sImp T pr = pr
sImp F pr = T
sImp pr F = sNot pr
sImp pr T = T
sImp pr1 pr2 = Imp pr1 pr2
\end{code}

\HDRd{Conditional Simplification}~
\begin{code}
sCond T p q = p
sCond F p q = q
sCond c p q = Cond c p q
\end{code}

\HDRc{Expression Simplification}

\begin{code}
esimp :: (Eq s, Ord s, Show s) => Dict s -> Expr s -> Expr s
esimp d (App fn es) = asimp d fn $ map (esimp d) es
esimp d (Set es) = mkSet $ map (esimp d) es
esimp d (Sub e sub) = esubst (ssimp d sub) $ esimp d e
esimp d e = e
\end{code}

\HDRd{Substitution Simplification}~

\begin{code}
ssimp :: (Eq s, Ord s, Show s) => Dict s -> Substn s -> Substn s
ssimp d sub = mapsnd (esimp d) sub
\end{code}

If we have information about the alphabet of a predicate variable
then the following law is really useful:
\RLEQNS{
   P[\vec e/\vec x] &=& P[\vec e/\vec x]\!|_{\alpha P}
   & \elabel{pvar-substn}
}
\begin{code}
pvsubst :: (Ord s) => Dict s -> String -> Substn s -> Pred s
pvsubst d p sub
 = case vlookup p d of
     Nothing  ->  mkPSub pr sub
     Just alf  ->  mkPSub pr $ filter ((`elem` alf) . fst) sub
 where
   pr = PVar p
\end{code}

\HDRd{Function Simplification}~
\begin{code}
asimp :: (Eq s, Ord s, Show s)
      => Dict s -> String -> [Expr s] -> Expr s
asimp d fn es
 = case flookup fn d of
     Nothing  ->  App fn es
     Just (FD _ _ _ evalf)
       -> case evalf d es of
            ( "", _ )  ->  App fn es
            ( _, e)    ->  e
\end{code}


\HDRc{Substitution Application}

\HDRd{Variable Substitution}~
\begin{code}
vsubst :: Substn s -> String -> Expr s
vsubst [] v = Var v
vsubst ((u,e):subs) v
 | u == v  =  e
 | otherwise  =  vsubst subs v
\end{code}

\HDRd{Expression Substitution}~
\begin{code}
esubst :: Ord s => Substn s -> Expr s -> Expr s
esubst sub (Var v) =  vsubst sub v
esubst sub (App fn es) = App fn $ map (esubst sub) es
esubst sub (Set es)  = mkSet $ map (esubst sub) es
esubst sub (Sub e sub') = esubst sub $ esubst sub' e
esubst sub e = e
\end{code}

\HDRd{Predicate Substitution}

We note that some constructs
cannot be substituted into until their definitions are expanded.

\begin{code}
psubst :: Ord s => Substn s -> Pred s -> Pred s

psubst _ T = T
psubst _ F = F

psubst sub pr@(PVar _) = PSub pr sub

psubst sub (Equal e1 e2) = Equal (esubst sub e1) (esubst sub e2)
psubst sub (Atm e) = Atm $ esubst sub e
psubst sub (Not pr) = Not $ psubst sub pr
psubst sub (And prs) = And $ map (psubst sub) prs
psubst sub (Or prs) = Or $ map (psubst sub) prs
psubst sub (Imp pr1 pr2) = Imp (psubst sub pr1) (psubst sub pr2)
psubst sub (Cond pr1 pr2 pr3)
 = Cond (psubst sub pr1) (psubst sub pr2) (psubst sub pr3)
-- we need to use subcomp here, unlike above,
-- because psubst can return a PSub
psubst sub (PSub pr sub') = psubst (subcomp sub sub') pr

-- the rest are non-substitutable (n.s.)
psubst sub pr  =  mkPSub pr sub
\end{code}

We sometimes need to know when we can substitute:
\begin{code}
canSub Skip  =  False
canSub (Seq _ _) = False
canSub (Iter _ _) = False
canSub (PFun _ _) = False
canSub (PAtm _) = False
canSub (PSeq _ _) = False
canSub (PPar _ _) = False
canSub (PCond _ _ _) = False
canSub (PIter _ _) = False
canSub _ = True
\end{code}

\newpage
\HDRd{Substitution composition}

We can define it as follows, where common target variables ($x_i$) are listed
first in each w.l.o.g.:
\begin{eqnarray*}
   \lefteqn{[e_1,\ldots,e_c,e_{c+1},\ldots,e_{c+m}
            /x_1,\ldots,x_c,y_1,\ldots,y_m]}
\\ \lefteqn{~[f_1,\ldots,f_c,f_{c+1},\ldots,f_{c+n}
            /x_1,\ldots,x_c,z_1,\ldots,z_n]}
\\ &\defs& [ e_1\rho,\ldots,e_c\rho,e_{c+1}\rho,\ldots,e_{c+m}\rho
           ~,~
             f_{c+1},\ldots,f_{c+n}
           / x_1,\ldots,x_c,y_1,\ldots,y_m
           ~,~
             z_1,\ldots,z_n]
\\ &=& \mathit{zip}~ v~ (v\sigma\rho)
\\ && \WHERE
\\ && \rho = [f_1,\ldots,f_c,f_{c+1},\ldots,f_{c+n}
             /x_1,\ldots,x_c,z_1,\ldots,z_n]
\\ && \sigma = [e_1,\ldots,e_c,e_{c+1},\ldots,e_{c+m}
               /x_1,\ldots,x_c,y_1,\ldots,y_m]
\\ && v = \seqof{x_1,\ldots,x_c,y_1,\ldots,y_m
                ,
                z_1,\ldots,z_n}
\end{eqnarray*}
\begin{code}
subcomp sub2 sub1
 = subsub++newsub
 where
   subsub = map (vesubst sub2) sub1
   vs' = map fst sub1
   newsub = filter (not . covered vs') sub2
   covered vs' (v,e) = v `elem` vs'

vesubst sub (v,e) = (v,esubst sub e)
\end{code}


\newpage
\HDRb{Free Variable Predicates}

It can be useful to know if a variable occurs free in a predicate.
However without full definition expansions of composites,
or information about predicate (meta/schematic)-variables,
it is hard to be definitive.
We define ``definitely-so'' predicates (\texttt{dftlyP}),
 that return true if certain the property holds,
 but use a false result to indicate either definitely false,
 or unable to tell.
This means that \texttt{dftlyP} is not equal to \texttt{not . dftlyNotP}.

Mostly, we want to know if $x \notin P$.
\begin{code}
dftlyNotInP :: Dict s -> String -> Pred s -> Bool

dftlyNotInP d v (PVar p)
 = case vlookup p d of
    Just alf_p -> not (v `elem` alf_p)
    Nothing -> False

dftlyNotInP d v (Equal e1 e2) = dftlyNotInE d v e1 && dftlyNotInE d v e2
dftlyNotInP d v (Atm e) = dftlyNotInE d v e

dftlyNotInP _ _ T = True
dftlyNotInP _ _ F = True
dftlyNotInP d v (Not pr) = dftlyNotInP d v pr
dftlyNotInP d v (And prs) = all (dftlyNotInP d v) prs
dftlyNotInP d v (Or prs) = all (dftlyNotInP d v) prs
dftlyNotInP d v (Imp pr1 pr2) = all (dftlyNotInP d v) [pr1,pr2]
dftlyNotInP d v (Cond pr1 pr2 pr3) = all (dftlyNotInP d v) [pr1,pr2,pr3]
dftlyNotInP d v (Iter pr1 pr2) = all (dftlyNotInP d v) [pr1,pr2]

dftlyNotInP d v (PSub pr sub) = False -- for now

dftlyNotInP d v Skip -- d'=d for all d in dyn
 = case alookup aDyn d of
    Just dyn -> not (v `elem` dyn)
    _ -> case alookup aDyn' d of
          Just dyn' -> not (v `elem` dyn')
          _ -> False

dftlyNotInP d v (Seq pr1 pr2)
 | isDash v   =  dftlyNotInP d v pr2
 | otherwise  =  dftlyNotInP d v pr1

-- we return false for all UTCP predicates

dftlyNotInP _ _ _ = False -- not true, or can't tell !
\end{code}

\newpage
For expressions:
\begin{code}
dftlyNotInE :: Dict s -> String -> Expr s -> Bool
dftlyNotInE d v (B _) = True
dftlyNotInE d v (Var x) = v /= x
dftlyNotInE d v (App _ es) = all (dftlyNotInE d v) es
dftlyNotInE d v (Set es) = all (dftlyNotInE d v) es
dftlyNotInE d v (Sub e sub) = False -- for now
dftlyNotInE _ _ _ = False
\end{code}



\HDRb{Generalised Matching}

A ``recogniser'' is simply a predicate over predicates:
\begin{code}
type Recogniser s = Pred s -> Bool

isAnd :: Recogniser s
isAnd (And _) = True
isAnd _ = False
isOr :: Recogniser s
isOr (Or _) = True
isOr _ = False
\end{code}

\HDRc{Match Recogniser}

We want some pattern matching that is
``position-independent'',
in order to exploit the commutativity and associativity properties
of certain logical operators.
In effect we want to generalise a pattern like
\[
 A \land p
\]
to a single pattern that finds $p$ where it occurs in a list
\[
 A_1 \land \ldots \land A_{i-1}
 \land p \land
  A_{i+1} \land \ldots \land A_n,
 \qquad
 i \in 1\ldots n
\]
Function \texttt{matchRecog} takes a recogniser and a list of predicates,
and if a predicate $A_i$ matching $p$ is found,
then returns a triple as follows:
\[
   (~\seqof{A_1, \ldots, A_{i-1}},
     A_i,
     \seqof{A_{i+1}, \ldots, A_n}~)
\]
\begin{code}
matchRecog :: (Ord s, Show s)
           => Recogniser s -> [Pred s]
           -> Maybe ([Pred s],Pred s,[Pred s])
matchRecog recog prs
 = mR [] prs
 where
   mR erofeb [] = Nothing  -- "erofeb" = reverse "before"
   mR erofeb (pr:prs)
    | recog pr   =  Just (reverse erofeb, pr, prs)
    | otherwise  =  mR (pr:erofeb) prs
\end{code}


We have some common recognisers:

$e'$, where $\fv{e'} \in \setof{s',ls'}$.
\begin{code}
isDashedObsExpr d (Atm e') = isDashed e' && notGround d e'
isDashedObsExpr _ _        = False
\end{code}
$x' = k$, where $x'$ is an after-observable, and $k$ is ground.
\begin{code}
isAfterEqToConst d (Equal (Var x') k) = isDyn' d x' && isGround d k
isAfterEqToConst _ _                  = False
\end{code}
$x = k$, where $x$ is an nominated observable, and $k$ is ground.
\begin{code}
isObsEqToConst v d (Equal (Var x) k)  =  v == x && isGround d k
isObsEqToConst _ _ _                  =  False
\end{code}
$s'=s$, or $s=s'$
\begin{code}
isIdle s1 s2 = s1=="s" && s2=="s'" || s1=="s'" && s2=="s"
\end{code}
$s'=s$ conjoined with $A$ whose alphabet is $\setof{s,s'}$.
\begin{code}
isIdleSeqAtom d s1 s2 pA
 | isIdle s1 s2
    = case vlookup pA d of
       Nothing  -> False
       Just a_alf  -> sort a_alf == ["s","s'"]
 | otherwise  =  False
\end{code}

\HDRb{Loop-Unroll}
\label{hb:unroll}

We treat a loop-unroll as special
---
we don't want this to always be available
\RLEQNS{
   c * P &=& (P ; c * P) \cond c \Skip
}
\begin{code}
unroll w@(Iter c pr)
 | isCondition c  = lred "loop-unroll" $ Cond c (Seq pr w) Skip
unroll pr = lred "" pr

lred nm pr = ( nm, pr )
\end{code}
