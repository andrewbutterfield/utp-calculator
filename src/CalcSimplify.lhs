\HDRa{Calculator Simplification}\label{ha:calc-simp}
\begin{code}
module CalcSimplify where
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

Predicate simplification
does not use the recursive predicate search just described,
but instead is a recursive descent,
where sub-components at any level are simplified first,
and then that level is simplified using predicate variant-specific rules
(like (\texttt{sImp} mentioned above).

\HDRc{Preliminaries}

At the top-level,
when we attempt to apply some rule,
we return a \texttt{CalcResult} --- a pairing of a string with a predicate.
If the string is empty, then no change occurred,
otherwise it supplies a (short ?!) justification/explanation
for what has happened.


For convenience,
the expression simplification functions return a pair with the string
replaced by a predicate that is true if a change occurred.
\begin{code}
diff, same :: Bool
diff = True
same = False
\end{code}


\HDRb{Expression Simplification}


The top-level expression simplifier.
\begin{code}
esimp :: (Eq s, Ord s, Show s) => Dict m s -> Expr s -> (Bool, Expr s)
esimp d (App fn es) = asimp d fn $ esimps d same [] es
esimp d (Sub e subs)
 = let
    (chgd,e') = esimp d e
    (chgds,subs') = ssimp d subs
   in (chgd||chgds, Sub e' subs')
esimp d e = (same, e)
\end{code}

Simplifying lists of expressions:
\begin{code}
esimps :: (Eq s, Ord s, Show s)
       => Dict m s -> Bool -> [Expr s]-> [Expr s] -> (Bool, [Expr s])
esimps d chgd se [] = (chgd, reverse se)
esimps d chgd se (e:es)
 = let (chgd',e') = esimp d e
   in esimps d (chgd||chgd') (e:se) es
\end{code}

\HDRc{Function Simplification}~
\begin{code}
asimp :: (Eq s, Ord s, Show s)
      => Dict m s -> String -> (Bool,[Expr s]) -> (Bool, Expr s)
asimp d fn (chgd,es)
 = case elookup fn d of
     Nothing  ->  (chgd, App fn es)
     Just (ExprEntry _ _ _ _ evalf)
       -> case evalf d es of
            ( "", _ )  ->  (chgd, App fn es)
            ( _, e)    ->  (diff, e)
\end{code}

\HDRc{Substitution Simplification}~
\begin{code}
ssimp :: (Eq s, Ord s, Show s) => Dict m s -> Substn s -> (Bool,Substn s)
ssimp d subs
 = let
    (vs,es) = unzip subs
    (chgd,es') = esimps d False [] es
   in (chgd, zip vs es')
\end{code}

\HDRb{Predicate Simplification}

Given a predicate, original marking,
the explanation and new mark associated with this operation
and the changed flag, produce the appropriate result:
\begin{code}
mkCR :: (Mark m, Ord s, Show s) 
     => Pred m s -> [m] -> String -> m -> Bool -> CalcResult m s
mkCR pr ms what m True   = (what,addMark m (ms,pr))
mkCR pr ms what m False  = ("",(ms,pr))
\end{code}
For composites, we only mark the composite if it changes,
and not if it is just sub-components that have changed:
\begin{code}
mkCompR :: (Mark m, Ord s, Show s)
     => Pred m s -> [m] -> String -> m 
     -> Bool -- top has changed
     -> Bool -- change somewhere
     -> CalcResult m s
mkCompR comp ms what m _ False     = ("",             (ms,comp))
mkCompR comp ms what m False True  = (what,           (ms,comp))
mkCompR comp ms what m True True   = (what, addMark m (ms,comp))
\end{code}


Now, the predicate simplifier:
\begin{code}
simplified = "simplify"
simplify :: (Mark m, Ord s, Show s) => m -> Dict m s -> CalcStep m s
\end{code}
For atomic predicates, 
we simplify the underlying expression,
and lift any variable booleans to their predicate equivalent.
\begin{code}
simplify m d mpr@(ms,(Atm e))
 = case esimp d e of
    (chgd,B True)   ->  mkCR T        ms simplified m chgd
    (chgd,B False)  ->  mkCR F        ms simplified m chgd
    (chgd,e')       ->  mkCR (Atm e') ms simplified m chgd
\end{code}
For equality we simplify both expressions,
and then attempt to simplify the equality to true or false.
\begin{code}
simplify m d mpr@(ms,(Equal e1 e2))
 = let
    (chgd1,e1') = esimp d e1
    (chgd2,e2') = esimp d e2
    (chgd',pr') = sEqual e1' e2'
    chgd = chgd1 || chgd2 || chgd'
   in if chgd then (simplified,addMark m (ms,pr')) else ("",mpr)
\end{code}
For composites,
we first simplify the components,
and then look in the dictionary by name for a simplifier.
\begin{code}
simplify m d mpr@(ms,(Comp name mprs))
 = let
    (subchgs,mprs') = subsimp m d same [] mprs
    (what,comppr') = compsimp m d name mprs'
    topchgd = not $ null what
   in mkCompR (Comp name mprs') 
                     ms simplified m topchgd (subchgs||topchgd)
 where

   subsimp m d chgd mprs' [] = (chgd,reverse mprs')
   subsimp m d chgd mprs' (mpr:mprs)
    = let (what,mpr') = simplify m d mpr
      in if null what 
       then subsimp m d chgd (mpr:mprs')  mprs
       else subsimp m d diff (mpr':mprs') mprs
       
   compsimp m d name mprs'
    = case plookup name d of
       Just (PredEntry _ _ _ _ psimp)  ->  psimp d mprs'
       _                               ->  ("",Comp name mprs')
\end{code}
For predicate substitutions,
we first simplify the substitution part,
and them
make a distinction between predicate variables,
and general predicates.
\begin{code}
simplify m d mpr@(ms,(PSub spr subs))
 = sbstsimp m d ms (ssimp d subs) spr
 where
\end{code}
For predicate variables,
we look to see if we have information about their alphabets,
which can be used to remove some elements from the substitution.
\begin{code}
  sbstsimp m d ms (subchgd,subs') spr@(mp,PVar p) 
    = case vlookup p d of
        Just (AlfEntry alf)
            ->  ("",(ms,mkPSub spr $ filter ((`elem` alf) . fst) subs'))
        _   ->  ("",mpr)
\end{code}
In the general case,
we simplify both predicate and substitution parts,
and combine.
\begin{code}
  sbstsimp m d ms (subschgd,subs') spr
   = let
      (what,spr') = simplify m d spr
      topchgd = not $ null what
     in mkCompR (PSub spr' subs')
                      ms simplified m topchgd (subschgd||topchgd)
\end{code}
All other cases are as simple as can be, considering\ldots
\begin{code}
simplify m d mpr@(ms,pr) = ( "", mpr)
\end{code}

\HDRc{Equality Predicate Simplification}~
\begin{code}
sEqual :: Eq s => Expr s -> Expr s -> (Bool, Pred m s)

sEqual (St s1) (St s2)
 | s1 == s2     = (diff,T)
 | otherwise    = (diff,F)

sEqual (B t1) (B t2)
 | t1 == t2   = (diff,T)
 | otherwise  =  (diff,F)

sEqual (Var v1) (Var v2)
 | v1 == v2   = (diff,T)

sEqual (St _) (B _) = (diff,F)
sEqual (B _) (St _) = (diff,F)

sEqual e1 e2
 | e1 == e2   =  (diff,T)
 | otherwise  =  (same,Equal e1 e2)
\end{code}



If we have information about the alphabet of a predicate variable
then the following law is really useful:
\RLEQNS{
   P[\vec e/\vec x] &=& P[\vec e/\vec x]\!|_{\alpha P}
   & \elabel{pvar-substn}
}
\begin{code}
-- pvsubst :: (Ord s) => m -> Dict m s -> String -> Substn s -> Pred m s
-- pvsubst m d p sub
--  = case vlookup p d of
--      Nothing  ->  mkPSub pr sub
--      Just alf  ->  mkPSub pr $ filter ((`elem` alf) . fst) sub
--  where
--    pr = PVar p
\end{code}




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
esubst sub (Sub e sub') = esubst sub $ esubst sub' e
esubst sub e = e
\end{code}

\HDRd{Predicate Substitution}

We note that some constructs
cannot be substituted into until their definitions are expanded.

\begin{code}
--psubst :: Ord s => Substn s -> Dict m s -> Dict m s

-- psubst _ T = T
-- psubst _ F = F
--
-- psubst sub pr@(PVar _) = PSub pr sub
--
-- psubst sub (Equal e1 e2) = Equal (esubst sub e1) (esubst sub e2)
-- psubst sub (Atm e) = Atm $ esubst sub e
-- psubst sub (Comp name prs) = Comp name $ map (psubst sub) prs
-- -- we need to use subcomp here, unlike above,
-- -- because psubst can return a PSub
-- psubst sub (PSub pr sub') = psubst (subcomp sub sub') pr
--
-- -- the rest are non-substitutable (n.s.)
-- psubst sub pr  =  mkPSub pr sub
\end{code}

We sometimes need to know when we can substitute:
\begin{code}
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






Lifting predicates
\begin{code}
(|||) p q x = p x || q x
(&&&) p q x = p x && q x
\end{code}


Dictionary-based variable properties:
\begin{code}
-- isDyn, isDyn', isDynObs, notDynObs :: Dict m s -> String -> Bool
-- isDyn d v = v `elem` (fromJust $ alookup aDyn d)
-- isDyn' d v' = v' `elem` (fromJust $ alookup aDyn' d)
-- isDynObs d = isDyn d ||| isDyn' d
-- notDynObs d = not . isDynObs d
\end{code}

Lifting variable functions to expressions:
\begin{code}
-- allEV :: Ord s => (String -> Bool) -> Expr s -> Bool
-- allEV vp  (Var v) = vp v
-- allEV vp  (App _ es) = all (allEV vp) es
-- allEV vp  (Sub e sub) = allEV vp $ esubst sub e
-- allEV vp  _ = True
--
-- mapEV :: Ord s => (String -> String) -> Expr s -> Expr s
-- mapEV f (Var v) = Var $ f v
-- mapEV f (App fn es) = App fn $ map (mapEV f) es
-- mapEV f (Sub e sub) = mapEV f $ esubst sub e
-- mapEV _ e = e
\end{code}

Lifting variable functions to predicates:
\begin{code}
-- allPV :: Ord s => (String -> Bool) -> Dict m s -> Bool
-- allPV vp T = True
-- allPV vp F = True
-- allPV vp (Equal e1 e2) = allEV vp e1 && allEV vp e2
-- allPV vp (Atm e) = allEV vp e
-- allPV vp (Comp _ prs) = all (allPV vp) prs
-- allPV vp pr = False
\end{code}

We also want to know when an expression is ``ground'',
i.e., has no (free) dynamic observation variables:
\begin{code}
-- isDashed, notDashed :: Ord s => Expr s -> Bool
-- isDashed = allEV isDash
-- notDashed = allEV notDash
--
-- isGround, notGround :: Ord s => Dict m s -> Expr s -> Bool
-- isGround d = allEV (notDynObs d)
-- notGround d = allEV (isDynObs d)
--
-- unDash, dash :: Ord s => Expr s -> Expr s
-- unDash = mapEV remDash
-- dash = mapEV addDash
--
-- isCondition :: Ord s => Dict m s -> Bool
-- isCondition = allPV notDash
\end{code}
