\HDRa{Calculator Simplificiation}\label{ha:calc-simp}
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

An auxilliary:
\begin{code}
justify chgd txt = if chgd then txt else ""
\end{code}



\begin{code}
simplified = "simplify"

simplify :: (Ord s, Show s) => m -> Dict m s -> CalcStep m s
simplify m d mpr@(ms,(Atm e))
 = case esimp d e of
    (chgd,B True)   ->  (justify chgd simplified,(ms,T))
    (chgd,B False)  ->  (justify chgd simplified,(ms,T))
    (chgd,e')       ->  (justify chgd simplified,(ms,Atm e'))
simplify m d mpr@(ms,pr) = ( "", mpr)
\end{code}

\HDRc{Predicate Simplification}

Predicate simplification:
\begin{code}
-- psimp :: (Eq s, Ord s, Show s) => m -> Dict m s -> Pred m s -> (String,Pred m s)
-- psimp m d (Equal e1 e2) = sEqual (esimp d e1) (esimp d e2)
-- psimp m d (Comp name prs) = error "psimp Comp NYI"
-- psimp m d (PSub (PVar p) sub) = pvsubst m d p (ssimp d sub)
-- psimp m d (PSub pr1 sub) = psubst (ssimp d sub) $ psimp m d pr1
-- psimp m d pr = ("",pr)
\end{code}

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


\HDRc{Expression Simplification}

\begin{code}
esimp :: (Eq s, Ord s, Show s) => Dict m s -> Expr s -> (Bool, Expr s)
esimp d (App fn es) = asimp d fn $ esimps d False [] es
esimp d (Sub e subs)
 = let
    (chgd,e') = esimp d e
    (chgds,subs') = ssimp d subs
   in (chgd||chgds, Sub e' subs')
esimp d e = (False, e)

esimps :: (Eq s, Ord s, Show s)
       => Dict m s -> Bool -> [Expr s]-> [Expr s] -> (Bool, [Expr s])
esimps d chgd se [] = (chgd, reverse se)
esimps d chgd se (e:es)
 = let (chgd',e') = esimp d e
   in esimps d (chgd||chgd') (e:se) es
\end{code}

\HDRd{Substitution Simplification}~

\begin{code}
ssimp :: (Eq s, Ord s, Show s) => Dict m s -> Substn s -> (Bool,Substn s)
ssimp d subs
 = let
    (vs,es) = unzip subs
    (chgd,es') = esimps d False [] es
   in (chgd, zip vs es')
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

\HDRd{Function Simplification}~
\begin{code}
asimp :: (Eq s, Ord s, Show s)
      => Dict m s -> String -> (Bool,[Expr s]) -> (Bool, Expr s)
asimp d fn (chgd,es)
 = case elookup fn d of
     Nothing  ->  (chgd, App fn es)
     Just (ExprEntry _ _ _ _ evalf)
       -> case evalf d es of
            ( "", _ )  ->  (chgd, App fn es)
            ( _, e)    ->  (True, e)
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
