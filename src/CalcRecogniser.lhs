\HDRa{Calculator Recogniser}\label{ha:calc-recog}
\begin{code}
module CalcRecogniser where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcAlphabets
import CalcPredicates
import CalcSimplify
\end{code}

\HDRb{Match Recogniser}

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
           => Recogniser m s -> [MPred m s]
           -> Maybe ([MPred m s],MPred m s,[MPred m s])
matchRecog recog mprs
 = mR [] mprs
 where
   mR erofeb [] = Nothing  -- "erofeb" = reverse "before"
   mR erofeb (mpr:mprs)
    | recog mpr   =  Just (reverse erofeb, mpr, mprs)
    | otherwise  =  mR (mpr:erofeb) mprs
\end{code}


\HDRb{Common Recognisers}

\HDRc{Dashed Atomic Predicate}
\begin{code}
isDashedObsExpr d (Atm e') = isDashed e' && notGround d e'
isDashedObsExpr _ _        = False
\end{code}

\HDRc{After-Obs. equated to Ground Value}

$x' = k$, where $x'$ is an after-observable, and $k$ is ground.
\begin{code}
isAfterEqToConst d (Equal (Var x') k) = isDyn' d x' && isGround d k
isAfterEqToConst _ _                  = False
\end{code}

\HDRc{Named Obs. equated to Ground Value}

$x = k$, where $x$ is an nominated observable, and $k$ is ground.
\begin{code}
isObsEqToConst v d (Equal (Var x) k)  =  v == x && isGround d k
isObsEqToConst _ _ _                  =  False
\end{code}


\HDRb{Supporting Variable Predicates}


Dictionary-based variable properties:
\begin{code}
isDyn, isDyn', isDynObs, notDynObs :: Dict m s -> String -> Bool
isDyn d v
 = case alookup aDyn d of
    Just (AlfEntry alfpart)  ->  v `elem` alfpart
    _                        ->  False
isDyn' d v
 = case alookup aDyn' d of
    Just (AlfEntry alfpart)  ->  v `elem` alfpart
    _                        ->  False
isDynObs d = isDyn d ||| isDyn' d
notDynObs d = not . isDynObs d
\end{code}

Lifting predicates
\begin{code}
(|||) p q x = p x || q x
(&&&) p q x = p x && q x
\end{code}

Lifting variable functions to expressions:
\begin{code}
allEV :: Ord s => (String -> Bool) -> Expr s -> Bool
allEV vp  (Var v) = vp v
allEV vp  (App _ es) = all (allEV vp) es
allEV vp  (Sub e sub) = allEV vp $ snd $ esubst sub e
allEV vp  _ = True

mapEV :: Ord s => (String -> String) -> Expr s -> Expr s
mapEV f (Var v) = Var $ f v
mapEV f (App fn es) = App fn $ map (mapEV f) es
mapEV f (Sub e sub) = mapEV f $ snd $ esubst sub e
mapEV _ e = e
\end{code}

Lifting variable functions to predicates:
\begin{code}
allPV :: Ord s => (String -> Bool) -> Pred m s -> Bool
allPV vp T = True
allPV vp F = True
allPV vp (Equal e1 e2) = allEV vp e1 && allEV vp e2
allPV vp (Atm e) = allEV vp e
allPV vp (Comp _ mprs) = all (allPV vp) $ map snd mprs
allPV vp pr = False
\end{code}

We also want to know when an expression is ``ground'',
i.e., has no (free) dynamic observation variables:
\begin{code}
isDashed, notDashed :: Ord s => Expr s -> Bool
isDashed = allEV isDash
notDashed = allEV notDash

isGround, notGround :: Ord s => Dict m s -> Expr s -> Bool
isGround d = allEV (notDynObs d)
notGround d = allEV (isDynObs d)

unDash, dash :: Ord s => Expr s -> Expr s
unDash = mapEV remDash
dash = mapEV addDash

isCondition :: Ord s => Pred m s -> Bool
isCondition = allPV notDash
\end{code}



\newpage
\HDRc{Definite Predicates}

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
dftlyNotInP :: Dict m s -> String -> Pred m s -> Bool

dftlyNotInP d v (PVar p)
 = case vlookup p d of
    Just (PVarEntry alf_p)  ->  not (v `elem` alf_p)
    _                       ->  False

dftlyNotInP d v (Equal e1 e2)
                      = dftlyNotInE d v e1 && dftlyNotInE d v e2
dftlyNotInP d v (Atm e) = dftlyNotInE d v e

dftlyNotInP _ _ T = True
dftlyNotInP _ _ F = True
dftlyNotInP d v (Comp _ mprs)
                          = all (dftlyNotInP d v) $ map snd mprs

dftlyNotInP d v (PSub mpr sub) = False -- for now

dftlyNotInP _ _ _ = False -- not true, or can't tell !
\end{code}

For expressions:
\begin{code}
dftlyNotInE :: Dict m s -> String -> Expr s -> Bool
dftlyNotInE d v (B _) = True
dftlyNotInE d v (Var x) = v /= x
dftlyNotInE d v (App _ es) = all (dftlyNotInE d v) es
dftlyNotInE d v (Sub e sub) = False -- for now
dftlyNotInE _ _ _ = False
\end{code}
