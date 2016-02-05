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
     (A_i,bits),
     \seqof{A_{i+1}, \ldots, A_n}~)
\]
where $bits$ are any fragments of $A_i$ picked out by the recogniser.
\begin{code}
matchRecog :: (Ord s, Show s)
           => Recogniser s -> [MPred s]
           -> Maybe ([MPred s],(MPred s,[MPred s]),[MPred s])
matchRecog recog mprs
 = mR [] mprs
 where
   mR erofeb [] = Nothing  -- "erofeb" = reverse "before"
   mR erofeb (mpr:mprs)
    | found      =  Just (reverse erofeb, (mpr,bits), mprs)
    | otherwise  =  mR (mpr:erofeb) mprs
    where (found,bits) = recog mpr
\end{code}



\HDRb{Common Recognisers}

\HDRc{Dashed Atomic Predicate}

\RLEQNS{
  e', \textrm{not ground} &\rightsquigarrow& \seqof{e'}
}
\begin{code}
mtchDashedObsExpr :: Ord s => Dict s -> Recogniser s
mtchDashedObsExpr d a'@(_,(Atm e'))
                 = condBind (isDashed e' && notGround d e') [a']
mtchDashedObsExpr _ _  = noMatch

isDashedObsExpr d = fst . mtchDashedObsExpr d
\end{code}

\HDRc{After-Obs. equated to Ground Value}

\RLEQNS{
  x'=k, x' \in Dyn', k \textrm{ ground} &\rightsquigarrow& \seqof{x',k}
}
\begin{code}
mtchAfterEqToConst :: Ord s => Dict s -> Recogniser s
mtchAfterEqToConst d (_,Equal v@(Var x') k)
         = condBind (isDyn' d x' && isGround d k) [atm v, atm k]
mtchAfterEqToConst _ _  = noMatch

isAfterEqToConst d = fst . mtchAfterEqToConst d
\end{code}

\HDRc{Named Obs. equated to Ground Value}

$x = k$, where $x$ is an nominated observable, and $k$ is ground.
\RLEQNS{
  x=k, x \textrm{ named}, k \textrm{ ground} &\rightsquigarrow& \seqof{x,k}
}
\begin{code}
mtchNmdObsEqToConst :: Ord s => String -> Dict s -> Recogniser s
mtchNmdObsEqToConst v d (_,Equal u@(Var x) k)
             =  condBind (v == x && isGround d k) [atm u, atm k]
mtchNmdObsEqToConst _ _ _  =  noMatch

isNmdObsEqToConst v d = fst . mtchNmdObsEqToConst v d
\end{code}

With the above, it can be useful to turn such
an equality into an equivalent substitution pair:
\begin{code}
eqToSub (_,Equal (Var x) e) = (x,e)
\end{code}


\HDRb{Supporting Variable Predicates}

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
allPV :: Ord s => (String -> Bool) -> Pred s -> Bool
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

isGround, notGround :: Ord s => Dict s -> Expr s -> Bool
isGround d = allEV (notDynObs d)
notGround d = allEV (isDynObs d)

unDash, dash :: Ord s => Expr s -> Expr s
unDash = mapEV remDash
dash = mapEV addDash

isCondition :: Ord s => MPred s -> Bool
isCondition = allPV notDash . snd
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
dftlyNotInP :: Dict s -> String -> MPred s -> Bool

dftlyNotInP d v (_,PVar p)
 = case plookup p d of
    Just (PredEntry _ _ alf_p _ _)  ->  not (v `elem` alf_p)
    _                               ->  False

dftlyNotInP d v (_,Equal e1 e2)
                      = dftlyNotInE d v e1 && dftlyNotInE d v e2
dftlyNotInP d v (_,Atm e) = dftlyNotInE d v e

dftlyNotInP _ _ (_,T) = True
dftlyNotInP _ _ (_,F) = True
dftlyNotInP d v (_,Comp _ mprs) = all (dftlyNotInP d v) mprs

dftlyNotInP d v (_,PSub mpr sub) = False -- for now

dftlyNotInP _ _ _ = False -- not true, or can't tell !
\end{code}

For expressions:
\begin{code}
dftlyNotInE :: Dict s -> String -> Expr s -> Bool
dftlyNotInE d v (B _) = True
dftlyNotInE d v (Var x) = v /= x
dftlyNotInE d v (App _ es) = all (dftlyNotInE d v) es
dftlyNotInE d v (Sub e sub) = False -- for now
dftlyNotInE _ _ _ = False
\end{code}
