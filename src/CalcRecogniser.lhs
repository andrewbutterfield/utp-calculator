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
import CalcSysTypes
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
matchRecog :: Recogniser -> [Pred]
           -> Maybe ([Pred],(Pred,[Pred]),[Pred])
matchRecog recog prs
 = mR [] prs
 where
   mR erofeb [] = Nothing  -- "erofeb" = reverse "before"
   mR erofeb (pr:prs)
    = case recog pr of
     Nothing -> mR (pr:erofeb) prs
     Just bits -> Just (reverse erofeb, (pr,bits), prs)
\end{code}



\HDRb{Common Recognisers}

\HDRc{Dashed Atomic Predicate}

\RLEQNS{
  e', \textrm{not ground} &\rightsquigarrow& \seqof{e'}
}
\begin{code}
mtchDashedObsExpr :: Dict -> Recogniser
mtchDashedObsExpr d a'@(Atm e')
                 = condBind (isDashed e' && notGround d e') [a']
mtchDashedObsExpr _ _  = Nothing

isDashedObsExpr d = isJust . mtchDashedObsExpr d
\end{code}

\HDRc{After-Obs. equated to Ground Value}

\RLEQNS{
  x'=k, x' \in Dyn', k \textrm{ ground} &\rightsquigarrow& \seqof{x',k}
}
\begin{code}
mtchAfterEqToConst :: Dict -> Recogniser
mtchAfterEqToConst d (Equal v@(Var x') k)
         = condBind (isDyn' d x' && isGround d k) [Atm v, Atm k]
mtchAfterEqToConst _ _  = Nothing

isAfterEqToConst d = isJust . mtchAfterEqToConst d
\end{code}

\HDRc{Named Obs. equated to Ground Value}

$x = k$, where $x$ is an nominated observable, and $k$ is ground.
\RLEQNS{
  x=k, x \textrm{ named}, k \textrm{ ground} &\rightsquigarrow& \seqof{x,k}
}
\begin{code}
mtchNmdObsEqToConst :: String -> Dict -> Recogniser
mtchNmdObsEqToConst v d (Equal u@(Var x) k)
             =  condBind (v == x && isGround d k) [Atm u, Atm k]
mtchNmdObsEqToConst _ _ _  =  Nothing

isNmdObsEqToConst v d = isJust . mtchNmdObsEqToConst v d
\end{code}

With the above, it can be useful to turn such
an equality into an equivalent substitution pair:
\begin{code}
eqToSub (Equal (Var x) e) = (x,e)
\end{code}


\HDRb{Supporting Variable Predicates}

Lifting variable functions to expressions:
\begin{code}
allEV :: (String -> Bool) -> Expr -> Bool
allEV vp  (Var v) = vp v
allEV vp  (App _ es) = all (allEV vp) es
allEV vp  (Sub e sub) = allEV vp $ snd $ esubst sub e
allEV vp  _ = True

mapEV :: (String -> String) -> Expr -> Expr
mapEV f (Var v) = Var $ f v
mapEV f (App fn es) = App fn $ map (mapEV f) es
mapEV f (Sub e sub) = mapEV f $ snd $ esubst sub e
mapEV _ e = e
\end{code}

Lifting variable functions to predicates:
\begin{code}
allPV :: (String -> Bool) -> Pred -> Bool
allPV vp T = True
allPV vp F = True
allPV vp (Equal e1 e2) = allEV vp e1 && allEV vp e2
allPV vp (Atm e) = allEV vp e
allPV vp (Comp _ prs) = all (allPV vp) prs
allPV vp pr = False
\end{code}

We also want to know when an expression is ``ground'',
i.e., any free variables are limited to being the static parameters:
\begin{code}
isDashed, notDashed :: Expr -> Bool
isDashed = allEV isDash
notDashed = allEV notDash

isGround, notGround :: Dict -> Expr -> Bool
isGround d = allEV (isStc d)
notGround d = not . isGround d

unDash, dash :: Expr -> Expr
unDash = mapEV remDash
dash = mapEV addDash

isCondition :: Pred -> Bool
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
dftlyNotInP :: Dict -> String -> Pred -> Bool

dftlyNotInP d v (PVar p)
 = case plookup p d of
    Just (PredEntry _ _ alf_p _ _)  ->  not (v `elem` alf_p)
    _                               ->  False

dftlyNotInP d v (Equal e1 e2)
                      = dftlyNotInE d v e1 && dftlyNotInE d v e2
dftlyNotInP d v (Atm e) = dftlyNotInE d v e

dftlyNotInP _ _ T = True
dftlyNotInP _ _ F = True
dftlyNotInP d v (Comp _ prs) = all (dftlyNotInP d v) prs

dftlyNotInP d v (PSub mpr sub) = False -- for now
\end{code}

For expressions:
\begin{code}
dftlyNotInE :: Dict -> String -> Expr -> Bool
dftlyNotInE d v (B _) = True
dftlyNotInE d v (Var x) = v /= x
dftlyNotInE d v (App _ es) = all (dftlyNotInE d v) es
dftlyNotInE d v (Sub e sub) = False -- for now
dftlyNotInE _ _ _ = False
\end{code}
