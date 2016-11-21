\HDRa{Dictionary Abstractions}\label{ha:dict-abs}
\begin{code}
module DictAbstractions where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
--import NiceSymbols
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcAlphabets
import CalcPredicates
\end{code}


We support abstractions of common composite patterns,
most implemented as dictionary entry builder functions.

We want to support a wide range of binary operators,
and well as predicate transformers of interest.

\HDRb{Generic Definitions}\label{hb:gen-defs}


First, a composite recogniser:
\begin{code}
isComp :: String -> Pred s -> Bool
isComp cname (Comp nm _)  =  nm == cname
isComp _     _            =  False
\end{code}


\HDRb{Variable Abstractions}

First, we deal with simple ways to provide \texttt{PredEntry}
for simple predicate variables:
\begin{code}
pvarEntry :: String -> [String] -> Dict s
pvarEntry nm alf
 = entry nm
   $ PredEntry [] ppPVar alf (pNoChg nm) (pNoChg nm)
 where ppPVar _ _ _ _ = ppa nm
\end{code}

\HDRb{Binary Operator Abstrations}

\HDRc{Associative Flattening }~

First, building a flattened associative list:
\begin{code}
mkAssoc
  :: String -> (Pred s -> Bool) -> [Pred s] -> [Pred s]
  -> Pred s
mkAssoc op isOp srp [] = Comp op $ reverse srp
mkAssoc op isOp srp (pr:prs)
 | isOp pr = mkAssoc op isOp (reverse (predPrs pr)++srp) prs
 | otherwise  = mkAssoc op isOp (pr:srp) prs

predPrs (Comp _ prs) = prs  ;  predPrs _ = []
\end{code}

\newpage
\HDRc{Lattice Simplification}~

Given associative binary operator $\otimes$ with zero $0$ and unit $1$
this embodies the following laws:
\RLEQNS{
   0 \otimes x & = 0 = & x \otimes 0
\\ 1 \otimes x & = x = & x \otimes 1
\\ \bigotimes_{i \in \setof{1}} x_i &=& x_1
}
\begin{code}
sLattice :: (Ord s, Show s)
         => Dict s
         -> String               -- op. name
         -> ([Pred s] -> Pred s) -- op. builder
         -> Pred s               -- zero
         -> Pred s               -- unit
         -> [Pred s]             -- op. arguments
         -> RWResult s
sLattice d tag op zero unit prs
 = ret $ simpL [] prs
 where

   simpL srp [] = reverse srp
   simpL srp (pr:prs)
    | pr == zero  =  [zero]
    | pr == unit  =  simpL     srp  prs
    | otherwise   =  simpL (pr:srp) prs

   ret []          =  Just (tag, unit, diff )
   ret [pr]        =  Just (tag, pr, diff )
   ret prs'
    | prs' == prs  =  Nothing
    | null prs'    =  Just (tag, unit, diff )
    | otherwise    =  Just (tag, op prs', diff )
\end{code}
