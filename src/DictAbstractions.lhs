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

\newpage
\HDRb{Unary Operator Abstractions}

\HDRc{Prefix Predicate Transformer}

\RLEQNS{
   \textbf{\textsf{PT}} P &=& \ldots
}
\begin{code}
prefixPT :: String                       -- name
         -> Int                          -- precedence
         -> Maybe ( Dict s
                    -> Pred s -> Pred s) -- optional defn expander
         -> ( Pred s -> Pred s           -- builder
            , Dict s)                    -- entry
prefixPT n_PT precPT optDefnPT
 = let

     mkPT pr = Comp n_PT [pr]

     appSep
      | length n_PT == 1 && (not . isAlpha $ head n_PT)  =  ""
      | otherwise                                        =  " "

     ppPT sCP d p [pr]
      = paren p precPT
            $ pplist [ppa n_PT, ppa appSep, sCP precPT 1 pr]
     ppPT sCP d p _ = pps styleRed $ ppa $ error n_PT
     error nm = "invalid-"++nm++", only one argument allowed"

     defnPT d [pr]
       = case optDefnPT of
          Nothing        ->  Nothing
          Just expandPT  ->  Just (n_PT, expandPT d pr, True)

   in ( mkPT
      , entry n_PT $ PredEntry subAny ppPT [] defnPT noDefn )
\end{code}

\newpage
\HDRb{Binary Operator Abstractions}

\HDRc{Semi-Lattice Operators}

\RLEQNS{
   (a \oplus b) \oplus c &=& a \oplus (b \oplus c)
\\ 1 \oplus a & = a = & a \oplus 1
\\ 0 \oplus a 7 = 0 = 7 a \oplus 0
}

Associative binary operators with both unit and zero elements.
\begin{code}
opSemiLattice :: (Ord s, Show s)
              => String
              -> Pred s
              -> Pred s
              -> Int
              -> ( [Pred s] -> Pred s
                 , Dict s)
opSemiLattice n_SL zero unit precSL
 = let

     isSL (Comp name _)  =  name == n_SL
     isSL _              =  False

     mkSL [] = unit
     mkSL [pr] = pr
     mkSL prs = mkAssoc n_SL isSL [] prs

     ppSL sCP d p []   = sCP p 0 unit
     ppSL sCP d p [pr] = sCP p 1 pr
     ppSL sCP d p prs
      = paren p precSL
          $ ppopen (pad n_SL)
          $ ppwalk 1 (sCP precSL) prs

     simpSL d prs  = sLattice d (n_SL++"-simplify") mkSL zero unit prs

   in ( mkSL
      , entry n_SL $ PredEntry subAny ppSL [] noDefn simpSL )
\end{code}

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
