\HDRa{Standard Predicates}\label{ha:std-preds}
\begin{code}
module StdPredicates where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Debug.Trace
import PrettyPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
\end{code}

Here we provide dictionary entries for all our ``standard''
 predicate forms.

\HDRb{Generic Definitions}\label{hb:gen-defs}

First, we deal with simple ways to provide PredEntry
for simple predicate variables:
\begin{code}
pvarEntry :: String -> [String] -> (String, Entry s)
pvarEntry nm alf
 = (nm, PredEntry [] ppPVar alf (pNoChg nm) (pNoChg nm))
 where ppPVar _ _ _ _ = ppa nm
\end{code}

Now, some generic intelligent composite constructors:

\HDRc{Associative Flattening }~

\begin{code}
mkAssoc
  :: String -> (MPred s -> Bool) -> [MPred s]-> [MPred s]
  -> Pred s
mkAssoc op isOp srpm [] = Comp op $ reverse srpm
mkAssoc op isOp srpm (mpr:mprs)
 | isOp mpr = mkAssoc op isOp (reverse (predPrs mpr)++srpm) mprs
 | otherwise  = mkAssoc op isOp (mpr:srpm) mprs

predPrs (_,Comp _ prs) = prs  ;  predPrs _ = []
\end{code}

\newpage
\HDRc{Lattice Simplification}~

Given binary operator $\otimes$ with zero $0$ and unit $1$
this embodies the following laws:
\RLEQNS{
   0 \otimes x & = 0 = & x \otimes 0
\\ 1 \otimes x & = x = & x \otimes 1
}
\begin{code}
sLattice :: Eq s
         => String
         -> ([MPred s] -> Pred s)
         -> Pred s
         -> Pred s
         -> [MPred s]
         -> (String, Pred s)
sLattice tag op zero unit mprs
 = ret tag $ zcheck $ filter ((/= unit) . snd) mprs
 where
   zcheck mprs
    | any ((==zero) . snd) mprs  =  [([], zero)]
    | otherwise = mprs
   ret tag mprs'
    | map snd mprs'==map snd mprs  =  ( "", op mprs )
    | otherwise                    =  ( tag, op mprs' )
\end{code}


\newpage

\HDRb{Standard Definitions}\label{hb:std-defs}


First, a composite recogniser:
\begin{code}
isComp :: String -> MPred s -> Bool
isComp cname (_, Comp nm _)  =  nm == cname
isComp _     _               =  False
\end{code}

\newpage
\HDRc{Negation}\label{hc:def-Not}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mNot & \tNot
}
\begin{code}
nNot = "Not" ; isNot  = isComp nNot

mkNot mpr = Comp nNot [mpr]

ppNot d ms p [mpr] -- ignore marking for now
 = paren p precNot
       $ pplist [ppa "~", mshowp d ms precNot mpr]
ppNot d ms p _ = pps styleRed $ ppa "invalid-~"
\end{code}
$\lnot\true=\false$
\begin{code}
simpNot d [(m,T)] = ("~-simp",F)
\end{code}
$\lnot\false=\true$
\begin{code}
simpNot d [(m,F)] = ("~-simp",T)
\end{code}
$\lnot\lnot p = p$
\begin{code}
simpNot d [(m,Comp name [(_,pr)])]
 | name == nNot  =  ("~~-simp",pr)

simpNot _ mprs = ("", Comp nNot mprs)

notEntry :: (Show s, Ord s) => (String, Entry s)
notEntry
 = ( nNot
   , PredEntry ["*"] ppNot [] (pNoChg nNot) simpNot )

-- build a Not at the MPred level
bNot mpr = noMark $ mkNot mpr
\end{code}

\newpage
\HDRc{Conjunction}\label{hc:def-And}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mAnd & \tAnd
}
\begin{code}
nAnd = "And" ; isAnd  =  isComp nAnd

mkAnd [] = T
mkAnd [(_,pr)] = pr
mkAnd mprs = mkAssoc nAnd isAnd [] mprs

ppAnd d ms p [] = showp d ms p T
ppAnd d ms p [mpr] = mshowp d ms p mpr
ppAnd d ms p mprs
 = paren p precAnd
     $ ppopen " /\\ "
     $ map (mshowp d ms precAnd) mprs

simpAnd d mprs  = sLattice "/\\-simplify" mkAnd F T mprs

andEntry :: (Show s, Ord s) => (String, Entry s)
andEntry
 = ( nAnd
   , PredEntry ["*"] ppAnd [] (pNoChg nAnd) simpAnd )

-- build an And at the MPred level
bAnd mprs = noMark $ mkAnd mprs
\end{code}

\newpage
\HDRc{Disjunction}\label{hc:def-Or}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mOr & \tOr
}
\begin{code}
nOr = "Or" ; isOr  = isComp nOr

mkOr [] = F
mkOr [(_,pr)] = pr
mkOr mprs = mkAssoc nOr isOr [] mprs

ppOr d ms p [] = showp d ms p F
ppOr d ms p [mpr] = mshowp d ms p mpr
ppOr d ms p mprs
 = paren p precOr
     $ ppopen " \\/ "
     $ map (mshowp d ms precOr) mprs

simpOr d mprs  = sLattice "\\/-simplify" mkOr T F mprs

orEntry :: (Show s, Ord s) => (String, Entry s)
orEntry
 = ( nOr
   , PredEntry ["*"] ppOr [] (pNoChg nOr) simpOr )

-- build an Or at the MPred level
bOr mprs = noMark $ mkOr mprs
\end{code}

\newpage
\HDRc{Implication}\label{hc:def-Imp}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mImp & \tImp
}
\begin{code}
nImp = "Imp" ; isImp  = isComp nImp

mkImp mpr1 mpr2 = Comp nImp [mpr1,mpr2]

ppImp d ms p [mpr1,mpr2]
 = paren p (precImp-1) -- bracket self
     $ ppopen  " => " [ mshowp d ms precImp mpr1
                      , mshowp d ms precImp mpr2 ]
ppImp d ms p mprs = pps styleRed $ ppa "invalid-=>"
\end{code}
$\true \implies p = p$
\begin{code}
simpImp d [ (_,T), (_,pr) ] = ( "=>-simp", pr        )
\end{code}
$\false \implies p = \true$
\begin{code}
simpImp d [ (_,F), _      ] = ( "=>-simp", T         )
\end{code}
$p \implies \false = \lnot p$
\begin{code}
simpImp d [ mpr,  (_,F)   ] = ( "=>-simp", mkNot mpr )
\end{code}
$p \implies \true = \true$
\begin{code}
simpImp d [ _,    (_,T)   ] = ( "=>-simp", T         )

simpImp d [ mpr1, mpr2    ] = ( "",  mkImp mpr1 mpr2 )

impEntry :: (Show s, Ord s) => (String, Entry s)
impEntry
 = ( nImp
   , PredEntry ["*"] ppImp [] (pNoChg nImp) simpImp )

-- build an Imp at the MPred level
bImp mpr1 mpr2 = noMark $ mkImp mpr1 mpr2
\end{code}

\newpage
\HDRc{Equivalence}\label{hc:def-Eqv}
\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mEqv & \tEqv
}
\begin{code}
nEqv = "Eqv" ; isEqv  = isComp nEqv

mkEqv mpr1 mpr2 = Comp nEqv [mpr1,mpr2]

ppEqv d ms p [mpr1,mpr2]
 = paren p (precEqv-1) -- bracket self
     $ ppopen  " == " [ mshowp d ms precEqv mpr1
                      , mshowp d ms precEqv mpr2 ]
ppEqv d ms p mprs = pps styleRed $ ppa "invalid-=="
\end{code}
$p \implies p = \true$ (simple cases only)
\begin{code}
simpEqv d [ (_,T), (_,T)  ] = ( "==-simp", T         )
simpEqv d [ (_,F), (_,F)  ] = ( "==-simp", T         )
\end{code}
$\true \equiv p = p$ and \emph{v.v.}
\begin{code}
simpEqv d [ (_,T), (_,pr) ] = ( "==-simp", pr        )
simpEqv d [ (_,pr), (_,T) ] = ( "==-simp", pr        )
\end{code}
$p \equiv \false = \lnot p$ and \emph{v.v.}
\begin{code}
simpEqv d [ mpr,  (_,F)   ] = ( "==-simp", mkNot mpr )
simpEqv d [ (_,F),  mpr   ] = ( "==-simp", mkNot mpr )
\end{code}
\begin{code}
simpEqv d [ mpr1, mpr2    ] = ( "",  mkEqv mpr1 mpr2 )

eqvEntry :: (Show s, Ord s) => (String, Entry s)
eqvEntry
 = ( nEqv
   , PredEntry ["*"] ppEqv [] (pNoChg nEqv) simpEqv )

-- build an Eqv at the MPred level
bEqv mpr1 mpr2 = noMark $ mkEqv mpr1 mpr2
\end{code}
