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
import CalcAlphabets
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

First, building a flattened associative list:
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

Next, a simplifier version that flattens something already built:
\begin{code}
flatAssoc isOp mpr@(ms,Comp op mprs)
 | isOp mpr   = (flatnote,(ms,mkAssoc op isOp [] mprs'))
 | otherwise  = (note,(ms,Comp op mprs'))
 where
   (notes,mprs') = unzip $ map (flatAssoc isOp) mprs
   flatnote = (op++"-flatten")
   note = if all null notes then "" else flatnote
flatAssoc isOp mpr = ("", mpr)
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
         -> [Pred s]
         -> RWResult s
sLattice tag op zero unit prs
 = ret tag $ zcheck $ filter (/= unit) prs
 where
   zcheck mprs
    | any (==zero) prs  =  [zero]
    | otherwise = prs
   ret tag prs'
    | prs' == prs       =  Nothing
    | otherwise         =  Just ( tag, op $ map noMark prs', diff )
\end{code}


\newpage

\HDRb{Standard Definitions}\label{hb:std-defs}


First, a composite recogniser:
\begin{code}
isComp :: String -> Pred s -> Bool
isComp cname (Comp nm _)  =  nm == cname
isComp _     _            =  False

iscomp :: String -> MPred s -> Bool
iscomp s = isComp s . snd
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
simpNot d [T] = Just ("~-simp",F,diff)
\end{code}
$\lnot\false=\true$
\begin{code}
simpNot d [F] = Just ("~-simp",T,diff)
\end{code}
$\lnot\lnot p = p$
\begin{code}
simpNot d [Comp name [(_,pr)]]
 | name == nNot  =  Just ("~~-simp",pr,diff)

simpNot _ _ = Nothing

notEntry :: (Show s, Ord s) => (String, Entry s)
notEntry
 = ( nNot
   , PredEntry anyVars ppNot [] (pNoChg nNot) simpNot )

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
nAnd = "And" ; isAnd  =  isComp nAnd ; isand = iscomp nAnd

mkAnd []   = T
mkAnd [(_,pr)] = pr
mkAnd mprs  = mkAssoc nAnd isand [] mprs

ppAnd d ms p [] = showp d ms p T
ppAnd d ms p [mpr] = mshowp d ms p mpr
ppAnd d ms p mprs
 = paren p precAnd
     $ ppopen " /\\ "
     $ map (mshowp d ms precAnd) mprs

simpAnd d prs  = sLattice "/\\-simplify" mkAnd F T prs

andEntry :: (Show s, Ord s) => (String, Entry s)
andEntry
 = ( nAnd
   , PredEntry anyVars ppAnd [] (pNoChg nAnd) simpAnd )

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
nOr = "Or" ; isOr  = isComp nOr ; isor = iscomp nOr

mkOr [] = F
mkOr [(_,pr)] = pr
mkOr mprs = mkAssoc nOr isor [] mprs

ppOr d ms p [] = showp d ms p F
ppOr d ms p [mpr] = mshowp d ms p mpr
ppOr d ms p mprs
 = paren p precOr
     $ ppopen " \\/ "
     $ map (mshowp d ms precOr) mprs

simpOr d prs  = sLattice "\\/-simplify" mkOr T F prs

orEntry :: (Show s, Ord s) => (String, Entry s)
orEntry
 = ( nOr
   , PredEntry anyVars ppOr [] (pNoChg nOr) simpOr )

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
simpImp d [ T, pr ] = Just( "=>-simp", pr, diff )
\end{code}
$\false \implies p = \true$
\begin{code}
simpImp d [ F, _ ]  = Just ( "=>-simp", T, diff )
\end{code}
$p \implies \false = \lnot p$
\begin{code}
simpImp d [pr, F ]  = Just ( "=>-simp", mkNot $ noMark pr, diff )
\end{code}
$p \implies \true = \true$
\begin{code}
simpImp d [ _, T ]  = Just ( "=>-simp", T, diff  )

simpImp _ _ = Nothing

impEntry :: (Show s, Ord s) => (String, Entry s)
impEntry
 = ( nImp
   , PredEntry anyVars ppImp [] (pNoChg nImp) simpImp )

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
simpEqv d [ T, T ]   =  Just ( "==-simp", T, diff  )
simpEqv d [ F, F ]   =  Just ( "==-simp", T, diff  )
\end{code}
$\true \equiv p = p$ and \emph{v.v.}
\begin{code}
simpEqv d [ T, pr ]  =  Just ( "==-simp", pr, diff )
simpEqv d [ pr, T ]  =  Just ( "==-simp", pr, diff )
\end{code}
$p \equiv \false = \lnot p$ and \emph{v.v.}
\begin{code}
simpEqv d [ pr, F ] = Just ( "==-simp", mkNot $ noMark pr, diff )
simpEqv d [ F, pr ] = Just ( "==-simp", mkNot $ noMark pr, diff )
\end{code}
\begin{code}
simpEqv _ _ = Nothing

eqvEntry :: (Show s, Ord s) => (String, Entry s)
eqvEntry
 = ( nEqv
   , PredEntry anyVars ppEqv [] (pNoChg nEqv) simpEqv )

-- build an Eqv at the MPred level
bEqv mpr1 mpr2 = noMark $ mkEqv mpr1 mpr2
\end{code}
