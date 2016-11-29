\HDRa{Standard Predicates}\label{ha:std-preds}
\begin{code}
module StdPredicates where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import NiceSymbols
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcAlphabets
import StdPrecedences
import CalcPredicates
import DictAbstractions
\end{code}

Here we provide dictionary entries for all our ``standard''
 predicate forms.

\HDRb{Generic Definitions}\label{hb:gen-defs}


First, a composite recogniser:
\begin{code}
isComp :: String -> Pred -> Bool
isComp cname (Comp nm _)  =  nm == cname
isComp _     _            =  False
\end{code}


\newpage
\HDRb{Standard Definitions}\label{hb:std-defs}


\HDRc{Negation}\label{hc:def-Not}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mNot & \tNot
}
\begin{code}
nNot = _lnot ; isNot  = isComp nNot

mkNot pr = Comp nNot [pr]

ppNot sCP d p [pr] -- ignore marking for now
 = paren p precNot
       $ pplist [ppa _lnot, sCP precNot 1 pr]
ppNot sCP d p _ = pps styleRed $ ppa ("invalid-"++_lnot)
\end{code}
$\lnot\true=\false$
\begin{code}
simpNot d [T] = Just (_lnot++"-simp",F,diff)
\end{code}
$\lnot\false=\true$
\begin{code}
simpNot d [F] = Just (_lnot++"-simp",T,diff)
\end{code}
$\lnot\lnot p = p$
\begin{code}
simpNot d [Comp name [pr]]
 | name == nNot  =  Just (_lnot++_lnot++"-simp",pr,diff)

simpNot _ _ = Nothing

notEntry :: Dict
notEntry
 = entry nNot
   $ PredEntry anyVars ppNot [] (pNoChg nNot) simpNot
\end{code}

\newpage
\HDRc{Conjunction}\label{hc:def-And}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mAnd & \tAnd
}
\begin{code}
nAnd = _land
(mkAnd, andEntry) = popSemiLattice nAnd F T precAnd
\end{code}

\HDRc{Disjunction}\label{hc:def-Or}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mOr & \tOr
}
\begin{code}
nOr = _lor
(mkOr, orEntry) = popSemiLattice nOr T F precOr
\end{code}

\newpage
\HDRc{Implication}\label{hc:def-Imp}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mImp & \tImp
}
\begin{code}
nImp = _implies ; isImp  = isComp nImp

mkImp pr1 pr2 = Comp nImp [pr1,pr2]

ppImp sCP d p [pr1,pr2]
 = paren p (precImp-1) -- bracket self
     $ ppopen (pad _implies) [ sCP precImp 1 pr1
                             , sCP precImp 2 pr2 ]
ppImp sCP d p mprs = pps styleRed $ ppa ("invalid-"++_implies)
\end{code}
$\true \implies p = p$
\begin{code}
simpImp d [ T, pr ] = Just( _implies++"-simp", pr, diff )
\end{code}
$\false \implies p = \true$
\begin{code}
simpImp d [ F, _ ]  = Just ( _implies++"-simp", T, diff )
\end{code}
$p \implies \false = \lnot p$
\begin{code}
simpImp d [pr, F ]  = Just ( _implies++"-simp", mkNot pr, diff )
\end{code}
$p \implies \true = \true$
\begin{code}
simpImp d [ _, T ]  = Just ( _implies++"-simp", T, diff  )

simpImp _ _ = Nothing

impEntry :: Dict
impEntry
 = entry nImp
   $ PredEntry anyVars ppImp [] (pNoChg nImp) simpImp
\end{code}

\newpage
\HDRc{Equivalence}\label{hc:def-Eqv}
\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mEqv & \tEqv
}
\begin{code}
nEqv = _equiv ; isEqv  = isComp nEqv

mkEqv pr1 pr2 = Comp nEqv [pr1,pr2]

ppEqv sCP d p [pr1,pr2]
 = paren p (precEqv-1) -- bracket self
     $ ppopen (pad _equiv) [ sCP precEqv 1 pr1
                           , sCP precEqv 2 pr2 ]
ppEqv sCP d p mprs = pps styleRed $ ppa ("invalid-"++_equiv)
\end{code}
$p \implies p = \true$ (simple cases only)
\begin{code}
simpEqv d [ T, T ]   =  Just ( _equiv++"-simp", T, diff  )
simpEqv d [ F, F ]   =  Just ( _equiv++"-simp", T, diff  )
\end{code}
$\true \equiv p = p$ and \emph{v.v.}
\begin{code}
simpEqv d [ T, pr ]  =  Just ( _equiv++"-simp", pr, diff )
simpEqv d [ pr, T ]  =  Just ( _equiv++"-simp", pr, diff )
\end{code}
$p \equiv \false = \lnot p$ and \emph{v.v.}
\begin{code}
simpEqv d [ pr, F ]  =  Just ( _equiv++"-simp", mkNot pr, diff )
simpEqv d [ F, pr ]  =  Just ( _equiv++"-simp", mkNot pr, diff )
\end{code}
\begin{code}
simpEqv _ _ = Nothing

eqvEntry :: Dict
eqvEntry
 = entry nEqv
   $ PredEntry anyVars ppEqv [] (pNoChg nEqv) simpEqv
\end{code}

\HDRb{Standard Predicate Dictionary}

\begin{code}
stdPredDict :: Dict
stdPredDict
 = mergeDicts
    [ dictVersion "std-pred 0.2"
    , notEntry
    , andEntry
    , orEntry
    , impEntry
    , eqvEntry
    ]
\end{code}
