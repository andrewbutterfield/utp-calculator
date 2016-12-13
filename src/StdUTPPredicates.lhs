\HDRa{Standard UTP Predicates}\label{ha:std-UTP-preds}
\begin{code}
module StdUTPPredicates where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcPredicates
import DictAbstractions
import StdPrecedences
import StdPredicates
import StdUTPPrecedences
\end{code}

Here we provide dictionary entries for all our ``standard''
UTP program/specification forms.


\newpage

\HDRb{Standard UTP Definitions}\label{hb:std-UTP-defs}

\HDRc{Non-composite Predicates}

\begin{code}
bT = noMark T
bF = noMark F
\end{code}

\HDRc{Lattice Top/Bottom}\label{hc:def-Top-Bot}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mTop & \tTop
\\ &|& \mBot & \tBot
}
\begin{code}
nTop = "Top" ; nBot = "nBot"
isTop = isComp nTop ; isBot  = isComp nBot

mkTop = Comp nTop []
mkBot = Comp nBot []

ppTop _ d p _ = ppa "T"
ppBot _ d p _ = ppa "_|_"

defnTop d _ = Just ("",F,diff) -- assuming full predicate lattice
defnBot d _ = Just ("",T,diff) -- assuming full predicate lattice

topEntry
 = ( nTop
   , PredEntry [] ppTop [] defnTop (pNoChg nTop) )
botEntry
 = ( nBot
   , PredEntry [] ppBot [] defnBot (pNoChg nBot) )
\end{code}


\newpage
\HDRc{Non-deterministic Choice}\label{hc:def-NDC}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mNDC & \tNDC
}
\begin{code}
nNDC = "NDC" ; isNDC  = isComp nNDC

mkNDC [] = T
mkNDC [pr] = pr
mkNDC prs = mkAssoc nNDC isNDC [] prs

ppNDC sCP d p []    =  sCP p 0 T
ppNDC sCP d p [pr]  =  sCP p 1 pr
ppNDC sCP d p prs
 = paren p precNDC
     $ ppopen " |~| "
     $ ppwalk 1 (sCP precNDC) prs

simpNDC d mprs  = psLattice d "|~|-simplify" mkNDC mkBot mkTop mprs

ndcEntry :: (String, Entry)
ndcEntry
 = ( nNDC
   , PredEntry ["*"] ppNDC [] (pNoChg nNDC) simpNDC )
\end{code}



\newpage
\HDRc{Refinement}\label{hc:def-Rfdby}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mRby & \tRby
}
\begin{code}
nRfdby = "Rfdby" ; isRfdby  = isComp nRfdby

mkRfdby pr1 pr2 = Comp nRfdby [pr1,pr2]

ppRfdby sCP d p [pr1,pr2]
 = paren p precRfdby
     $ ppopen " |= " [ sCP precRfdby 1 pr1
                     , sCP precRfdby 2 pr2 ]
ppRfdby _ _ _ _ = pps styleRed $ ppa "invalid-|="

simpRfdby d [T, pr2] = Just ("true-|=",T,diff)
simpRfdby d [pr1, F] = Just ("|=-false",T,diff)
simpRfdby d [pr1, pr2] = Nothing

rfdbyEntry :: (String, Entry)
rfdbyEntry
 = ( nRfdby
   , PredEntry [] ppRfdby []
               (pNoChg nRfdby) simpRfdby )

-- build an Rfdby at the MPred level
bRfdby mpr1 mpr2 = noMark $ mkRfdby mpr1 mpr2
\end{code}

\newpage
\HDRc{Conditional}\label{hc:def-Cond}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mCond & \tCond
}
\begin{code}
nCond = "Cond" ; isCond  = isComp nCond

mkCond pr1 pr2 pr3 = Comp nCond [pr1,pr2,pr3]

ppCond sCP d p [prt,prc,pre]
 = paren p precCond
      $ pplist [ sCP precCond 1 prt
               , ppa " <| "
               , sCP 0 2 prc
               , ppa " |> "
               , sCP precCond 3 pre ]
ppCond sCP d p prs = pps styleRed $ ppa "invalid-<|>"

simpCond d [pr1, T, pr3] = Just ("true-cond",pr1,diff)
simpCond d [pr1, F, pr3] = Just ("false-cond",pr3,diff)
simpCond _ _ = Nothing

condEntry :: (String, Entry)
condEntry
 = ( nCond
   , PredEntry ["*"] ppCond [] (pNoChg nCond) simpCond )
\end{code}

\newpage
\HDRc{Skip}\label{hc:def-Skip}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mSkip & \tSkip
}
\begin{code}
nSkip = "Skip" ; isSkip  = isComp nSkip

mkSkip = Comp nSkip []

shSkip = "II"
ppSkip _ _ _ _ = ppa shSkip

simpSkip _ _ = Nothing

skipEntry
  = ( nSkip
    , PredEntry [] ppSkip [] simpSkip simpSkip )
\end{code}

\newpage
\HDRc{Sequencing}\label{hc:def-Seq}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mSeq & \tSeq
}
\begin{code}
nSeq = "Seq" ; isSeq  = isComp nSeq

mkSeq mpr1 mpr2 = Comp nSeq [mpr1,mpr2]

ppSeq sCP d p [pr1,pr2]
 = paren p precSeq
     $ ppopen " ; " [ sCP precSeq 1 pr1
                    , sCP precSeq 2 pr2 ]
ppSeq _ _ _ _ = pps styleRed $ ppa "invalid-;"

simpSeq d [ F, pr ] = Just ( "simp-;", F, diff )
simpSeq d [ pr, F ] = Just ( "simp-;", F, diff )
simpSeq d [ pr1, pr2 ]
\end{code}
  $\Skip \seq p = p$
\begin{code}
 | isSkip pr1  =  Just ( "simp-;", pr2, diff )
\end{code}
  $p \seq \Skip = p$
\begin{code}
 | isSkip pr2  =  Just ( "simp-;", pr1, diff )

 | otherwise   =  Nothing

seqEntry :: (String, Entry)
seqEntry
 = ( nSeq
   , PredEntry [] ppSeq [] (pNoChg nSeq) simpSeq )
\end{code}

\newpage
\HDRc{Iteration}\label{hc:def-Iter}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mIter & \tIter
}
\begin{code}
nIter = "Iter" ; isIter  = isComp nIter

mkIter mpr1 mpr2 = Comp nIter [mpr1,mpr2]

ppIter sCP d p [pr1,pr2]
 = paren p precIter
     $ ppopen " * " [ sCP precIter 1 pr1
                    , sCP precIter 2 pr2 ]
ppIter _ _ _ _ = pps styleRed $ ppa "invalid-*"

simpIter d [pr1, F ]
 = Just ("c-*-false", mkAnd [mkNot pr1, mkSkip], diff)
simpIter d [pr1, pr2 ] = Nothing

iterEntry :: (String, Entry)
iterEntry
 = ( nIter
   , PredEntry [] ppIter [] (pNoChg nIter) simpIter )
\end{code}
