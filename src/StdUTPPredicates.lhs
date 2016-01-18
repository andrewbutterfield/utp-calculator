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
import StdPrecedences
import StdUTPPrecedences
import StdPredicates
import CalcPredicates
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

ppTop d ms p _ = ppa "T"
ppBot d ms p _ = ppa "_|_"

defnTop d _ = ("",F) -- assuming full predicate lattice
defnBot d _ = ("",T) -- assuming full predicate lattice

topEntry
 = ( nTop
   , PredEntry False ppTop defnTop (pNoChg nTop) )
botEntry
 = ( nBot
   , PredEntry False ppBot defnBot (pNoChg nBot) )

-- build Top and Bot at the MPred level
bTop, bBot :: MPred s
bTop = noMark mkTop
bBot = noMark mkBot
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
mkNDC [(_,pr)] = pr
mkNDC mprs = mkAssoc nNDC isNDC [] mprs

ppNDC d ms p [] = showp d ms p T
ppNDC d ms p [mpr] = mshowp d ms p mpr
ppNDC d ms p mprs
 = paren p precNDC
     $ ppopen " |~| "
     $ map (mshowp d ms precNDC) mprs

simpNDC d mprs  = sLattice "|~|-simplify" mkNDC mkBot mkTop mprs

ndcEntry :: (Show s, Ord s) => (String, Entry s)
ndcEntry
 = ( nNDC
   , PredEntry True ppNDC (pNoChg nNDC) simpNDC )

-- build an NDC at the MPred level
bNDC mprs = noMark $ mkNDC mprs
\end{code}



\newpage
\HDRc{Refinement}\label{hc:def-Rfdby}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mRby & \tRby
}
\begin{code}
nRfdby = "Rfdby" ; isRfdby  = isComp nRfdby

mkRfdby mpr1 mpr2 = Comp nRfdby [mpr1,mpr2]

ppRfdby d ms p [mpr1,mpr2]
 = paren p precRfdby
     $ ppopen " |= " [ mshowp d ms precRfdby mpr1
                     , mshowp d ms precRfdby mpr2 ]
ppRfdby d ms p mprs = pps styleRed $ ppa "invalid-|="

simpRfdby d [mpr1, mpr2] = ( "",  mkImp mpr1 mpr2 )

rfdbyEntry :: (Show s, Ord s) => (String, Entry s)
rfdbyEntry
 = ( nRfdby
   , PredEntry False ppRfdby
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

mkCond mpr1 mpr2 mpr3 = Comp nCond [mpr1,mpr2,mpr3]

ppCond d ms p [mprt,mprc,mpre]
 = paren p precCond
      $ pplist [ mshowp d ms precCond mprt
               , ppa " <| "
               , mshowp d ms 0 mprc
               , ppa " |> "
               , mshowp d ms precCond mpre ]
ppCond d ms p mprs = pps styleRed $ ppa "invalid-<|>"

simpCond d [mpr1, mpr2, mpr3] = ( "",  mkCond mpr1 mpr2 mpr3)

condEntry :: (Show s, Ord s) => (String, Entry s)
condEntry
 = ( nCond
   , PredEntry True ppCond simpCond simpCond )

-- build an Cond at the MPred level
bCond mpr1 mpr2 mpr3 = noMark $ mkCond mpr1 mpr2 mpr3
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

ppSkip d _ p _ = ppa "II"

simpSkip d _ = ("",mkSkip)

skipEntry
  = ( nSkip
    , PredEntry False ppSkip simpSkip simpSkip )

-- build Skip at the MPred level
bSkip :: MPred s
bSkip = noMark mkSkip
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

ppSeq d ms p [mpr1,mpr2]
 = paren p precSeq
     $ ppopen " ; " [ mshowp d ms precSeq mpr1
                    , mshowp d ms precSeq mpr2 ]
ppSeq d ms p mprs = pps styleRed $ ppa "invalid-;"

simpSeq d [ mpr1, mpr2    ]
\end{code}
  $\Skip \seq p = p$
\begin{code}
 | isSkip mpr1 = ( "simp-;",  snd mpr2 )
\end{code}
  $p \seq \Skip = p$
\begin{code}
 | isSkip mpr2 = ( "simp-;",  snd mpr1 )

 | otherwise   = ( "", mkSeq mpr1 mpr2 )

seqEntry :: (Show s, Ord s) => (String, Entry s)
seqEntry
 = ( nSeq
   , PredEntry False ppSeq
               (pNoChg nSeq) simpSeq )

-- build an Seq at the MPred level
bSeq mpr1 mpr2 = noMark $ mkSeq mpr1 mpr2
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

ppIter d ms p [mpr1,mpr2]
 = paren p precIter
     $ ppopen " * " [ mshowp d ms precIter mpr1
                    , mshowp d ms precIter mpr2 ]
ppIter d _ p mprs = pps styleRed $ ppa "invalid-*"

simpIter d [mpr1, mpr2 ] = ( "", mkIter mpr1 mpr2 )

iterEntry :: (Show s, Ord s) => (String, Entry s)
iterEntry
 = ( nIter
   , PredEntry False ppIter (pNoChg nIter) simpIter )

-- build an Iter at the MPred level
bIter mpr1 mpr2 = noMark $ mkIter mpr1 mpr2
\end{code}
