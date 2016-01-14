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
UTP predicate forms.

\HDRb{Generic Definitions}\label{hb:gen-defs}

First, some generic intelligent composite constructors:

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
isComp cname (_, Comp nm _) = nm == cname ; isComp _ _ = False
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
   , PredEntry True ppNot (pNoChg nNot) simpNot )

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
nAnd = "And" ; isAnd  = isComp nAnd

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
   , PredEntry True ppAnd (pNoChg nAnd) simpAnd )

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

mkOr [] = T
mkOr [(_,pr)] = pr
mkOr mprs = mkAssoc nOr isOr [] mprs

ppOr d ms p [] = showp d ms p T
ppOr d ms p [mpr] = mshowp d ms p mpr
ppOr d ms p mprs
 = paren p precOr
     $ ppopen " \\/ "
     $ map (mshowp d ms precOr) mprs

simpOr d mprs  = sLattice "\\/-simplify" mkOr T F mprs

orEntry :: (Show s, Ord s) => (String, Entry s)
orEntry
 = ( nOr
   , PredEntry True ppOr (pNoChg nOr) simpOr )

-- build an Or at the MPred level
bOr mprs = noMark $ mkOr mprs
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
   , PredEntry True ppImp (pNoChg nImp) simpImp )

-- build an Imp at the MPred level
bImp mpr1 mpr2 = noMark $ mkImp mpr1 mpr2
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
