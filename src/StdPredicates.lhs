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
  :: String -> (MPred m s -> Bool) -> [MPred m s]-> [MPred m s]
  -> Pred m s
mkAssoc op isOp srpm [] = Comp op $ reverse srpm
mkAssoc op isOp srpm (mpr:mprs)
 | isOp mpr = mkAssoc op isOp (reverse (predPrs mpr)++srpm) mprs
 | otherwise  = mkAssoc op isOp (mpr:srpm) mprs

predPrs (_,Comp _ prs) = prs  ;  predPrs _ = []
\end{code}

\HDRc{Lattice Simplification}~

Given binary operator $\otimes$ with zero $0$ and unit $1$
this embodies the following laws:
\RLEQNS{
   0 \otimes x & = 0 = & x \otimes 0
\\ 1 \otimes x & = x = & x \otimes 1
}
\begin{code}
sLattice tag op zero unit mprs
 = ret tag $ zcheck $ filter ((/= unit) . snd) mprs
 where
   zcheck mprs
    | any ((==zero) . snd) mprs  =  []
    | otherwise = mprs
   ret tag mprs'
    | map snd mprs'==map snd mprs  =  ( "", op mprs )
    | otherwise                    =  ( tag, op mprs' )
\end{code}


\newpage

\HDRb{Standard Definitions}\label{hb:std-defs}
\HDRc{Lattice Top/Bottom}\label{hc:def-Top-Bot}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mTop & \tTop
\\ &|& \mBot & \tBot
}
\begin{code}
isTop (_,Comp "Skip" _) = True  ;  isTop _ = False
isBot (_,Comp "Skip" _) = True  ;  isBot _ = False

mkTop = Comp "Top" []
mkBot = Comp "Bot" []

ppTop d p _ = pps styleBlue $ ppa "T"
ppBot d p _ = pps styleBlue $ ppa "_|_"

simpTop d _ = ("",F) -- assuming full predicate lattice
simpBot d _ = ("",T) -- assuming full predicate lattice

topEntry = ("Top", PredEntry $ PD [] PUndef ppTop simpTop)
botEntry = ("Bot", PredEntry $ PD [] PUndef ppBot simpBot)

-- build Top and Bot at the MPred level
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
mkNot mpr = Comp "Not" [mpr]

ppNot d p [(m,pr)] -- ignore marking for now
 = paren p precNot
       $ pplist [pps styleBlue $ ppa "~", showp d precNot pr]
ppNot d p _ = pps styleRed $ ppa "invalid-~"

simpNot d [(m,T)] = ("~-simp",F)
simpNot d [(m,F)] = ("~-simp",T)
simpNot _ mprs = ("", Comp "Not" mprs)

notEntry :: (Show s, Ord s) => (String, Entry m s)
notEntry = ("Not", PredEntry $ PD ["P"] PUndef ppNot simpNot)

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
isAnd (_,Comp "And" _) = True  ;  isAnd _ = False

mkAnd [] = T
mkAnd [(_,pr)] = pr
mkAnd mprs = mkAssoc "And" isAnd [] mprs

ppAnd d p [] = showp d p T
ppAnd d p [(m,pr)] = showp d p pr
ppAnd d p mprs
 = paren p precAnd
     $ ppsopen styleBlue " /\\ "
     $ map (showp d precAnd . snd) mprs

simpAnd d mprs  = sLattice "/\\-simplify" mkAnd F T mprs

andEntry :: (Show s, Ord s) => (String, Entry m s)
andEntry = ("And", PredEntry $ PD ["P$"] PUndef ppAnd simpAnd)

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
isOr (_,Comp "Or" _) = True  ;  isOr _ = False

mkOr [] = T
mkOr [(_,pr)] = pr
mkOr mprs = mkAssoc "Or" isOr [] mprs

ppOr d p [] = showp d p T
ppOr d p [(m,pr)] = showp d p pr
ppOr d p mprs
 = paren p precOr
     $ ppsopen styleBlue " \\/ "
     $ map (showp d precOr . snd) mprs

simpOr d mprs  = sLattice "\\/-simplify" mkOr T F mprs

orEntry :: (Show s, Ord s) => (String, Entry m s)
orEntry = ("Or", PredEntry $ PD ["P$"] PUndef ppOr simpOr)

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
isNDC (_,Comp "NDC" _) = True  ;  isNDC _ = False

mkNDC [] = T
mkNDC [(_,pr)] = pr
mkNDC mprs = mkAssoc "NDC" isNDC [] mprs

ppNDC d p [] = showp d p T
ppNDC d p [(m,pr)] = showp d p pr
ppNDC d p mprs
 = paren p precNDC
     $ ppsopen styleBlue " |~| "
     $ map (showp d precNDC . snd) mprs

simpNDC d mprs  = sLattice "|~|-simplify" mkNDC T F mprs

ndcEntry :: (Show s, Ord s) => (String, Entry m s)
ndcEntry = ("NDC", PredEntry $ PD ["P$"] PUndef ppNDC simpNDC)

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
isImp (_,Comp "Imp" _) = True  ;  isImp _ = False

mkImp mpr1 mpr2 = Comp "Imp" [mpr1,mpr2]

ppImp d p [mpr1,mpr2]
 = paren p precImp
     $ ppsopen styleBlue " => " [ showp d precImp $ snd mpr1
                                , showp d precImp $ snd mpr2 ]
ppImp d p mprs = pps styleRed $ ppa "invalid-=>"

simpImp d [ (_,T), (_,pr) ] = ( "=>-simp", pr        )
simpImp d [ (_,F), _      ] = ( "=>-simp", T         )
simpImp d [ mpr,  (_,F)   ] = ( "=>-simp", mkNot mpr )
simpImp d [ _,    (_,T)   ] = ( "=>-simp", T         )
simpImp d [ mpr1, mpr2    ] = ( "",  mkImp mpr1 mpr2 )

impEntry :: (Show s, Ord s) => (String, Entry m s)
impEntry = ("Imp", PredEntry $ PD ["P","Q"] PUndef ppImp simpImp)

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
isRfdby (_,Comp "Rfdby" _) = True  ;  isRfdby _ = False

mkRfdby mpr1 mpr2 = Comp "Rfdby" [mpr1,mpr2]

ppRfdby d p [mpr1,mpr2]
 = paren p precRfdby
     $ ppsopen styleBlue " |= " [ showp d precRfdby $ snd mpr1
                                , showp d precRfdby $ snd mpr2 ]
ppRfdby d p mprs = pps styleRed $ ppa "invalid-|="

simpRfdby d [mpr1, mpr2] = ( "",  mkImp mpr1 mpr2 )

rfdbyEntry :: (Show s, Ord s) => (String, Entry m s)
rfdbyEntry = ( "Rfdby"
             , PredEntry $ PD ["P","Q"] PUndef ppRfdby simpRfdby)

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
isCond (_,Comp "Cond" _) = True  ;  isCond _ = False

mkCond mpr1 mpr2 mpr3 = Comp "Cond" [mpr1,mpr2,mpr3]

ppCond d p [mprt,mprc,mpre]
 = paren p precCond 
      $ pplist [ showp d precCond $ snd mprt
               , pps styleBlue $ ppa " <| "
               , showp d 0 $ snd mprc
               , pps styleBlue $ ppa " |> "
               , showp d precCond $ snd mpre ]

ppCond d p mprs = pps styleRed $ ppa "invalid-<|>"

simpCond d [mpr1, mpr2] = ( "",  mkImp mpr1 mpr2 )

condEntry :: (Show s, Ord s) => (String, Entry m s)
condEntry = ( "Cond"
            , PredEntry $ PD ["P","c","R"] PUndef ppCond simpCond)

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
isSkip (_,Comp "Skip" _) = True  ;  isSkip _ = False

mkSkip = Comp "Skip" []

ppSkip d p _ = pps styleBlue $ ppa "II"

simpSkip d _ = ("",mkSkip)

skipEntry = ("Skip", PredEntry $ PD [] PUndef ppSkip simpSkip)

-- build Skip at the MPred level
bSkip = noMark mkSkip
\end{code}

\newpage
\HDRc{Sequencing}\label{hc:def-Seq}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mSeq & \tSeq
}
\begin{code}
isSeq (_,Comp "Seq" _) = True  ;  isSeq _ = False

mkSeq mpr1 mpr2 = Comp "Seq" [mpr1,mpr2]

ppSeq d p [mpr1,mpr2]
 = paren p precSeq
     $ ppsopen styleBlue " ; " [ showp d precSeq $ snd mpr1
                               , showp d precSeq $ snd mpr2 ]
ppSeq d p mprs = pps styleRed $ ppa "invalid-;"

simpSeq d [ mpr1, mpr2    ]
 | isSkip mpr1 = ( "simp-;",  snd mpr2 )
 | isSkip mpr2 = ( "simp-;",  snd mpr1 )
 | otherwise   = ( "", mkSeq mpr1 mpr2 )

seqEntry :: (Show s, Ord s) => (String, Entry m s)
seqEntry = ("Seq", PredEntry $ PD ["P","Q"] PUndef ppSeq simpSeq)

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
isIter (_,Comp "Iter" _) = True  ;  isIter _ = False

mkIter mpr1 mpr2 = Comp "Iter" [mpr1,mpr2]

ppIter d p [mpr1,mpr2]
 = paren p precIter
     $ ppsopen styleBlue " * " [ showp d precIter $ snd mpr1
                               , showp d precIter $ snd mpr2 ]
ppIter d p mprs = pps styleRed $ ppa "invalid-*"

simpIter d [mpr1, mpr2 ] = ( "", mkIter mpr1 mpr2 )

iterEntry :: (Show s, Ord s) => (String, Entry m s)
iterEntry = ( "Iter"
            , PredEntry $ PD ["c","Q"] PUndef ppIter simpIter )

-- build an Iter at the MPred level
bIter mpr1 mpr2 = noMark $ mkIter mpr1 mpr2
\end{code}

\newpage
\HDRb{The Standard Dictionary}\label{hb:std-dict}

\begin{code}
stdDict :: (Ord s, Show s) => Dict m s
stdDict
 = M.fromList
    [ topEntry
    , botEntry
    , notEntry
    , andEntry
    , orEntry
    , ndcEntry
    , impEntry
    , rfdbyEntry
    , condEntry
    , skipEntry
    , seqEntry
    , iterEntry
    ]
\end{code}

\HDRc{Debugging aids}

\begin{code}
putPred :: (Mark m, Ord s, Show s) => Pred m s -> IO ()
putPred = putStrLn . pdshow 80 stdDict
putMPred :: (Mark m, Ord s, Show s) => MPred m s -> IO ()
putMPred = putPred . snd
\end{code}
