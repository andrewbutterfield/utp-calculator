\HDRa{Standard Predicates}\label{ha:std-preds}
\begin{code}
module StdPredicates where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Debug.Trace
import PrettyPrint
import StdPrecedences
import CalcPredicates
\end{code}

\HDRb{Standard Definitions}\label{hb:std-defs}

Here we provide dictionary entries for all our ``standard''
UTP predicate forms.

First, some generic intelligent composite constructors:
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
ppNot d p _ = ppa "invalid-Not"

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

simpOr d mprs  = sLattice "\\/-simplify" mkOr F T mprs

orEntry :: (Show s, Ord s) => (String, Entry m s)
orEntry = ("Or", PredEntry $ PD ["P$"] PUndef ppOr simpOr)

-- build an Or at the MPred level
bOr mprs = noMark $ mkOr mprs
\end{code}

\newpage
\HDRb{The Standard Dictionary}\label{hb:std-dict}

\begin{code}
stdDict :: (Ord s, Show s) => Dict m s
stdDict
 = M.fromList
    [ notEntry
    , andEntry
    , orEntry
    ]
\end{code}

\HDRc{Debugging aids}

\begin{code}
putPred :: (Ord s, Show s) => Pred m s -> IO ()
putPred = putStrLn . pdshow 80 stdDict
\end{code}
