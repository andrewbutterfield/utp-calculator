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


\HDRb{Negation}

\RLEQNS{
  p \in Pred &::=& \ldots
\\ &|& \mNot & \tNot
}
\begin{code}
mkNot mpr = Comp "Not" [mpr]

ppNot d p [(m,pr)] -- ignore marking for now
 = paren p precNot $ pplist [ppa "~", showp d precNot pr]
showNot d p _ = ppa "invalid-Not"

simpNot d [(m,T)] = ("~-simp",F)
simpNot d [(m,F)] = ("~-simp",T)
simpNot _ mprs = ("", Comp "Not" mprs)

notEntry :: (Show s, Ord s) => (String, Entry m s)
notEntry = ("Not", PredEntry $ PD ["P"] PUndef ppNot simpNot)
\end{code}


\HDRb{The Standard Dictionary}

\begin{code}
stdDict :: (Ord s, Show s) => Dict m s
stdDict
 = M.fromList
    [ notEntry
    ]
\end{code}

\HDRc{Debugging aids}

\begin{code}
putPred :: (Ord s, Show s) => Pred m s -> IO ()
putPred = putStrLn . pdshow 80 stdDict
\end{code}
