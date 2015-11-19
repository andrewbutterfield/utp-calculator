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
-- here we code the dictionary entry for "Not"
\end{code}


\HDRb{The Standard Dictionary}

\begin{code}
stdDict = M.empty
\end{code}

\HDRc{Debugging aids}

\begin{code}
putPred :: (Ord s, Show s) => Pred m s -> IO ()
putPred = putStrLn . pdshow 80 stdDict
\end{code}