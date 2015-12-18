\HDRa{Standard Laws}\label{ha:std-laws}
\begin{code}
module StdLaws where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcPredicates
import CalcRecogniser
import StdPredicates
\end{code}


\begin{code}
unroll :: (Mark m, Ord s) => RWFun m s
unroll mw@(_,Comp "Iter"  [mc@(_,c), mpr])
 | isCondition c
           = lred "loop-unroll" $ bCond mc (bSeq mpr mw) bSkip
unroll mpr = lred "" mpr

lred nm mpr = ( nm, mpr )
\end{code}
