\HDRa{Calculator Tests}\label{ha:calc-test}
\begin{code}
module CalcTest where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
import StdPredicates
import CalcZipper
import CalcSteps
\end{code}

\HDRc{Default Mark Type}

We will generally use non-negative \emph{Int} as markers,
with $-1$ representing ``no mark'',
and incrementing being used to generate new marks.
\begin{code}
instance Mark Int where
  startm = 0
  nextm = (+1)
\end{code}

Some concrete instances
\begin{code}
type IPred s = MPred Int s
iT, iF :: IPred s
iT = bT
iF = bF
iPV :: String -> IPred s
iPV = bPV
iEqual :: Expr s -> Expr s -> IPred s
iEqual = bEqual
iAtm :: Expr s -> IPred s
iAtm = bAtm
iComp :: String -> [IPred s] -> IPred s
iComp = bComp
iPSub :: Ord s => IPred s -> Substn s -> IPred s
iPSub = bPSub
\end{code}
