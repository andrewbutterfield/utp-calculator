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
\end{code}

\HDRc{Default Mark Type}

We will generally use non-negative \emph{Int} as markers,
with $-1$ representing ``no mark'',
and incrementing being used to generate new marks.
\begin{code}
instance Mark Int where
  nomark = -1
  nextm = (+1)
\end{code}

\begin{code}
-- vacuous mark instance
instance Mark () where { nomark=(); nextm=id }

iT, iF :: MPred Int s
iT = bT
iF = bF
\end{code}
