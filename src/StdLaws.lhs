\HDRa{Standard Laws}\label{ha:std-laws}
\begin{code}
module StdLaws where
import Utilities
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcPredicates
import CalcAlphabets
import CalcSimplify
import CalcRecogniser
import StdPredicates
\end{code}

We don't have a lot of laws here we want to invoked directly,
beng too low-level for effective use of the calculator.
We just give a dictionary here for the standard composites.

\HDRb{The Standard Dictionary}\label{hb:std-dict}

\begin{code}
stdDict :: (Ord s, Show s) => Dict s
stdDict
 = makeDict
    [ notEntry
    , andEntry
    , orEntry
    , impEntry
    , eqvEntry
    ]
\end{code}
