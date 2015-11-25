\HDRa{Calculator Zipper}\label{ha:calc-zipper}
\begin{code}
module CalcZipper where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcPredicates
\end{code}


\HDRb{Zipper Setup}

\begin{code}
startMPZ :: MPred m s -> MPZipper m s
startMPZ mp = ( mp, [] )
\end{code}

\HDRb{Going Deeper}

We go down by specifying which sub-component, if necessary,
with components numbered from 0 upwards
\begin{code}
downMPZ :: Int -> MPZipper m s -> MPZipper m s
downMPZ _ ( (m, PSub mpr subs), ss ) = ( mpr, PSub' m subs : ss )
downMPZ i ( (m, Comp name mprs), ss )
 | 0 <= i && i < length mprs
   = (  mpri, Comp' m name before after : ss )
   where ( before, (mpri:after) ) = splitAt i mprs
downMPZ _ mpz = mpz -- default case, do nothing
\end{code}

\HDRb{Coming Back Up}

We can plug an \texttt{MPred} into a\texttt{ MPred'} to get an \texttt{MPred},
effectively moving up one level
\begin{code}
plugMPZ :: MPred' m s -> MPred m s -> MPred m s
plugMPZ (Comp' m name before after) mpr
                            =  (m, Comp name (before++mpr:after))
plugMPZ (PSub' m subs) mpr  =  (m, PSub mpr subs)
\end{code}

We then lift this to work with a zipper
where the top-most (inner-most) step is first
\begin{code}
upMPZ :: MPZipper m s -> MPZipper m s
upMPZ ( mpr, (s:ss) ) = ( plugMPZ s mpr, ss )
upMPZ mpz = mpz -- taken if currently at top
\end{code}

\HDRb{Modifying the Focus}

\begin{code}
updateMPZ :: (MPred m s -> MPred m s) -> MPZipper m s -> MPZipper m s
updateMPZ f ( mpr, ss ) = ( f mpr, ss )
\end{code}

\HDRb{Exiting the Zipper}

We can unzip by repeatedly plugging in:
\begin{code}
unzipMPZ :: [MPred' m s] -> MPred m s -> MPred m s
unzipMPZ [] mpr = mpr
unzipMPZ (s:ss) mpr = unzipMPZ ss $ plugMPZ s mpr
\end{code}

We exit by unzipping as above:
\begin{code}
exitMPZ :: MPZipper m s -> MPred m s
exitMPZ ( mpr, ss ) = unzipMPZ ss mpr
\end{code}
