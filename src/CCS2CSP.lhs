\HDRa{CCS to CSP}\label{ha:CCs2CSP}
\begin{code}
module CCS2CSP where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import NiceSymbols
import CalcPPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
import DictAbstractions
import CalcAlphabets
import CalcSysTypes
import CalcSimplify
import CalcRecogniser
import CalcRun
import StdSets
import StdExpressions
import StdPredicates
\end{code}

\begin{code}
-- import Debug.Trace
-- dbg str x = trace (str++show x) x
\end{code}

\HDRb{Introduction}

We rapid prototype emerging work
looking at the relationship between CCS and CSP style process algebras.

\begin{code}
c2cVersion = "0.1"
\end{code}




For now we want to be able to compute $g^*(P)$ for CCS process $P$,
from the work being done by Gerard Nkembe Ogondi.

Working off \verb"CCS-Pi-extensions_v12.pdf", of July 2nd 2020.

\HDRc{Notation}

First, some notation from that work

\[
  a.0 | \bar a . 0 \quad = \quad a.\bar a.0 + \bar a . a . 0 + \tau[a].0
\]

\[
 ( (a_1 + a_{12} + a_{13} + a_{14}).0
 | (a_2 + \bar a_{12}).0
 | (a_3 + \bar a_{13}).0
 | (a_4 + \bar a_{14}).0
 )
 \upharpoonright
 \{ a_{ij} | 1 \leq i < j \leq 4 \}
\]

\[
  g^*(b.a.0 | a.\bar b.0)
  \quad=\quad
  ( (b_1 + b_{12}).a_1.0
  | a_2.(\bar b_{2} + \bar b_{12}).0
  )
  \upharpoonright
  \{ b_{12} \}
\]

So we need some CCS syntax, and events with bars and indices,
as well as functions on CCS syntax.

\HDRc{Definition of $g^*$ (and friends)}

We start with a version of $g^*$ applied to alphabets (Defn 4.2, p17).

We then see a definition of a function called $c2star$ on CCS processes
(Defn 4.3, p18).
Basically it replaces parallel composition $|$ by a starred version ($|^*$).

We then see a definition of $g^{*n}$ for alphabets (Defn 4.4, p18).

Then a definition of $g^*$ applied to processes is defined (Defn 4.5, p19).

As far as we can see, Defn 4.4 and 4.5 are what we need,
with Defn 4.2 modified to add zero superscripts,
as described just before Defn 4.4.

\textbf{Alert:} Line 5 of Defn 4.5 (dropping alphabet notation):

\[
g^*(g^*(P_1)|P_2) = g^{**}(P_1) | g^*(P_2)
\]
This is problematic
--- it is fine as a statement of a law regarding $g^*$ and $g^{**}$
-- you cannot use it to define $g^*$ because pattern-matching on the
application of a function to argument is not possible in general.
We can ``fake it'',
by having an explicit function application construct in our
syntax, with a lazy semantics,
and also have to treat function names as meaningful.

This needs to be re-designed.
Function $g^*$ needs to have a level parameter,
and a way to increment indices.
Ideally we should be able to construct the indices from the bottom-up.




\HDRb{CCS2CSP Dictionary}
\begin{code}
c2cDict :: Dict
c2cDict
 = mergeDicts
    [ dictVersion ("CCS2CSP "++c2cVersion)

    -- stuff
    -- , xxxEntry

    , stdExprDict
    , stdSetDict
    , stdPredDict
    ]
\end{code}



\HDRb{Top Level Support}

\begin{code}
c2cshow :: Pred -> String
c2cshow = pdshow 80 c2cDict noStyles

c2cput :: Pred -> IO ()
c2cput = putStrLn . c2cshow

c2ceput :: Expr -> IO ()
c2ceput = c2cput . Atm

c2ccalc pr = calcREPL c2cDict [] pr

c2clog = putStrLn . calcPrint

c2ccalcput pr = (c2ccalc pr) >>= c2clog
\end{code}
