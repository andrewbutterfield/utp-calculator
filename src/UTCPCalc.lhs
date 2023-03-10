\HDRa{UTCP Semantics with Calculator}\label{ha:UTCPsem-with-calc}
\begin{code}
module UTCPCalc where
import Utilities
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import CalcPPrint
import CalcTypes
import CalcSysTypes
import CalcPredicates
import CalcSteps
import StdPredicates
import StdLaws
import StdUTPPredicates
import StdUTPLaws
import UTCPLaws
import UTCPCReduce
import UTCPSemantics
import CalcRun
\end{code}

We now define useful bits:
The static dictionary, and some useful pre-defined variables
\begin{code}
a = PVar "A"; aa = patm a
b = PVar "B"; ab = patm b
c = Var  "c"; cp = Atm  c
athenb = pseq [aa,ab]
awithb = ppar [aa,ab]
acondb = pcond [cp,aa,ab]
doa = piter [cp,aa]

p = PVar "P" ; q = PVar "Q" ; r=PVar "R"
pthenq = pseq [p,q]
pwithq = ppar [p,q]
pcondq = pcond [cp,p,q]
dop = piter [cp,p]
\end{code}


\HDRb{The UTCP Theory}
Our theory:
\begin{code}
dictUTCP :: Dict
dictUTCP
 = foldl1 dictMrg [ makeDict [(version,AlfEntry [versionUTCP])]
                  , stdDict
                  , stdUTPDict
                  , alfUTCPDict
                  , setUTCPDict
                  , genUTCPDict
                  , semUTCPDict
                  , lawsUTCPDict
                  ]

showUTCP pr = plainShow 80 dictUTCP pr

calc :: Pred -> IO CalcLog
calc = calcREPL dictUTCP [] -- . buildMarks
\end{code}
