\HDRa{UTCP Semantics with Calculator}\label{ha:UTCPsem-with-calc}
\begin{code}
module UTCPCalc where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcPredicates
import CalcSteps
import StdPredicates
import UTCPSemantics
import UTCPLaws
import UTCPCReduce
import CalcRun
\end{code}

We now define useful bits:
The static dictionary, and some useful pre-defined variables
\begin{code}

-- arithmetic examples
-- (x,y,z) = (Var "x", Var "y", Var "z")
-- [add,sub,mul,dvd] = map (\ f -> App f [x,y]) ["+","-","*","/"]
-- subs1 = [("x",y),("y",x)]
-- subs2 = [("x",mul),("y",dvd),("z",add)]

a = pvar "A"; aa = patm a
b = pvar "B"; ab = patm b
c = Var  "c"; cp = atm  c
athenb = pseq [aa,ab]
awithb = ppar [aa,ab]
acondb = pcond [cp,aa,ab]
doa = piter [cp,aa]

p = pvar "P" ; q = pvar "Q" ; r=pvar "R"
pthenq = pseq [p,q]
pwithq = ppar [p,q]
pcondq = pcond [cp,p,q]
dop = piter [cp,p]
\end{code}


\HDRb{The UTCP Theory}
Our theory:
\begin{code}
dictUTCP :: (Eq m, Eq s, Ord s, Show s) => Dict m s
dictUTCP
 = foldl1 dictMrg [ M.fromList [(version,AlfEntry [versionUTCP])]
                  , alfUTCPDict
                  , setUTCPDict
                  , genUTCPDict
                  , semUTCPDict
                  ]

showUTCP (_,pr)  = pdshow 80 dictUTCP pr
\end{code}
