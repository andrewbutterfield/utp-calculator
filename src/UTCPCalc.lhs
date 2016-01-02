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

catalog = putStr $ unlines (map catshow
 [
   ("a",a)  -- pvar "A";
 , ("aa",aa)  -- patm a
 , ("b",b)  -- pvar "B";
 , ("ab",ab)  -- patm b
 , ("cp",cp)  -- atm c
 , ("athenb",athenb)  -- pseq aa ab;
 , ("awithb",awithb)  -- ppar aa ab
 , ("acondb",acondb)  -- pcond cp aa ab
 , ("doa",doa)  -- piter cp aa
 , ("p",p)  -- pvar "P"
 , ("q",q)  -- pvar "Q"
 , ("r",r)  -- pvar "R"
 , ("pthenq",pthenq)  -- pseq p q
 , ("pwithq",pwithq)  -- ppar p q
 , ("pcondq",pcondq)  -- pcond cp p q
 , ("dop",dop)  -- piter cp p
 ] ++ usage)

catshow :: (String, MPred Int ()) -> String
catshow (name,mpr) = name ++ " ... " ++ showUTCP mpr
xx = pvar "??"

usage
 = [ "'run' and 'doprog' wrap predicates in the top-level execution loop"
   , "To calulate the 'run' execution of 'athenb' (say),"
   , "                           use 'calculemus $ run athenb'"
   ]
\end{code}


\HDRb{The UTCP Theory}
Our theory:
\begin{code}
dictUTCP :: (Eq s, Ord s, Show s) => Dict m s
dictUTCP
 = foldl1 dictMrg [ M.fromList [(version,AlfEntry [versionUTCP])]
                  , alfDict, setDict, genDict ]

showUTCP (_,pr)  = pdshow 80 dictUTCP pr
\end{code}
