\HDRa{UTP Semantics with Calculator}\label{ha:sem-with-calc}
\begin{code}
module SemanticCalc where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcPredicates
import CalcSteps
import UTCPSemantics
import UTCPLaws
import UTCPCReduce
import CalcRun
\end{code}

We now define useful bits:
The static dictionary, and some useful pre-defined variables
\begin{code}
true = B True
false = B False

c = Var "c"

-- arithmetic examples
(x,y,z) = (Var "x", Var "y", Var "z")
[add,sub,mul,dvd] = map (\ f -> App f [x,y]) ["+","-","*","/"]
subs1 = [("x",y),("y",x)]
subs2 = [("x",mul),("y",dvd),("z",add)]

a = PVar "A"; aa = PAtm a
b = PVar "B"; ab = PAtm b
cp = Atm c
athenb = PSeq aa ab; awithb = PPar aa ab
acondb = PCond cp aa ab
doa = PIter cp aa
p = PVar "P" ; q = PVar "Q" ; r=PVar "R"
pthenq = PSeq p q
pwithq = PPar p q
pcondq = PCond cp p q
dop = PIter cp p

catalog = putStr $ unlines (map catshow
 [
   ("a",a)  -- PVar "A";
 , ("aa",aa)  -- PAtm a
 , ("b",b)  -- PVar "B";
 , ("ab",ab)  -- PAtm b
 , ("cp",cp)  -- Atm c
 , ("athenb",athenb)  -- PSeq aa ab;
 , ("awithb",awithb)  -- PPar aa ab
 , ("acondb",acondb)  -- PCond cp aa ab
 , ("doa",doa)  -- PIter cp aa
 , ("p",p)  -- PVar "P"
 , ("q",q)  -- PVar "Q"
 , ("r",r)  -- PVar "R"
 , ("pthenq",pthenq)  -- PSeq p q
 , ("pwithq",pwithq)  -- PPar p q
 , ("pcondq",pcondq)  -- PCond cp p q
 , ("dop",dop)  -- PIter cp p
 ] ++ usage)

catshow ::(String, Pred ()) -> String
catshow (name,pr) = name ++ " ... " ++ showUTCP pr
xx = PVar "??"

usage
 = [ "'run' and 'doprog' wrap predicates in the top-level execution loop"
   , "To calulate the 'run' execution of 'athenb' (say),"
   , "                           use 'calculemus $ run athenb'"
   ]
\end{code}

Now some sample expanded definitions:
\begin{code}
par,big :: Ord s => Pred s
par = defnPar Skip Skip
big = defnPar (defnSeq Skip defnII) (defnSeq defnII Skip)
\end{code}


\HDRb{The UTCP Theory}
Our theory:
\begin{code}
dictUTCP :: (Eq s, Ord s, Show s) => Dict s
dictUTCP
 = foldl1 M.union [ M.fromList [(version,AlfEntry [versionUTCP])]
                  , alfDict, setDict, genDict ]

showUTCP pr  = pdshow dictUTCP pr

stepsUTCP :: (Ord s, Show s) => ThSteps s
stepsUTCP = TS reduceUTCP defnUTCP creduceUTCP

calculemus :: (Ord s, Show s)
           => Pred s -> IO ( Pred s, [CalcResult s], Dict s )
calculemus pr = calcREPL stepsUTCP dictUTCP pr
\end{code}
