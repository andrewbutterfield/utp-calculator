\HDRa{Running the Calculator}\label{ha:calc-run}
\begin{code}
module CalcRun where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcPredicates
import CalcSteps
\end{code}

Version
\begin{code}
version = "version"
versionCalcRun = "CR-0.6"
\end{code}


\newpage
\HDRb{Calculator REPL}

For now we define a simple REPL.
First, some top-level setup:
\begin{code}
calcREPL :: (Ord s, Show s)
         => ThSteps s -> Dict s ->  Pred s
         -> IO ( Pred s, [CalcResult s], Dict s )
calcREPL th d pr
 = do putStrLn ""
      putStrLn $ versionShow d'
      runREPL th d' (pr,[]) pr
 where d' = M.unionWith mergeEntry d dictVersion

dictVersion
  = M.fromList [( version
                , AlfEntry [ versionPrettyPrint
                           , versionCalcPredicates
                           , versionCalcSteps
                           , versionCalcRun
                           ]
               )]
\end{code}

Now, the main REPL loop:
\begin{code}
runREPL th d (pr0,steps) currpr
 = do
 putStr ( "\n"
        ++ pdshow d currpr
        ++ "\n\n ?,d,r,l,s,c,u,x :- " )
 ln <- getLine
 case ln of
   ('x':_) -> return (pr0,steps, d)
   ('u':_) -> calcUndo th d (pr0,steps) currpr
   ('d':_) -> calcStep th d (defn th) (pr0,steps) currpr
   ('r':_) -> calcStep th d (reduce th $ d) (pr0,steps) currpr
   ('l':_) -> calcStep th d unroll (pr0,steps) currpr
   ('s':_) -> calcStep th d (simplify d) (pr0,steps) currpr
   ('c':_) -> calcCStep th d (creduce th $ d) (pr0,steps) currpr
   ('?':_) -> calcHelp th d (pr0,steps) currpr
   _       -> runREPL th d (pr0,steps) currpr
\end{code}

Undoing
\begin{code}
calcUndo th d st@(pr0,[]) currpr = runREPL th d st currpr
calcUndo th d (pr0,[(_,_)])    _ = runREPL th d (pr0,[]) pr0
calcUndo
 th d (p,(_:steps@((_,q):_)))  _ = runREPL th d (p,steps) q
\end{code}

Help
\begin{code}
calcHelp th d st currpr
 = do putStr $ unlines
       [ ""
       , "? - this help message"
       , "s - simplify everywhere"
       , "x - exit, returning proof script"
       , "u - undo"
       , "most subsequent commands affect the first applicable location"
       , "d - definition expansion"
       , "r - reduction law application"
       , "l - loop unrolling"
       , "c - conditional reduction step"
       ]
      runREPL th d st currpr
\end{code}

\newpage
Applying a given kind of step:
\begin{code}
calcStep th d stepf st@(pr0,steps) currpr
 = do case apply stepf currpr of
       ( "", _ )  ->  runREPL th d st currpr
       step'@( comment, pr' )
         -> do  putStrLn ( "\n = " ++ show comment )
                runREPL th d (pr0,(step':steps)) pr'
\end{code}

Apply a given conditional step:
\begin{code}
calcCStep th d cstepf st@(pr0,steps) currpr
 = case capply cstepf currpr of
     ( "", _ )  ->  runREPL th d st currpr
     cstep'@( comment, crps' )
       ->  do putStrLn $ unlines $ ccshow d $ zip [1..] crps'
              let num = length crps'
              putStrLn ("Please select 1.."++show num)
              sel <- fmap getInt getLine
              if 1 <= sel && sel <= num
               then do let step' = condResolve d sel cstep'
                       putStrLn ( "\n = " ++ show comment )
                       runREPL th d (pr0,(step':steps)) (snd step')
               else runREPL th d st currpr
 where
   getInt (c:_)
    | isDigit c = digitToInt c
   getInt _ = 0

ccshow d [] = []
ccshow d ((i,(cpr,rpr)):rest)
 = ["","(" ++ show i++ ") provided:    " ++ pdshow d cpr
   ,"--"
   ,pdshow d rpr]
   ++ ccshow d rest
\end{code}

\newpage
\HDRb{Displaying Calculations}

Now, rendering the results to look pretty:
\begin{code}
calcPrint :: (Ord s, Show s)
          => ( Pred s, [CalcResult s], Dict s ) -> String
calcPrint ( pr0, steps, d )
 = unlines ( "" : versionShow d : "" : pdshow d pr0
             : (concat $ map (stepPrint d) $ reverse steps))

versionShow d
 = case alookup version d of
    Nothing -> ""
    Just vs -> concat $ intersperse ", " vs

stepPrint :: (Ord s, Show s) => Dict s -> CalcResult s -> [String]
stepPrint d (comment,pr)
 = [""," = " ++ show comment,""] ++ [pdshow d pr]

outcome :: ( Pred s, [CalcResult s] ) -> Pred s
outcome ( pr0, [] ) = pr0
outcome ( _, ((_,pr'):_)) = pr'
\end{code}
