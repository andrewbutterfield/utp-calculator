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
import CalcTypes
import CalcPredicates
import CalcSteps
import CalcSimplify
\end{code}


\newpage
\HDRb{Calculator REPL}

For now we define a simple REPL.
First, some top-level setup:
\begin{code}
calcREPL :: (Mark m, Ord s, Show s)
         => Dict m s ->  MPred m s
         -> IO ( MPred m s, [CalcResult m s], Dict m s )
calcREPL d mpr
 = do putStrLn ""
      putStrLn $ versionShow d'
      runREPL d' startm (mpr,[]) mpr
 where d' = M.unionWith mergeEntry d dictVersion

dictVersion
  = M.fromList [( version
                , AlfEntry [ "0.0.1"
                           ]
               )]

version = "version"

versionShow d
 = case alookup version d of
    Just (AlfEntry vs)
            -> "UTP-Calc v" ++ (concat $ intersperse ", " vs)
    Nothing -> ""
\end{code}

Now, the main REPL loop:
\begin{code}
runREPL :: (Mark m, Ord s, Show s) 
        => Dict m s -> m -> (MPred m s, [CalcResult m s])
        -> MPred m s
        -> IO ( MPred m s, [CalcResult m s], Dict m s )
runREPL d m (mpr0,steps) currpr
 = do
  putStr ( "\n"
         ++ pdshow 80 d (snd currpr)
         ++ "\n\n ?,d,r,l,s,c,u,x :- " )
  ln <- getLine
  case ln of
   ('?':_) -> calcHelp d m (mpr0,steps) currpr
   ('s':_) -> calcStep d m (simplify d m) (mpr0,steps) currpr
   ('u':_) -> calcUndo d m (mpr0,steps) currpr
--    ('d':_) -> calcStep th d (defn th) (mpr0,steps) currpr
--    ('r':_) -> calcStep th d (reduce th $ d) (mpr0,steps) currpr
--    -- ('l':_) -> calcStep th d unroll (mpr0,steps) currpr
--    ('c':_) -> calcCStep th d (creduce th $ d) (mpr0,steps) currpr
   ('x':_) -> return (mpr0,steps, d)
   _ -> do putStrLn ("'"++ln++"' ??")
           runREPL d m (mpr0,steps) currpr
\end{code}

Undoing
\begin{code}
calcUndo d m st@(mpr0,[]) currpr = runREPL d m st currpr
calcUndo d m (mpr0,[(_,_)])    _ = runREPL d (prevm m) (mpr0,[]) mpr0
calcUndo d m (p,(_:steps@((_,q):_))) _ = runREPL d (prevm m) (p,steps) q
\end{code}

Help
\begin{code}
calcHelp d m st currpr
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
      runREPL d m st currpr
\end{code}

\newpage
Applying a given kind of step:
\begin{code}
calcStep :: (Mark m, Ord s, Show s)
         => Dict m s -> m -> CalcStep m s
         -> (MPred m s, [CalcResult m s]) -> MPred m s
         -> IO ( MPred m s, [CalcResult m s], Dict m s )
calcStep d m stepf st@(mpr0,steps) currpr
 = do case stepf currpr of
       ( "", _ )  ->  runREPL d m st currpr
       step'@( comment, mpr' )
         -> do  putStrLn ( "\n = " ++ show comment )
                runREPL d (nextm m) (mpr0,(step':steps)) mpr'
\end{code}

Apply a given conditional step:
\begin{code}
-- calcCStep d cstepf st@(mpr0,steps) currpr
--  = case capply cstepf currpr of
--      ( "", _ )  ->  runREPL d st currpr
--      cstep'@( comment, crps' )
--        ->  do putStrLn $ unlines $ ccshow d $ zip [1..] crps'
--               let num = length crps'
--               putStrLn ("Please select 1.."++show num)
--               sel <- fmap getInt getLine
--               if 1 <= sel && sel <= num
--                then do let step' = condResolve d sel cstep'
--                        putStrLn ( "\n = " ++ show comment )
--                        runREPL d (mpr0,(step':steps)) (snd step')
--                else runREPL d st currpr
--  where
--    getInt (c:_)
--     | isDigit c = digitToInt c
--    getInt _ = 0
--
-- ccshow d [] = []
-- ccshow d ((i,(cpr,rpr)):rest)
--  = ["","(" ++ show i++ ") provided:    " ++ pdshow d cpr
--    ,"--"
--    ,pdshow d rpr]
--    ++ ccshow d rest
\end{code}

\newpage
\HDRb{Displaying Calculations}

Now, rendering the results to look pretty:
\begin{code}
calcPrint :: (Ord s, Show s)
          => ( MPred m s, [CalcResult m s], Dict m s ) -> String
calcPrint ( pr0, steps, d )
 = unlines ( "" : versionShow d : "" : pdshow 80 d ( snd pr0)
             : (concat $ map (stepPrint d) $ reverse steps))

stepPrint :: (Ord s, Show s) => Dict m s -> CalcResult m s -> [String]
stepPrint d (comment,pr)
 = [""," = " ++ show comment,""] ++ [pdshow 80 d $ snd pr]

outcome :: ( MPred m s, [CalcResult m s] ) -> MPred m s
outcome ( pr0, [] ) = pr0
outcome ( _, ((_,pr'):_)) = pr'
\end{code}


\newpage
Now, doing it conditionally%
\footnote{
  It should be possible to implement both \texttt{apply} and \texttt{capply}
  as a single traverse function with appropriate higher
  function parameters, but right now my head hurts!
}
\begin{code}
-- capply :: Ord s => CCalcStep s -> Pred s -> CCalcResult s
-- capply cstep pr
--  = case cstep pr of
--      ( "", _ ) ->  crapply cstep pr
--      res       ->  res
--
-- crapply :: Ord s => CCalcStep s -> Pred s -> CCalcResult s
-- crapply cstep (Not p) = cmapplies lnot cstep [p]
-- crapply cstep (And prs) = cmapplies And cstep prs
-- crapply cstep (Or prs) = cmapplies Or cstep prs
-- crapply cstep (Imp p1 p2) = cmapplies imp cstep [p1,p2]
-- crapply cstep (Cond p1 p2 p3) = cmapplies cond cstep [p1,p2,p3]
-- crapply cstep (PSub p sub) = cmapplies (psub sub) cstep [p]
-- crapply cstep (Seq p1 p2) = cmapplies seqs cstep [p1,p2]
-- crapply cstep (Iter p1 p2) = cmapplies iter cstep [p1,p2]
-- crapply cstep (PFun f prs) = cmapplies (PFun f) cstep prs
-- crapply cstep (PAtm p) = cmapplies patm cstep [p]
-- crapply cstep (PSeq p1 p2) = cmapplies pseq cstep [p1,p2]
-- crapply cstep (PPar p1 p2) = cmapplies ppar cstep [p1,p2]
-- crapply cstep (PCond p1 p2 p3) = cmapplies pcond cstep [p1,p2,p3]
-- crapply cstep (PIter p1 p2) = cmapplies piter cstep [p1,p2]
-- crapply cstep p = ( "", [] )
--
-- cmapplies :: Ord s
--           => ([Pred s] -> Pred s) -> CCalcStep s -> [Pred s]
--           -> CCalcResult s
-- cmapplies cons cstep prs
--  = ( comment, mapsnd cons crps )
--  where ( comment, crps ) = crapplies cstep prs
--
-- crapplies :: Ord s => CCalcStep s -> [Pred s]
--                    -> ( String, [(Pred s,[Pred s])] )
-- crapplies _ [] = ( "", [] )
-- crapplies cstep [pr]
--  = ( comment, mapsnd (:[]) crps' )
--  where ( comment, crps' ) = capply cstep pr
-- crapplies cstep (pr:prs)
--  = case capply cstep pr of
--      (  "", _ )
--        -> ( comment, mapsnd (pr:) crps' )
--           where ( comment, crps' ) = crapplies cstep prs
--      ( comment, crps' )
--        -> ( comment, mapsnd (:prs) crps' )
\end{code}
