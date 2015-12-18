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
calcREPL :: (Mark m, Show m, Ord s, Show s)
         => Dict m s ->  MPred m s
         -> IO ( MPred m s, [RWResult m s], Dict m s )
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
runREPL :: (Mark m, Show m, Ord s, Show s)
        => Dict m s -> m -> (MPred m s, [RWResult m s])
        -> MPred m s
        -> IO ( MPred m s, [RWResult m s], Dict m s )
runREPL d m state@(mpr0,steps) currpr
 = do
  putStr ( "\n"
         ++ pmdshow 80 d noStyles currpr
         ++ "\n\n ?,d,r,l,s,c,u,x :- " )
  ln <- getLine
  case ln of
   ('?':_) -> calcHelp d m state currpr
   ('s':_) -> calcStep d m (simplify d $ nextm m) state currpr
   ('u':_) -> calcUndo d m state currpr
   ('d':_) -> calcStep d m (expandDefn d $ nextm m) state currpr
--    ('r':_) -> calcStep  d m (reduce th $ d) state currpr
--    -- ('l':_) -> calcStep  d m unroll state currpr
--    ('c':_) -> calcCStep  d m (creduce th $ d) state currpr
   ('x':_) -> return (mpr0,steps,d)
   ('M':_) -> showMarks d m state currpr
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
       , "M - show marks (DEBUG)"
       ]
      runREPL d m st currpr
\end{code}

\newpage
Applying a given kind of step:
\begin{code}
calcStep :: (Mark m, Show m, Ord s, Show s)
         => Dict m s -> m -> (MPred m s -> BeforeAfter m s)
         -> (MPred m s, [RWResult m s]) -> MPred m s
         -> IO ( MPred m s, [RWResult m s], Dict m s )
calcStep d m stepf st@(mpr0,steps) currpr
 = do case stepf currpr of
       ( _, "", _ )  ->  runREPL d m st currpr
       ( before,comment, after )
         -> do  putStrLn ( "\n = " ++ show comment )
                let st' = stUpdate before (comment,after) st
                runREPL d (nextm m) st' after
 where
   stUpdate before wafter ( mpr0, []) = ( before, [wafter] )
   stUpdate before wafter ( mpr0, ((what,_):steps))
    = ( mpr0, (wafter:(what,before):steps) )
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

Showing Marks
\begin{code}
showMarks :: (Mark m, Show m, Ord s, Show s)
          => Dict m s -> m
          -> (MPred m s, [RWResult m s]) -> MPred m s
          -> IO ( MPred m s, [RWResult m s], Dict m s )
showMarks d m state@(mpr0,steps) currpr
 = do showm (0::Int) (mpr0:map snd steps)
      runREPL d m state currpr
 where
   showm _ [] = return ()
   showm i (mpr:mprs)
    = do putStrLn (show i ++ " ! " ++ show (marksOf mpr))
         showm (i+1) mprs
   marksOf  ( ms, pr ) = ms ++ predMarks pr
   predMarks (Comp _ mprs) = concat $ map marksOf mprs
   predMarks (PSub mpr _) = marksOf mpr
   predMarks _ = []
\end{code}

\newpage
\HDRb{Displaying Calculations}

First,
a mark-style function:
\begin{code}
stepshow :: (Mark m, Eq m) => m -> MarkStyle m
stepshow n m
 | n == prevm m         =  Just styleOld
 | n == m          =  Just styleNew
 | otherwise      =  Nothing
 where
   styleOld = Underline
   styleNew = styleRed
\end{code}

Now, rendering the results to look pretty:
\begin{code}
calcPrint :: (Mark m, Eq m, Ord s, Show s)
          => ( MPred m s, [RWResult m s], Dict m s ) -> String
calcPrint ( mpr0, steps, d )
 = unlines ( "" : versionShow d : "" : pmdshow 80 d (stepshow startm) mpr0
             : (stepPrint d (nextm startm) $ reverse steps))

stepPrint :: (Mark m, Eq m, Ord s, Show s)
           => Dict m s -> m -> [RWResult m s] -> [String]
stepPrint d m [] = []
stepPrint d m ((comment,mpr):rest)
 = [""," = " ++ show comment,""] ++ [pmdshow 80 d (stepshow m) mpr]
   ++ stepPrint d (nextm m) rest


outcome :: ( MPred m s, [RWResult m s] ) -> MPred m s
outcome ( mpr0, [] ) = mpr0
outcome ( _, ((_,mpr'):_)) = mpr'
\end{code}


\newpage
Now, doing it conditionally%
\footnote{
  It should be possible to implement both \texttt{apply} and \texttt{capply}
  as a single traverse function with appropriate higher
  function parameters, but right now my head hurts!
}
\begin{code}
-- capply :: Ord s => CRWFun s -> Pred s -> CRWResult s
-- capply cstep pr
--  = case cstep pr of
--      ( "", _ ) ->  crapply cstep pr
--      res       ->  res
--
-- crapply :: Ord s => CRWFun s -> Pred s -> CRWResult s
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
--           => ([Pred s] -> Pred s) -> CRWFun s -> [Pred s]
--           -> CRWResult s
-- cmapplies cons cstep prs
--  = ( comment, mapsnd cons crps )
--  where ( comment, crps ) = crapplies cstep prs
--
-- crapplies :: Ord s => CRWFun s -> [Pred s]
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
