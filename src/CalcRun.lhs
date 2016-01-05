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
calcREPL :: (Ord s, Show s)
         => Dict s ->  MPred s
         -> IO ( MPred s, [RWResult s], Dict s )
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
runREPL :: (Ord s, Show s)
        => Dict s -> Mark -> (MPred s, [RWResult s])
        -> MPred s
        -> IO ( MPred s, [RWResult s], Dict s )
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
   ('r':_) -> calcStep d m (doReduce   d $ nextm m) state currpr
   ('c':_) -> calcCStep d m (doCReduce d $ nextm m) state currpr
   ('l':_) -> calcStep  d m (doUnroll d $ nextm m) state currpr
   ('x':_) -> return (mpr0,steps,d)
   ('M':_) -> showMarks d m state currpr
   _ -> do putStrLn ("'"++ln++"' ??")
           runREPL d m (mpr0,steps) currpr
\end{code}

Undoing
\begin{code}
calcUndo d m st@(_,[]) currpr = runREPL d m st currpr
calcUndo d m (mpr0,[(_,_)]) _
                     = runREPL d (prevm m) (unMark mpr0,[]) mpr0
calcUndo d m (p,(_:((w,q):steps))) _
                = runREPL d (prevm m) (p,(w,q'):steps) q'
                where q' = popMark q
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
calcStep :: (Ord s, Show s)
         => Dict s -> Mark -> (MPred s -> BeforeAfter s)
         -> (MPred s, [RWResult s]) -> MPred s
         -> IO ( MPred s, [RWResult s], Dict s )
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
calcCStep :: (Ord s, Show s)
          => Dict s -> Mark -> (MPred s -> BeforeAfters s)
          -> (MPred s, [RWResult s]) -> MPred s
          -> IO ( MPred s, [RWResult s], Dict s )
calcCStep d m cstepf st@(mpr0,steps) currpr
 = case cstepf currpr of
    (_,"",_)  ->  runREPL d m st currpr
    ( before, comment, afters' )
      -> do putStrLn $ unlines $ ccshow d $ zip [1..] afters'
            let num = length afters'
            putStrLn ("Please select 1.."++show num)
            sel <- fmap getInt getLine
            if 1 <= sel && sel <= num
             then do let step' = condResolve d sel (comment,afters')
                     putStrLn ( "\n = " ++ show comment )
                     runREPL d m (mpr0,(step':steps)) (snd step')
             else runREPL d m st currpr
 where
   getInt (c:_)
    | isDigit c = digitToInt c
   getInt _ = 0

ccshow d [] = []
ccshow d ((i,(cpr,rmpr)):rest)
 = ["","(" ++ show i++ ") provided:    " ++ pdshow 80 d cpr
   ,"--"
   ,pmdshow 80 d noStyles rmpr]
   ++ ccshow d rest
\end{code}

Showing Marks
\begin{code}
showMarks :: (Ord s, Show s)
          => Dict s -> Mark
          -> (MPred s, [RWResult s]) -> MPred s
          -> IO ( MPred s, [RWResult s], Dict s )
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
stepshow :: Mark -> MarkStyle
stepshow n m
 | n == prevm m  =  Just styleOld
 | n == m        =  Just styleNew
 | otherwise     =  Nothing
 where
   styleOld = Underline
   styleNew = styleRed
\end{code}

Now, rendering the results to look pretty:
\begin{code}
calcPrint :: (Ord s, Show s)
          => ( MPred s, [RWResult s], Dict s ) -> String
calcPrint ( mpr0, steps, d )
 = unlines ( "" : versionShow d : "" : pmdshow 80 d (stepshow 0) mpr0
             : (stepPrint d (nextm 0) $ reverse steps))

stepPrint :: (Ord s, Show s)
          => Dict s -> Mark -> [RWResult s] -> [String]
stepPrint d m [] = []
stepPrint d m ((comment,mpr):rest)
 = [""," = " ++ show comment,""] ++ [pmdshow 80 d (stepshow m) mpr]
   ++ stepPrint d (nextm m) rest


outcome :: ( MPred s, [RWResult s], Dict s ) -> MPred s
outcome ( mpr0, [],          _ )  =  mpr0
outcome ( _,    ((_,mpr'):_), _)  =  mpr'
\end{code}
