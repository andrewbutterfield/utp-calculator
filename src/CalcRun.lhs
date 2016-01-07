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

\HDRb{Introduction}

We want to produce a result of the form
\RLEQNS{
   ne_0  && ( \ldots q_1 \ldots q_2 \ldots q_3 \ldots)
\EQm{step_1}
\\ pe_1 && ( \ldots \OLD{M_1(q_1)} \ldots q_2 \ldots q_3 \ldots) & \mbox{display 1=Old}
\\
\\ ne_1 && ( \ldots M_1(q'_1) \ldots q_2 \ldots q_3 \ldots)
\EQm{step_2}
\\ pe_2 && ( \ldots \NEW{M_1(q'_1)} \ldots \OLD{M_2(q_2)} \ldots q_3 \ldots) & \mbox{display 1=New, 2=Old}
\\
\\ ne_2 && ( \ldots M_1(q'_1) \ldots M_2(q'_2) \ldots q_3 \ldots)
\EQm{step_3}
\\ pe_3 && ( \ldots M_1(q'_1) \ldots \NEW{M_2(q'_2)} \ldots \OLD{M_3(q_3)} \ldots) & \mbox{display 2=New, 3=Old}
\\
\\ ne_3 && ( \ldots M_1(q'_1) \ldots M_2(q'_2) \ldots \NEW{M_3(q'_3)} \ldots) & \mbox{display 3=New}
}
that will display as
\RLEQNS{
   pe_1 && ( \ldots \OLD{M_1(q_1)} \ldots q_2 \ldots q_3 \ldots) & \mbox{display 1=Old}
\EQm{step_1}
\\ pe_2 && ( \ldots \NEW{M_1(q'_1)} \ldots \OLD{M_2(q_2)} \ldots q_3 \ldots) & \mbox{display 1=New, 2=Old}
\EQm{step_2}
\\ pe_3 && ( \ldots M_1(q'_1) \ldots \NEW{M_2(q'_2)} \ldots \OLD{M_3(q_3)} \ldots) & \mbox{display 2=New, 3=Old}
\EQm{step_3}
\\ ne_3 && ( \ldots M_1(q'_1) \ldots M_2(q'_2) \ldots \NEW{M_3(q'_3)} \ldots) & \mbox{display 3=New}
}
We expect both $pe_i$ and $ne_i$ to contain mark $i$,
and $pe_i$ to also contain mark $i-1$ (as it's obtained from $ne_{i-1}$
by marking it with $i$).


\HDRc{Calculation process}

We start with $ne_0 = p$, and no steps
\[ (ne_0,\seqof{}) \]
Running $step_1$ on $ne_0$ produces $(pe_1,ne_1)$
We replace $ne_0$ with $pe_1$, and push $ne_1$ onto the list
\[ (pe_1,\seqof{ne_1}) \]
Running $step_2$ on $ne_1$ produces $(pe_2,ne_2)$
We replace $ne_1$ with $pe_2$, and push $ne_2$ onto the list
\[ (pe_1,\seqof{ne_2,pe_2}) \]
Running $step_3$ on $ne_2$ produces $(pe_3,ne_3)$
We replace $ne_2$ with $pe_3$, and push $ne_3$ onto the list
\[ (pe_1,\seqof{ne_3,pe_3,pe_2}) \]

Running $step_i$ on $ne_{i-1}$ produces $(pe_i,ne_i)$
We replace $ne_{i-1}$ with $pe_i$, and push $ne_i$ onto the list
\[ (pe_1,\seqof{ne_i,pe_i,\dots,pe_3,pe_2}) \]

Note that $pe_i = M_i(ne_{i-1})$.

For undo, we can revert $pe_i$ back to $ne_{i-1}$
by removing all occurrences of marking $i$.

Given a structure of the form
\[
  (p_1,\seqof{p_k,p_{k-1},\dots,p_i,\dots,p_3,p_2})
\]
we have the following invariant:
\RLEQNS{
   \setof k &\in& markings(p_k) & \say{the $ne_k$ case}
\\ \setof{i-1,i} &\subseteq& markings(p_i), 1 < i < k &\say{the $pe_i$ case}
\\ \setof 1 &=& markings(p_1) & \say{the $pe_1$ case}
}

Why do we have $p_1$ seperate? And why the \texttt{Dict} component?
\newpage
\HDRb{Calculator REPL}

For now we define a simple REPL.
First, some top-level setup:
\begin{code}
calcREPL :: (Ord s, Show s)
         => Dict s ->  MPred s
         -> IO (CalcLog s)
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
        -> IO (CalcLog s)
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
         -> IO (CalcLog s)
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
          -> IO (CalcLog s)
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
          -> IO (CalcLog s)
showMarks d m state@(mpr0,steps) currpr
 = do showm (0::Int) (mpr0:map snd (reverse steps))
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
calcPrint :: (Ord s, Show s) => CalcLog s -> String
calcPrint ( mpr0, steps, d )
 = unlines ( "" : versionShow d : "" : pmdshow 80 d (stepshow 0) mpr0
             : (stepPrint d (nextm 0) $ reverse steps))

stepPrint :: (Ord s, Show s)
          => Dict s -> Mark -> [RWResult s] -> [String]
stepPrint d m [] = []
stepPrint d m ((comment,mpr):rest)
 = [""," = " ++ show comment,""] ++ [pmdshow 80 d (stepshow m) mpr]
   ++ stepPrint d (nextm m) rest


outcome :: CalcLog s -> MPred s
outcome ( mpr0, [],          _ )  =  mpr0
outcome ( _,    ((_,mpr'):_), _)  =  mpr'
\end{code}
