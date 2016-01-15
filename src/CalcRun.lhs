\HDRa{Running the Calculator}\label{ha:calc-run}
\begin{code}
module CalcRun where
import Utilities
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


\newpage
\HDRc{Calculation process}

We start with $ne_0 = p$, and no steps
\[ (ne_0,\seqof{}) \]
Running $step_1$ on $ne_0$ produces $(pe_1,ne_1)$
We replace $ne_0$ with $ne_1$, and push $pe_1$ onto the list
\[ (ne_1,\seqof{pe_1}) \]
Running $step_2$ on $ne_1$ produces $(pe_2,ne_2)$
We replace $ne_1$ with $ne_2$, and push $pe_2$ onto the list
\[ (ne_2,\seqof{pe_2,pe_1}) \]
Running $step_3$ on $ne_2$ produces $(pe_3,ne_3)$
We replace $ne_2$ with $ne_3$, and push $pe_3$ onto the list
\[ (ne_3,\seqof{pe_3,pe_2,pe_1}) \]

Running $step_i$ on $ne_{i-1}$ produces $(pe_i,ne_i)$
We replace $ne_{i-1}$ with $ne_i$, and push $pe_i$ onto the list
\[ (ne_i,\seqof{pe_i,pe_{i-1},\dots,pe_2,pe_1}) \]

Note that $pe_i = M_i(ne_{i-1})$.

For undo, we can revert $pe_i$ back to $ne_{i-1}$
by removing all occurrences of marking $i$.

\def\CALCINV{
Given a structure of the form
\[
  (n_k,\seqof{p_k,p_{k-1},\dots,p_i,\dots,p_2,p_1})
\]
we have the following invariant:
\RLEQNS{
    1 &\in& markings(p_1) & \say{the $pe_1$ case}
\\ \setof{i-1,i} &\subseteq& markings(p_i), 1 < i \leq k &\say{the $pe_i$ case}
\\ k &\in& markings(n_k) & \say{the $ne_k$ case}
}
}
\CALCINV

Why do we have $n_k$ separate?
Because the others are in fact paired with a string ($w_k$) identifying the step.
\[
  (n_k,\seqof{(w_k,p_k),(w_{k-1},p_{k-1}),
   \dots,(w_i,p_i),\dots,(w_2,p_2),(w_1,p_1)})
\]

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
      runREPL d' startm (mpr,[])
 where d' = dictMrg d $ dictVersion calcVersion

calcVersion = "UTP-Calc v0.0.1"

versionShow d
 = case alookup version d of
    Just (AlfEntry vs)
            -> (concat $ intersperse ", " vs)
    Nothing -> ""
\end{code}

Now, the main REPL loop:
\begin{code}
runREPL :: (Ord s, Show s)
        => Dict s -> Mark -> (MPred s, [RWResult s])
        -> IO (CalcLog s)
runREPL d m state@(currpr,steps)
 = do
  if invMarks (currpr,steps,d)
   then return ()
   else putStrLn "**** Marking Invariant fails ****"
  putStr ( pmdshow 80 d noStyles currpr
         ++ "\n\n ?,d,r,l,s,c,u,x :- " )
  ln <- getLine
  case ln of
   ('?':_) -> calcHelp d m state
   ('s':_) -> calcStep d m (simplify d $ nextm m) state
   ('u':_) -> calcUndo d m state
   ('d':_) -> calcStep d m (expandDefn d $ nextm m) state
   ('r':_) -> calcStep d m (doReduce   d $ nextm m) state
   ('c':_) -> calcCStep d m (doCReduce d $ nextm m) state
   ('l':_) -> calcStep  d m (doUnroll d $ nextm m) state
   ('x':_) -> return (currpr,steps,d)
   ('M':_) -> showMarks d m state
   ('B':_) -> viewBefore d m state
   ('A':_) -> viewAfter d m state
   _ -> do putStrLn ("'"++ln++"' ??")
           runREPL d m (currpr,steps)
\end{code}

Undoing
\begin{code}
calcUndo d m st@(_,[]) = runREPL d m st
calcUndo d m (n_k,(_,q):steps)
                = runREPL d (prevm m) (q',steps)
                where q' = stripMark m q
\end{code}

Help
\begin{code}
calcHelp d m st
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
       , "B - view before (DEBUG)"
       , "A - view after (DEBUG)"
       ]
      runREPL d m st
\end{code}

\newpage
Applying a given kind of step:
\begin{code}
calcStep :: (Ord s, Show s)
         => Dict s -> Mark -> (MPred s -> BeforeAfter s)
         -> (MPred s, [RWResult s])
         -> IO (CalcLog s)
calcStep d m stepf st@(currpr,steps)
 = do case stepf currpr of
       ( _, "", _ )  ->  runREPL d m st
       ( before,comment, after )
         -> do  putStrLn ( "\n = " ++ show comment )
                let st' = stUpdate (comment,before) after st
                runREPL d (nextm m) st'

stUpdate wbefore after ( _, steps) = ( after, wbefore:steps)
\end{code}

Apply a given conditional step:
\begin{code}
calcCStep :: (Ord s, Show s)
          => Dict s -> Mark -> (MPred s -> BeforeAfters s)
          -> (MPred s, [RWResult s])
          -> IO (CalcLog s)
calcCStep d m cstepf st@(currpr,steps)
 = case cstepf currpr of
    (_,"",_)  ->  runREPL d m st
    ( before, comment, afters' )
      -> do putStrLn $ unlines $ ccshow d $ zip [1..] afters'
            let num = length afters'
            putStrLn ("Please select 1.."++show num)
            sel <- fmap getInt getLine
            if 1 <= sel && sel <= num
             then do let (_,after) = condResolve d sel (comment,afters')
                     putStrLn ( "\n = " ++ show comment )
                     let st' = stUpdate (comment, before) after st
                     runREPL d (nextm m) st'
             else runREPL d m st
 where
   getInt (c:_)
    | isDigit c = digitToInt c
   getInt _ = 0

ccshow :: (Show s, Ord s)
       => Dict s -> [(Int,(Pred s, MPred s))] -> [String]
ccshow d [] = []
ccshow d ((i,(cpr,rmpr)):rest)
 = ["","(" ++ show i++ ") provided:    " ++ pdshow 80 d cpr
   ,"--"
   ,pmdshow 80 d noStyles rmpr]
   ++ ccshow d rest
\end{code}

\newpage
Showing Marks
\begin{code}
showMarks :: (Ord s, Show s)
          => Dict s -> Mark
          -> (MPred s, [RWResult s])
          -> IO (CalcLog s)
showMarks d m state@(currpr,steps)
 = do showm (1::Int) $ reverse (currpr:map snd steps)
      runREPL d m state

showm _ [] = return ()
showm i (mpr:mprs)
 = do putStrLn (show i ++ " ! " ++ show (marksOf mpr))
      showm (i+1) mprs

marksOf :: MPred s -> [Mark]
marksOf  ( ms, pr ) = ms ++ predMarks pr

predMarks (Comp _ mprs) = concat $ map marksOf mprs
predMarks (PSub mpr _) = marksOf mpr
predMarks _ = []
\end{code}

Viewing before and after
\begin{code}
viewAfter d m state@(currpr,steps)
 = do putView currpr
      runREPL d m state

viewBefore d m state@(currpr,[])
 = do putView currpr
      runREPL d m state
viewBefore d m state@(currpr,(_,prevpr):_)
 = do putView prevpr
      runREPL d m state
\end{code}

\CALCINV
\begin{code}
invMarks :: CalcLog s -> Bool
invMarks (n_0, [],_) =  null $ marksOf n_0
invMarks (n_k, ps,_)
 = invMarksNE k n_k
   && all invPE (zip [1..] $ reverse ps)
 where
   k = length ps
   invPE (i,(_,p_i)) = invMarksPE i p_i

invMarksPE i p_i
 | i == 1         =  1 `elem` marksOf p_i
 | otherwise      =  [i-1,i] \\ marksOf p_i == []
invMarksNE k n_k  =  k `elem` marksOf n_k
\end{code}

\newpage
\HDRb{Displaying Calculations}

First,
a mark-style function:
\begin{code}
type StepNo = Int
stepshow :: StepNo -> MarkStyle
stepshow s m
 | s == prevm m  =  Just styleOld
 | s == m        =  Just styleNew
 | otherwise     =  Nothing
 where
   styleOld = Underline
   styleNew = styleMagenta
\end{code}

Now, rendering the results to look pretty:
\begin{code}
calcPrint :: (Ord s, Show s) => CalcLog s -> String
calcPrint ( currpr, steps, d )
 = unlines ( "" : versionShow d : ""
             : (stepPrint d 0 $ reverse steps)
               ++ [pmdshow 80 d (stepshow $ length steps) currpr])

stepPrint :: (Ord s, Show s)
          => Dict s -> StepNo -> [RWResult s] -> [String]
stepPrint d s [] = []
stepPrint d s ((comment,mpr):rest)
 = [pmdshow 80 d (stepshow s) mpr]
   ++[" = " ++ show comment]
   ++ stepPrint d (s+1) rest


outcome :: CalcLog s -> MPred s
outcome ( mpr0, [],          _ )  =  mpr0
outcome ( _,    ((_,mpr'):_), _)  =  mpr'
\end{code}
