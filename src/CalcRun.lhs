\HDRa{Running the Calculator}\label{ha:calc-run}
\begin{code}
module CalcRun where
import Utilities
import Data.List
import Data.Char
import Data.Maybe
import NiceSymbols
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcPredicates
import CalcSysTypes
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
calcREPL :: Dict -> InvState -> Pred
         -> IO (CalcLog)
calcREPL d invst pr
 = do putStrLn ""
      putStrLn $ versionShow d'
      runREPL d' startm (buildMarks pr,[],invst)
 where d' = dictMrg (dictVersion calcVersion) d

calcVersion = "UTP-Calc v0.2"

versionShow d
 = case alookup version d of
    Just (AlfEntry vs)
            -> (concat $ intersperse ", " vs)
    Nothing -> ""
\end{code}

Now, the main REPL loop:
\begin{code}
runREPL :: Dict -> Mark -> State
        -> IO (CalcLog)
runREPL d m state@(currpr,steps,istate)
 = do
--   if invMPred currpr
--      then return ()
--      else do putStrLn "\n============================"
--              putStrLn "@@@@ M-Pred Invariant fails @@@@"
--              putStrLn $ viewPred currpr
--              putStrLn "\n============================"
--
--   if invMarks (state,d)
--    then return ()
--    else putStrLn "**** Marking Invariant fails ****"
  putStr ( pmdshow 80 d noStyles currpr
         ++ "\n\n ?,d,r,l,s,c,I,i,u,x :- " )
  ln <- getLine
  case ln of
   ('?':_) -> calcHelp  d m state
   ('s':_) -> calcStep  d m (simplify2  d $ nextm m) state
   ('u':_) -> calcUndo  d m state
   ('d':_) -> calcStep  d m (expandDefn d $ nextm m) state
   ('r':_) -> calcStep  d m (doReduce   d invs $ nextm m) state
   ('c':_) -> calcCStep d m (doCReduce  d $ nextm m) state
   ('l':s) -> calcStep  d m (doUnroll s d invs $ nextm m) state
   ('I':_) -> displayInv d m state
   ('i':_) -> calcStep  d m
               (chkInvariants d istate $ nextm m) state
   ('M':_) -> showMarks d m state
   ('B':_) -> viewBefore d m state
   ('A':_) -> viewAfter d m state
   ('x':_) -> return (state,d)
   _ -> do putStrLn ("unrecognised command : '"++ln++"'")
           runREPL d m state
  where invs = map snd istate
\end{code}

Undoing
\begin{code}
calcUndo d m st@(_,[],_) = runREPL d m st
calcUndo d m (n_k,(_,q):steps,is)
                = runREPL d (prevm m) (q',steps,is)
                where q' = stripMark m q
\end{code}

Help
\begin{code}
calcHelp d m st
 = do putStr $ unlines
       [ ""
       , "? - this help message"
       , "s - simplify everywhere (twice)"
       , "i - check invariant"
       , "I - show invariant"
       , "x - exit, returning proof script"
       , "u - undo"
       , "subsequent commands affect the first applicable location"
       , "d - definition expansion"
       , "r - reduction law application"
       , "l[n] - loop unrolling - n: optional depth"
       , "c - conditional reduction step"
       , "--"
       , "M - show marks (DEBUG)"
       , "B - view before (DEBUG)"
       , "A - view after (DEBUG)"
       ]
      runREPL d m st
\end{code}

Displaying the invariant
\begin{code}
displayInv d m st@(_,_,[])
 = do putStrLn "No Invariant!"
      runREPL d m st
displayInv d m st@(_,_,[(_,inv)])
 = do putStrLn ("Invariant:  "++plainShow 80 d inv)
      runREPL d m st
displayInv d m st@(_,_,ivs)
 = do putStrLn "Invariants:"
      sequence $ map (putStrLn . plainShow 80 d . snd) ivs
      runREPL d m st
\end{code}

\newpage
Applying a given kind of step:
\begin{code}
calcStep :: Dict -> Mark -> (MPred -> Maybe (BeforeAfter))
         -> State
         -> IO (CalcLog)
calcStep d m stepf st@(currpr,steps,is)
 = do case stepf currpr of
       Nothing  ->  runREPL d m st
       Just ( before,comment, after )
         -> do  putStrLn ( "\n = " ++ quote comment )
                let st' = stUpdate (comment,before) after st
                runREPL d (nextm m) st'

stUpdate :: (String, MPred) ->  MPred -> State -> State
stUpdate wbefore after ( _, steps, is) = ( after, wbefore:steps, is)

quote str = _ll++' ':str++' ':_gg
\end{code}

Apply a given conditional step:
\begin{code}
calcCStep :: Dict -> Mark -> (MPred -> Maybe(BeforeAfters))
          -> State
          -> IO (CalcLog)
calcCStep d m cstepf st@(currpr,steps,_)
 = case cstepf currpr of
    Nothing  ->  runREPL d m st
    Just( before, comment, afters' )
      -> do putStrLn $ unlines $ ccshow d $ zip [1..] afters'
            let num = length afters'
            putStrLn ("Please select 1.."++show num)
            sel <- fmap getInt getLine
            if 1 <= sel && sel <= num
             then do let afters'' = map addtopmod afters'
                     let Just (why,after,_)
                           = condResolve d sel $ Just (comment,afters'')
                     putStrLn ( "\n = " ++ quote comment )
                     let st' = stUpdate (why, before) after st
                     runREPL d (nextm m) st'
             else runREPL d m st
 where
   getInt (c:_)
    | isDigit c = digitToInt c
   getInt _ = 0
   addtopmod (pr,mpr) = (pr,mpr,True) -- assume top modified

ccshow :: Dict -> [(Int,(Pred, MPred))] -> [String]
ccshow d [] = []
ccshow d ((i,(cpr,rmpr)):rest)
 = ["","(" ++ show i++ ") provided:    " ++ plainShow 80 d cpr
   ,"--"
   ,pmdshow 80 d noStyles rmpr]
   ++ ccshow d rest
\end{code}

\newpage

Mark management
\begin{code}
startm :: Mark
startm = 0
nextm, prevm :: Mark -> Mark
nextm = (+1)
prevm = subtract 1
\end{code}

Showing Marks
\begin{code}
showMarks :: Dict -> Mark
          -> State
          -> IO (CalcLog)
showMarks d m state@(currpr,steps,_)
 = do showm (1::Int) $ reverse (currpr:map snd steps)
      runREPL d m state

showm _ [] = return ()
showm i (mpr:mprs)
 = do putStrLn (show i ++ " ! " ++ show (marksOf mpr))
      showm (i+1) mprs

marksOf :: MPred -> [Mark]
marksOf = mFlatten . snd

mFlatten (MT ms mts) = ms ++ concat (map mFlatten mts)
\end{code}

Viewing before and after
\begin{code}
viewAfter d m state@(currpr,steps,_)
 = do putView currpr
      runREPL d m state

viewBefore d m state@(currpr,[],_)
 = do putView currpr
      runREPL d m state
viewBefore d m state@(currpr,(_,prevpr):_,_)
 = do putView prevpr
      runREPL d m state
\end{code}

\CALCINV
\begin{code}
invMarks :: CalcLog -> Bool
invMarks ((n_0, [],_),_) =  null $ marksOf n_0
invMarks ((n_k, ps,_),_)
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
calcPrint :: CalcLog -> String
calcPrint ( (currpr, steps, _), d )
 = unlines ( "" : versionShow d : ""
             : (stepPrint d 0 $ reverse steps)
               ++ [pmdshow 80 d (stepshow $ length steps) currpr])

stepPrint :: Dict -> StepNo -> [Step] -> [String]
stepPrint d s [] = []
stepPrint d s ((comment,mpr):rest)
 = [pmdshow 80 d (stepshow s) mpr]
   ++[" = " ++ quote comment]
   ++ stepPrint d (s+1) rest


outcome :: CalcLog -> MPred
outcome ((mpr, _, _),_)  =  mpr
\end{code}

Calculation and prettiness all in one go:
\begin{code}
printREPL d invstate mpr
  = do res <- calcREPL d invstate mpr
       putStrLn "\n\nTRANSCRIPT:"
       putStrLn $ calcPrint res
\end{code}

Rendering to a file (without highlighting!)
\begin{code}
saveCalc :: FilePath -> CalcLog -> IO ()
saveCalc fp calc
 = writeFile fp $ calcPrint $ cleanCalc calc
\end{code}

A utility to help guage terminal widths:
\begin{code}
wline n
 = putStrLn $ take n $ concat $ map ten [1..]
 where ten n = " 2345678 "++show (n `mod` 10)
\end{code}
