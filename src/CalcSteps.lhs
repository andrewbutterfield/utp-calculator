\HDRa{Calculator Steps}\label{ha:calc-steps}
\begin{code}
module CalcSteps where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcPredicates
import CalcZipper
\end{code}

\HDRb{Calculation Step Intro}\label{hb:step-intro}

Imagine an expression $e$ to which we apply $step$ three times,
which results in the following changes:
\[
  step_i : t_i \mapsto t'_i
\]
The presentation of the calculation should look like the following,
where underlining denotes ``old'' and the colour red denotes ``new'':
\RLEQNS{
\\ && e
\EQ{defn of $e$ (w.l.o.g.)}
\\&& ( \ldots \OLD{t_1} \ldots t_2 \ldots t_3 \ldots)
\EQm{step_1}
\\&& ( \ldots \NEW{t'_1} \ldots \OLD{t_2} \ldots t_3 \ldots)
\EQm{step_2}
\\&& ( \ldots t'_1 \ldots \NEW{t'_2} \ldots \OLD{t_3} \ldots)
\EQm{step_3}
\\&& ( \ldots t'_1 \ldots t'_2 \ldots \NEW{t'_3} \ldots)
}
Notice how each $step_i$ affects the Old/New marking of both its predecessor
and successor expressions.
Rather than having two markings (Old/New) it turns out to be more efficient
to have a numeric marking, so $step_i$ introduces mark number $i$.
The interpetation of such marks as old, new or irrelevant can then be done
relative to the numbering of the step outcome being rendered for display.

We can breakdown the above calculation using mark numbers ($M_i$) as follows
\RLEQNS{
   e  && ( \ldots t_1 \ldots t_2 \ldots t_3 \ldots)
\EQm{step_1}
\\ pe_1 && ( \ldots \OLD{M_1(t_1)} \ldots t_2 \ldots t_3 \ldots) & \mbox{display 1=Old}
\\
\\ ne_1 && ( \ldots M_1(t'_1) \ldots t_2 \ldots t_3 \ldots)
\EQm{step_2}
\\ pe_2 && ( \ldots \NEW{M_1(t'_1)} \ldots \OLD{M_2(t_2)} \ldots t_3 \ldots) & \mbox{display 1=New, 2=Old}
\\
\\ ne_2 && ( \ldots M_1(t'_1) \ldots M_2(t'_2) \ldots t_3 \ldots)
\EQm{step_3}
\\ pe_3 && ( \ldots M_1(t'_1) \ldots \NEW{M_2(t'_2)} \ldots \OLD{M_3(t_3)} \ldots) & \mbox{display 2=New, 3=Old}
\\
\\ ne_3 && ( \ldots M_1(t'_1) \ldots M_2(t'_2) \ldots \NEW{M_3(t'_3)} \ldots) & \mbox{display 3=New}
}

So we see that $step_i$ takes $ne_{i-1}$ and produces:
\begin{itemize}
  \item $pe_i$, where $M_i$ has been wrapped around $t_i$
  \item $ne_i$, which is $pe_i$, where $t_i$ (already marked with $M_i$)
   is replaced by $t'_i$.
\end{itemize}
This seems to present a problem for the zipper,
as we have to identify corresponding locations,
where $t_i$ and $t'_i$ reside,
in two different versions of a single expression.
However the structure of the two expressions is identical everywhere else
so a single zipper ``path'' can be applied to both.

\begin{code}
type MPZip2 m s = (MPred m s, String, MPred m s, [MPred' m s])
\end{code}


\HDRb{Calculation Step Basics}\label{hb:step-basics}

A failed step returns a null string,
and the predicate part is generally considered undefined.
\begin{code}
nope :: CalcResult m s
nope = ( "", error "calc. step failed" )
\end{code}
Given a decision, we can resolve a conditional step
into a completed one:
\begin{code}
condResolve :: (Ord s, Show s)
         => Dict m s -> Int -> CCalcResult m s -> CalcResult m s
condResolve d i ( nm, outcomes ) -- i is typically obtained from user
 = ( nm 
     ++ ", given "
     ++ pdshow 1000 d cnd -- no linebreaks, for now
   , res )
 where (cnd, res) = outcomes !! (i-1)
\end{code}

\newpage
\HDRb{Recursive Predicate Search}\label{hb:rec-pred-srch}


We now look at applying calculation steps by recursively exploring
a predicate, and returning when we succeed.

\HDRc{Search Top Level}\label{hc:srch-top}

This call encapsulates the use of zippers completely:
\begin{code}
doStep :: Mark m
       => m -> CalcStep m s  -> MPred m s
       -> Maybe (MPred m s, String, MPred m s)
doStep m cstep mpr
 = let
     (mpr1,what,mpr2,ss) = stepFocus cstep $ startMPZ mpr
     pmpr' = unzipMPZ ss $ reMark m mpr1
     nmpr' = unzipMPZ ss $ reMark m mpr2
   in if null what then Nothing else Just (pmpr',what,nmpr')
\end{code}

\HDRc{Search Current Focus}\label{hc:srch-focus}

We try a step function first at the current focus level,
only recursing in deeper if that fails:
\begin{code}
stepFocus :: CalcStep m s -> MPZipper m s -> MPZip2 m s
stepFocus cstep mpz@( mpr, ss )
 = let ( what, mpr' ) = cstep mpr
   in if null what 
      then stepComponents cstep mpz
      else (mpr, what, mpr', ss) 
\end{code}

\HDRc{Search Sub-Components}\label{hc:srch-sub-comp}

We are now systematically exploring composite sub-parts:
\begin{code}
stepComponents :: CalcStep m s -> MPZipper m s -> MPZip2 m s

-- Substitution, simple, only 1 sub-component:
stepComponents cstep ( (mp, PSub mpr subs), ss )
  = stepFocus cstep ( mpr, PSub' mp subs : ss )
  
-- Composites: trickier, so start with simplest case
stepComponents cstep ( (mp, Comp name [mpr]), ss )
 = stepFocus cstep ( mpr, Comp' mp name [] [] : ss )

stepComponents cstep ( (mp, Comp name (mpr:mprs)), ss )
  = stepComp' cstep (Comp' mp name [] mprs) ss mpr

stepComponents cstep ( mpr, ss ) = ( mpr, "", mpr, ss ) 
\end{code}

\HDRc{Search Component List}\label{hc:srch-list}

Going through a sub-component list:
\begin{code}
stepComp' :: CalcStep m s 
          -> MPred' m s   -- current Comp'
          -> [MPred' m s] -- current zip history
          -> MPred m s    -- current focus, within Comp
          -> MPZip2 m s
         
-- end case, processing last components
stepComp' cstep s@(Comp' mp name before []) ss mpr
 = let result@( _, what, _, _ ) = stepFocus cstep (mpr, s : ss )
   in if null what
      then ( mpr, "", mpr, ss )
      else result

-- general case, more components remaining
stepComp' cstep s@(Comp' mp name before after@(npr:rest)) ss mpr
 = let result@( _, what, _, _ ) = stepFocus cstep (mpr, s : ss )
   in if null what
      then stepComp' cstep (Comp' mp name (before++[mpr]) rest) ss npr
      else result
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



