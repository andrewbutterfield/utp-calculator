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

Imagine an predicate $p$ containing sub-predicates $q_1$, $q_2$ and $q_3$,
to which we apply $step$ three times,
which results in the following changes:
\[
  step_i : q_i \mapsto q'_i, \qquad i \in 1\ldots 3
\]
The presentation of the calculation should look like the following,
where underlining denotes ``old'' and the colour red denotes ``new'':
\RLEQNS{
\\ && p
\EQ{defn of $p$ (w.l.o.g.)}
\\&& ( \ldots \OLD{q_1} \ldots q_2 \ldots q_3 \ldots)
\EQm{step_1}
\\&& ( \ldots \NEW{q'_1} \ldots \OLD{q_2} \ldots q_3 \ldots)
\EQm{step_2}
\\&& ( \ldots q'_1 \ldots \NEW{q'_2} \ldots \OLD{q_3} \ldots)
\EQm{step_3}
\\&& ( \ldots q'_1 \ldots q'_2 \ldots \NEW{q'_3} \ldots)
}
Notice how each $step_i$ affects the Old/New marking of both its predecessor
and successor predicates.
Rather than having two markings (Old/New) it turns out to be more efficient
to have a numeric marking, so $step_i$ introduces mark number $i$.
The interpetation of such marks as old, new or irrelevant can then be done
relative to the numbering of the step outcome being rendered for display.

We can breakdown the above calculation using mark numbers ($M_i$) as follows
\RLEQNS{
   p  && ( \ldots q_1 \ldots q_2 \ldots q_3 \ldots)
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

So we see that $step_i$ takes $ne_{i-1}$ and produces:
\begin{itemize}
  \item $pe_i$, where $M_i$ has been wrapped around $q_i$
  \item $ne_i$, which is $pe_i$, where $q_i$ (already marked with $M_i$)
   is replaced by $q'_i$.
\end{itemize}
What is not obvious from the above example is what should happen
when two successive steps affect the same or a nested sub-predicate.
Here we find we need to be able to associate multiple marks with
any sub-component.

In order to mark and highlight predicates in calculation steps,
we need to return not just the modified result, marked at the point of change,
but also the original predicate, also marked at the same location
(with the same mark in each case --- the mark identifies the specific
calculation step).
We have a type that has this information,
along with a justification string:
\begin{code}
type BeforeAfter m s
 = ( MPred m s   -- before predicate, marked
   , String      -- justification, null if no change occurred
   , MPred m s ) -- after predicate, marked
\end{code}
In the conditional case, we have lists of outcomes
paired with conditions:
\begin{code}
type BeforeAfters m s
 = ( MPred m s   -- before predicate, marked
   , String      -- justification, null if no change occurred
   , [(Pred m s,MPred m s)] ) -- after predicates, marked
\end{code}

This seems to present a problem for the zipper,
as we have to identify corresponding locations,
where $q_i$ and $q'_i$ reside,
in two different versions of a single predicate.
However the structure of the two predicates is identical everywhere else
so a single zipper ``path'' can be applied to both.

\begin{code}
type MPZip2 m s = (BeforeAfter m s, [MPred' m s])
\end{code}

For conditional searches,
we return a list of \texttt{Pred},\texttt{MPred} pairs:
\begin{code}
type CMPZip2 m s = ( BeforeAfters m s, [MPred' m s] )
\end{code}

\newpage
\HDRb{Calculation Step Basics}\label{hb:step-basics}

A failed step returns a null string,
and the predicate part is generally considered undefined.
\begin{code}
nope :: RWResult m s
nope = ( "", error "calc. step failed" )
\end{code}
Given a decision,
typically obtained from the user,
we can resolve a conditional step
into a completed one:
\begin{code}
condResolve :: (Ord s, Show s)
         => Dict m s -> Int -> CRWResult m s -> RWResult m s
condResolve d i ( nm, [ (T, outcome) ] ) -- no choice
 = ( nm, outcome )
condResolve d i ( nm, outcomes )
 = ( nm
     ++ ", given "
     ++ pdshow 1000 d cnd -- no linebreaks, for now
   , res )
 where (cnd, res) = outcomes !! (i-1)
\end{code}

\newpage
\HDRb{Atomic Step}\label{hb:atomic-step}

We treat things like simplification here as one big atomic modify step.

\begin{code}
doAtomicStep :: Mark m
       => m -> (m -> RWFun m s)  -> MPred m s
       -> Maybe (MPred m s, String, MPred m s)
doAtomicStep m mcstep mpr
 = let (what,mpr') = mcstep m mpr
   in if null what then Nothing else Just (mpr,what,mpr')
\end{code}

\newpage
\HDRb{Recursive Predicate Search}\label{hb:rec-pred-srch}


We now look at applying calculation steps by recursively exploring
a predicate, and returning when we succeed.

\HDRc{Search Top Level}\label{hc:srch-top}

This call encapsulates the use of zippers completely:
\begin{code}
doStepSearch :: Mark m
       => m -> RWFun m s  -> MPred m s
       -> Maybe (BeforeAfter m s)
doStepSearch m cstep mpr
 = let
     ((mpr1,what,mpr2),ss) = stepFocus cstep $ startMPZ mpr
     pmpr' = unzipMPZ ss $ addMark m mpr1
     nmpr' = unzipMPZ ss $ addMark m mpr2
   in if null what then Nothing else Just (pmpr',what,nmpr')
\end{code}

\HDRc{Search Current Focus}\label{hc:srch-focus}

We try a step function first at the current focus level,
only recursing in deeper if that fails:
\begin{code}
stepFocus :: RWFun m s -> MPZipper m s -> MPZip2 m s
stepFocus cstep mpz@( mpr, ss )
 = let ( what, mpr' ) = cstep mpr
   in if null what
      then stepComponents cstep mpz
      else ((mpr, what, mpr'), ss)
\end{code}

\HDRc{Search Sub-Components}\label{hc:srch-sub-comp}

We are now systematically exploring composite sub-parts:
\begin{code}
stepComponents :: RWFun m s -> MPZipper m s -> MPZip2 m s

-- Substitution, simple, only 1 sub-component:
stepComponents cstep ( (mp, PSub mpr subs), ss )
  = stepFocus cstep ( mpr, PSub' mp subs : ss )

-- Composites: trickier, so start with simplest case
stepComponents cstep ( (mp, Comp name [mpr]), ss )
 = stepFocus cstep ( mpr, Comp' mp name [] [] : ss )

stepComponents cstep ( (mp, Comp name (mpr:mprs)), ss )
  = stepComp' cstep (Comp' mp name [] mprs) ss mpr

stepComponents cstep ( mpr, ss ) = ( (mpr, "", mpr), ss )
\end{code}

\HDRc{Search Component List}\label{hc:srch-list}

Going through a sub-component list:
\begin{code}
stepComp' :: RWFun m s
          -> MPred' m s   -- current Comp'
          -> [MPred' m s] -- current zip history
          -> MPred m s    -- current focus, within Comp
          -> MPZip2 m s

-- end case, processing last components
stepComp' cstep s@(Comp' mp name before []) ss mpr
 = let result@( (_, what, _), _ ) = stepFocus cstep (mpr, s : ss )
   in if null what
      then ( (mpr, "", mpr), ss )
      else result

-- general case, more components remaining
stepComp' cstep s@(Comp' mp name before after@(npr:rest)) ss mpr
 = let result@( (_, what, _), _ ) = stepFocus cstep (mpr, s : ss )
   in if null what
      then stepComp' cstep (Comp' mp name (before++[mpr]) rest) ss npr
      else result
\end{code}

\newpage
\HDRb{Recursive Predicate Conditional Search}\label{hb:rec-pred-cond-srch}


We now look at applying \emph{conditional} calculation steps
by recursively exploring
a predicate, and returning when we succeed.

\HDRc{Conditional Search Top Level}\label{hc:cond-srch-top}

This call encapsulates the use of zippers completely:
\begin{code}
doStepCSearch :: Mark m
       => m -> CRWFun m s  -> MPred m s
       -> Maybe (BeforeAfters m s)
doStepCSearch m ccstep mpr
 = let
     ((mpr1,what,mprs2),ss) = stepCFocus ccstep $ startMPZ mpr
     pmpr' = unzipMPZ ss $ addMark m mpr1
     nmprs' = mapsnd (unzipMPZ ss . addMark m) mprs2
   in if null what then Nothing else Just (pmpr',what,nmprs')
\end{code}

\HDRc{Conditionally Search Current Focus}\label{hc:cond-srch-focus}

We try a step function first at the current focus level,
only recursing in deeper if that fails:
\begin{code}
stepCFocus :: CRWFun m s -> MPZipper m s -> CMPZip2 m s
stepCFocus ccstep mpz@( mpr, ss )
 = let ( what, cmprs' ) = ccstep mpr
   in if null what
      then stepCComponents ccstep mpz
      else ((mpr, what, cmprs'), ss)
\end{code}

\HDRc{Conditionally Search Sub-Components}\label{hc:cnd-srch-sub-comp}

We are now systematically exploring composite sub-parts:
\begin{code}
stepCComponents :: CRWFun m s -> MPZipper m s -> CMPZip2 m s

-- Substitution, simple, only 1 sub-component:
stepCComponents ccstep ( (mp, PSub mpr subs), ss )
  = stepCFocus ccstep ( mpr, PSub' mp subs : ss )

-- Composites: trickier, so start with simplest case
stepCComponents ccstep ( (mp, Comp name [mpr]), ss )
 = stepCFocus ccstep ( mpr, Comp' mp name [] [] : ss )

stepCComponents ccstep ( (mp, Comp name (mpr:mprs)), ss )
  = stepCComp' ccstep (Comp' mp name [] mprs) ss mpr

stepCComponents ccstep ( mpr, ss ) = ( (mpr, "", [(T,mpr)]), ss )
\end{code}

\HDRc{Conditionally Search Component List}\label{hc:cond-srch-list}

Going through a sub-component list:
\begin{code}
stepCComp' :: CRWFun m s
          -> MPred' m s   -- current Comp'
          -> [MPred' m s] -- current zip history
          -> MPred m s    -- current focus, within Comp
          -> CMPZip2 m s

-- end case, processing last components
stepCComp' ccstep s@(Comp' mp name before []) ss mpr
 = let result@((_, what, _), _) = stepCFocus ccstep (mpr, s:ss)
   in if null what
      then ( (mpr, "", [(T,mpr)]), ss )
      else result

-- general case, more components remaining
stepCComp' ccstep s@(Comp' mp name before after@(npr:rest)) ss mpr
 = let result@((_, what, _), _) = stepCFocus ccstep (mpr, s:ss)
   in if null what
      then stepCComp' ccstep
                   (Comp' mp name (before++[mpr]) rest) ss npr
      else result
\end{code}

\HDRb{Definition Expansion}\label{hb:defn-expand}

\begin{code}
defnExpand = "expand defn. "

expandDefn :: (Mark m, Ord s, Show s) => Dict m s -> m -> RWFun m s
expandDefn d m mpr
  = error "expandDefn NYI"
\end{code}
