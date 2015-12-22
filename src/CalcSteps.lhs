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
 = let result@( (_, what, _), _ ) = stepFocus cstep (mpr, s:ss)
   in if null what
      then ( (mpr, "", mpr), ss )
      else result

-- general case, more components remaining
stepComp' cstep s@(Comp' mp name before after@(npr:rest)) ss mpr
 = let result@( (_, what, _), _ )  = stepFocus cstep (mpr, s:ss)
   in if null what
      then stepComp' cstep
                     (Comp' mp name (before++[mpr]) rest) ss npr
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
expandDefn :: (Mark m, Ord s, Show s) => Dict m s -> m
           -> MPred m s -> BeforeAfter m s
expandDefn d m mpr
 = case doStepSearch m (expDefs d) mpr of
     Nothing   ->  ( mpr, "", mpr )
     Just exp  ->  exp

expDefs :: Dict m s -> RWFun m s
expDefs d mpr@(ms, Comp name mprs )
 = case plookup name d of
    Just pd@(PredEntry _ _ pdef _)
      -> let ( what, pr' ) = pdef d mprs
         in ( what, ( ms, pr') )
    _ -> ( "", mpr )
expDefs d mpr = ( "", mpr )
\end{code}


\newpage

\HDRb{(Reduction) Laws}\label{hb:reduce-laws}

\HDRc{Simple Reduction}

\begin{code}
doReduce :: (Mark m, Ord s, Show s) => Dict m s -> m
           -> MPred m s -> BeforeAfter m s
doReduce d m mpr
 = case M.lookup "laws" d of
    Just (LawEntry red cred)  ->  doRed d m mpr red
    _                         -> ( mpr, "", mpr )

doRed d m mpr [] = ( mpr, "", mpr )
doRed d m mpr (rf:rfs)
 = case doStepSearch m (rf d) mpr of
     Nothing   ->  doRed d m mpr rfs
     Just red  ->  red
\end{code}

\HDRc{Conditional Reduction}

\begin{code}
doCReduce :: (Mark m, Ord s, Show s) => Dict m s -> m
           -> MPred m s -> BeforeAfters m s
doCReduce d m mpr
 = case M.lookup "laws" d of
    Just (LawEntry red cred)  ->  doCRed d m mpr cred
    _                         -> ( mpr, "", [] )

doCRed d m mpr [] = ( mpr, "", [] )
doCRed d m mpr (rf:rfs)
 = case doStepCSearch m (rf d) mpr of
    Nothing   ->  doCRed d m mpr rfs
    Just red  ->  red
\end{code}
