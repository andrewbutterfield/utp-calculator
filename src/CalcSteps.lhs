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
import CalcSysTypes
import CalcZipper

dbg str x = trace (str++show x) x
\end{code}


\newpage
\HDRb{Calculation Step Basics}\label{hb:step-basics}

Given a decision,
typically obtained from the user,
we can resolve a conditional step
into a completed one:
\begin{code}
condResolve :: (Ord s, Show s)
         => Dict s -> Int -> MCRWResult s -> MRWResult s
condResolve _ _ Nothing = Nothing
condResolve d i (Just (nm, [(pr,mpr,chgd)])) = Just (nm,mpr,chgd)
condResolve d i (Just (nm, outcomes))
 = Just( nm
         ++ ", given "
         ++ pdshow 1000 d cnd -- no linebreaks, for now
       , res, chgd )
 where (cnd, res, chgd) = outcomes !! (i-1)
\end{code}

%\newpage
%\HDRb{Atomic Step}\label{hb:atomic-step}
%
%We treat things like simplification here as one big atomic modify step.
%\begin{code}
%doAtomicStep :: Mark -> (Mark -> MPred s -> RWResult s) -> MPred s
%             -> Maybe (MPred s, String, MPred s)
%doAtomicStep m mcstep mpr@(_,pr)
% = case mcstep m pr of
%     Nothing -> Nothing
%     Just (what,pr',_) -> Just (mpr,what,noMark pr')
%\end{code}

\newpage
\HDRb{Recursive Predicate Search}\label{hb:rec-pred-srch}


We now look at applying calculation steps by recursively exploring
a predicate, and returning when we succeed.

\HDRc{Search Top Level}\label{hc:srch-top}

This call encapsulates the use of zippers completely:
\begin{code}
doStepSearch :: Show s => Mark -> (MPred s -> MRWResult s)  -> MPred s
             -> Maybe (BeforeAfter s)
doStepSearch m cstep mpr
 = let
     ((mpr1,what,mpr2),ss) = stepFocus cstep $ startMPZ mpr
     pmpr' = unzipMPZ ss $ addMark m mpr1
     nmpr' = unzipMPZ ss $ addMark m mpr2
   in if null what then Nothing else Just (pmpr',what,nmpr')
\end{code}
We will need to lift functions from \texttt{Pred} to \texttt{MPred}:
\begin{code}
rwLift :: (Pred s -> RWResult s) -> MPred s -> MRWResult s
rwLift prf (ms,pr)
 = case prf pr of
     Nothing -> Nothing
     Just (what,pr',chgd) -> Just (what,(ms,pr'),chgd)
\end{code}

\HDRc{Search Current Focus}\label{hc:srch-focus}

We try a step function first at the current focus level,
only recursing in deeper if that fails:
\begin{code}
stepFocus :: (MPred s -> MRWResult s) -> MPZipper s -> MPZip2 s
stepFocus cstep mpz@( mpr, ss )
 = case cstep mpr of
     Nothing                 ->  stepComponents cstep mpz
     Just ( what, mpr', _ )  ->  ((mpr, what, mpr'), ss)
\end{code}

\HDRc{Search Sub-Components}\label{hc:srch-sub-comp}

We are now systematically exploring composite sub-parts:
\begin{code}
stepComponents :: (MPred s -> MRWResult s) -> MPZipper s -> MPZip2 s

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
stepComp' :: (MPred s -> MRWResult s)
          -> MPred' s   -- current Comp'
          -> [MPred' s] -- current zip history
          -> MPred s    -- current focus, within Comp
          -> MPZip2 s

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
doStepCSearch :: Mark -> (MPred s -> MCRWResult s)  -> MPred s
              -> Maybe (BeforeAfters s)
doStepCSearch m ccstep mpr
 = let
     ((mpr1,what,mprs2),ss) = stepCFocus ccstep $ startMPZ mpr
     pmpr' = unzipMPZ ss $ addMark m mpr1
     nmprs' = mapsnd (unzipMPZ ss . addMark m) mprs2
   in if null what then Nothing else Just (pmpr',what,nmprs')
\end{code}
We will need to lift functions from \texttt{Pred} to \texttt{MPred}:
\begin{code}
crwLift :: (Pred s -> CRWResult s) -> MPred s -> MCRWResult s
crwLift prf (ms,pr)
 = case prf pr of
     Nothing -> Nothing
     Just (what,res) -> Just (what,map (cresLift ms) res)
 where cresLift ms (pcond,pres,chgd) = (pcond,(ms,pres),chgd)
\end{code}

\HDRc{Conditionally Search Current Focus}\label{hc:cond-srch-focus}

We try a step function first at the current focus level,
only recursing in deeper if that fails:
\begin{code}
stepCFocus :: (MPred s -> MCRWResult s) -> MPZipper s -> CMPZip2 s
stepCFocus ccstep mpz@( mpr, ss )
 = case ccstep mpr of
    Nothing              ->  stepCComponents ccstep mpz
    Just (what, cmprs')  ->  ((mpr, what, map fixafters cmprs'), ss)

fixafters (pr, mpr', _) = (pr, mpr')
\end{code}

\HDRc{Conditionally Search Sub-Components}\label{hc:cnd-srch-sub-comp}

We are now systematically exploring composite sub-parts:
\begin{code}
stepCComponents :: (MPred s -> MCRWResult s) -> MPZipper s -> CMPZip2 s

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
stepCComp' :: (MPred s -> MCRWResult s)
          -> MPred' s   -- current Comp'
          -> [MPred' s] -- current zip history
          -> MPred s    -- current focus, within Comp
          -> CMPZip2 s

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
expandDefn :: (Ord s, Show s) => Dict s -> Mark
           -> MPred s -> Maybe (BeforeAfter s)
expandDefn d m mpr  = doStepSearch m (expDefs d) mpr

expDefs :: Dict s -> MPred s -> MRWResult s
expDefs d mpr@(ms, Comp name mprs )
 = case plookup name d of
    Just pd@(PredEntry _ _ _ pdef _)
      -> case pdef d $ map snd mprs of
          Just (what,pr',chgd) -> Just (what, (ms,pr'), chgd)
          _ -> Nothing
    _ -> Nothing
expDefs _ _ = Nothing
\end{code}


\newpage

\HDRb{(Reduction) Laws}\label{hb:reduce-laws}

\HDRc{Simple Reduction}

\begin{code}
doReduce :: (Ord s, Show s) => Dict s -> Mark
           -> MPred s -> Maybe (BeforeAfter s)
doReduce d m mpr
 = case M.lookup "laws" d of
    Just (LawEntry red _ _)  ->  doRed d m mpr red
    _                        ->  Nothing

doRed :: (Ord s, Show s) => Dict s -> Mark -> MPred s -> [RWFun s]
      -> Maybe (BeforeAfter s)
doRed d m mpr [] = Nothing
doRed d m mpr@(ms,_) (rf:rfs)
 = case doStepSearch m (rwLift $ rf d) mpr of
    Nothing    ->  doRed d m mpr rfs
    reduction  ->  reduction -- add m in as extra mark?
\end{code}

\HDRc{Conditional Reduction}

\begin{code}
doCReduce :: (Ord s, Show s) => Dict s -> Mark
           -> MPred s -> Maybe (BeforeAfters s)
doCReduce d m mpr
 = case M.lookup "laws" d of
    Just (LawEntry _ cred _)  ->  doCRed d m mpr cred
    _                         ->  Nothing

doCRed :: (Ord s, Show s) => Dict s -> Mark -> MPred s -> [CRWFun s]
       -> Maybe (BeforeAfters s)
doCRed d m mpr [] = Nothing
doCRed d m mpr (rf:rfs)
 = case doStepCSearch m (crwLift $ rf d) mpr of
    Nothing      ->  doCRed d m mpr rfs
    creductions  ->  creductions
\end{code}

\HDRc{Loop Unrolling}

\begin{code}
doUnroll :: (Ord s, Show s) => String -> Dict s -> Mark
           -> MPred s -> Maybe (BeforeAfter s)
doUnroll ns d m mpr
 = case M.lookup "laws" d of
    Just (LawEntry _ _ unr)   ->  doUnr ns d m mpr unr
    _                         ->  Nothing

doUnr :: (Ord s, Show s) => String -> Dict s -> Mark -> MPred s
      -> [String -> RWFun s] -> Maybe (BeforeAfter s)
doUnr ns d m mpr [] = Nothing
doUnr ns d m mpr (rf:rfs)
 = case doStepSearch m (rwLift $ rf ns d) mpr of
     Nothing    ->  doUnr ns d m mpr rfs
     unrolling  ->  unrolling
\end{code}

Hmmmm, all of the above could be abstracted down to one thing...
(Even more if we make everything use \texttt{BeforeAfters}.
