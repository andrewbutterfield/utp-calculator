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
condResolve :: Dict -> Int -> MCRWResult -> MRWResult
condResolve _ _ Nothing = Nothing
condResolve d i (Just (nm, [(pr,mpr,chgd)])) = Just (nm,mpr,chgd)
condResolve d i (Just (nm, outcomes))
 = Just( nm
         ++ ", given "
         ++ plainShow 1000 d cnd -- no linebreaks, for now
       , res, chgd )
 where (cnd, res, chgd) = outcomes !! (i-1)
\end{code}

%\newpage
%\HDRb{Atomic Step}\label{hb:atomic-step}
%
%We treat things like simplification here as one big atomic modify step.
%\begin{code}
%doAtomicStep :: Mark -> (Mark -> MPred -> RWResult) -> MPred
%             -> Maybe (MPred, String, MPred)
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
doStepSearch :: Mark -> (MPred -> MRWResult)  -> MPred
             -> Maybe (BeforeAfter)
doStepSearch m cstep mpr
 = let
     ((mpr1,what,mpr2),ss) = stepFocus cstep $ startMPZ mpr
     pmpr' = unzipMPZ ss $ addMark m mpr1
     nmpr' = unzipMPZ ss $ addMark m mpr2
   in if null what then Nothing else Just (pmpr',what,nmpr')
\end{code}
We will need to lift functions from \texttt{Pred} to \texttt{MPred}:
\begin{code}
rwLift :: (Pred -> RWResult) -> MPred -> MRWResult
rwLift prf (pr, MT ms _)
 = case prf pr of
     Nothing -> Nothing
     Just (what,pr',chgd)
      -> Just (what,topMark ms $ buildMarks pr',chgd)
\end{code}

\HDRc{Search Current Focus}\label{hc:srch-focus}

We try a step function first at the current focus level,
only recursing in deeper if that fails:
\begin{code}
stepFocus :: (MPred -> MRWResult) -> MPZipper -> MPZip2
stepFocus cstep mpz@( mpr, ss )
 = case cstep mpr of
     Just ( what, mpr', _ )  ->  ((mpr, what, mpr'), ss)
     Nothing                 ->  stepComponents cstep mpz
\end{code}

\HDRc{Search Sub-Components}\label{hc:srch-sub-comp}

We are now systematically exploring composite sub-parts:
\begin{code}
stepComponents :: (MPred -> MRWResult) -> MPZipper -> MPZip2


-- Substitution, simple, only 1 sub-component:
stepComponents cstep ( (PSub pr subs, MT ms [smt]), ss )
  = stepFocus cstep ( (pr, smt), (PSub' subs, MT' ms [] []) : ss )

-- Composites: trickier, so start with simplest case
stepComponents cstep ( (Comp name [pr], MT ms [cmt]), ss )
 = stepFocus cstep ( (pr, cmt), (Comp' name [] [], MT' ms [] []) : ss )

stepComponents cstep ( (Comp name (pr:prs), MT ms (mt:mts)), ss )
  = stepComp' cstep (Comp' name [] prs, MT' ms [] mts) ss (pr, mt)

stepComponents cstep ( mpr, ss ) = ( (mpr, "", mpr), ss )
\end{code}

\HDRc{Search Component List}\label{hc:srch-list}

Going through a sub-component list:
\begin{code}
stepComp' :: (MPred -> MRWResult)
          -> MPred'   -- current Comp'
          -> [MPred'] -- current zip history
          -> MPred    -- current focus, within Comp
          -> MPZip2

-- end case, processing last components
stepComp' cstep s@(Comp' name before [], MT' ms mbef []) ss mpr
 = let result@( (_, what, _), _ ) = stepFocus cstep (mpr, s:ss)
   in if null what
      then ( (mpr, "", mpr), ss )
      else result

-- general case, more components remaining
stepComp' cstep s@( Comp' name before after@(npr:rest)
                  , MT' ms mbef (mnxt:maft) ) ss mpr@(pr,mt)
 = let result@( (_, what, _), _ )  = stepFocus cstep (mpr, s:ss)
   in if null what
      then stepComp' cstep
                     ( Comp' name (before++[pr]) rest
                     , MT' ms (mbef++[mt]) maft ) ss (npr,mnxt)
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
doStepCSearch :: Mark -> (MPred -> MCRWResult)  -> MPred
              -> Maybe (BeforeAfters)
doStepCSearch m ccstep mpr
 = let
     ((mpr1,what,mprs2),ss) = stepCFocus ccstep $ startMPZ mpr
     pmpr' = unzipMPZ ss $ addMark m mpr1
     nmprs' = mapsnd (unzipMPZ ss . addMark m) mprs2
   in if null what then Nothing else Just (pmpr',what,nmprs')
\end{code}
We will need to lift functions from \texttt{Pred} to \texttt{MPred}:
\begin{code}
crwLift :: (Pred -> CRWResult) -> MPred -> MCRWResult
crwLift prf (pr, mt)
 = case prf pr of
     Nothing -> Nothing
     Just (what,res) -> Just (what,map (cresLift mt) res)
 where cresLift mt (pcond,pres,chgd) = (pcond,buildMarks pres,chgd)
\end{code}

\HDRc{Conditionally Search Current Focus}\label{hc:cond-srch-focus}

We try a step function first at the current focus level,
only recursing in deeper if that fails:
\begin{code}
stepCFocus :: (MPred -> MCRWResult) -> MPZipper -> CMPZip2
stepCFocus ccstep mpz@( mpr, ss )
 = case ccstep mpr of
    Nothing              ->  stepCComponents ccstep mpz
    Just (what, cmprs')  ->  ((mpr, what, map fixafters cmprs'), ss)

fixafters (pr, mpr', _) = (pr, mpr')
\end{code}

\HDRc{Conditionally Search Sub-Components}\label{hc:cnd-srch-sub-comp}

We are now systematically exploring composite sub-parts:
\begin{code}
stepCComponents :: (MPred -> MCRWResult) -> MPZipper -> CMPZip2

-- Substitution, simple, only 1 sub-component:
stepCComponents ccstep ( (PSub pr subs, MT ms [smt]), ss )
  = stepCFocus ccstep ( (pr, smt)
                      , (PSub' subs, MT' ms [] []) : ss )

-- Composites: trickier, so start with simplest case
stepCComponents ccstep ( (Comp name [pr], MT ms [smt]), ss )
 = stepCFocus ccstep ( (pr, smt)
                     , (Comp' name [] [], MT' ms [] []) : ss )

stepCComponents ccstep ( (Comp name (pr:prs), MT ms (mt:mts)), ss )
  = stepCComp' ccstep ( Comp' name [] prs
                      , MT' ms [] mts ) ss (pr, mt)

stepCComponents ccstep ( mpr, ss ) = ( (mpr, "", [(T,mpr)]), ss )
\end{code}

\HDRc{Conditionally Search Component List}\label{hc:cond-srch-list}

Going through a sub-component list:
\begin{code}
stepCComp' :: (MPred -> MCRWResult)
          -> MPred'   -- current Comp'
          -> [MPred'] -- current zip history
          -> MPred    -- current focus, within Comp
          -> CMPZip2

-- end case, processing last components
stepCComp' ccstep s@(Comp' name before [], MT' ms mbef []) ss mpr
 = let result@((_, what, _), _) = stepCFocus ccstep (mpr, s:ss)
   in if null what
      then ( (mpr, "", [(T,mpr)]), ss )
      else result

-- general case, more components remaining
stepCComp' ccstep s@( Comp' name before after@(npr:rest)
                    , MT' ms mbef maft@(nmt:mrest) ) ss mpr@(pr,mt)
 = let result@((_, what, _), _) = stepCFocus ccstep (mpr, s:ss)
   in if null what
      then stepCComp' ccstep
                   ( Comp' name (before++[pr]) rest
                   , MT' ms (mbef++[mt]) mrest ) ss (npr, nmt)
      else result
\end{code}

\HDRb{Definition Expansion}\label{hb:defn-expand}

\begin{code}
expandDefn :: Dict -> Mark
           -> MPred -> Maybe (BeforeAfter)
expandDefn d m mpr  = doStepSearch m (expDefs d) mpr
\end{code}

\begin{code}
expDefs :: Dict -> MPred -> MRWResult

expDefs d mpr@(Comp name prs, MT ms mts)
 = case plookup name d of
    Just pd@(PredEntry _ _ _ pdef _)
      -> case pdef d prs of
          Just (what,pr',chgd)
            -> Just (what, topMark ms $ buildMarks pr', chgd)
          _ -> Nothing
    _ -> Nothing

expDefs d mpr@(Atm (App name es), MT ms mts)
 = case elookup name d of
    Just ed@(ExprEntry _ _ edef _ _)
      -> case edef d es of
          Just (what,e')
            -> Just ( what
                    , topMark ms
                        $ buildMarks (Atm e')
                    , True )
          _ -> Nothing
    _ -> Nothing

expDefs _ _ = Nothing
\end{code}

\newpage

\HDRb{(Reduction) Laws}\label{hb:reduce-laws}

\HDRc{Simple Reduction}

\begin{code}
doReduce :: Dict -> [Pred] -> Mark
           -> MPred -> Maybe (BeforeAfter)
doReduce d invs m mpr
 = case M.lookup laws d of
    Just (LawEntry red _ _)  ->  doRed d m invs mpr red
    _                        ->  Nothing

doRed :: Dict -> Mark -> [Pred] -> MPred -> [RWFun]
      -> Maybe (BeforeAfter)
doRed d m invs mpr [] = Nothing
doRed d m invs mpr@(ms,_) (rf:rfs)
 = case doStepSearch m (rwLift $ rf d invs) mpr of
    Nothing    ->  doRed d m invs mpr rfs
    reduction  ->  reduction -- add m in as extra mark?
\end{code}

\HDRc{Conditional Reduction}

\begin{code}
doCReduce :: Dict -> Mark
           -> MPred -> Maybe (BeforeAfters)
doCReduce d m mpr
 = case M.lookup laws d of
    Just (LawEntry _ cred _)  ->  doCRed d m mpr cred
    _                         ->  Nothing

doCRed :: Dict -> Mark -> MPred -> [CRWFun]
       -> Maybe (BeforeAfters)
doCRed d m mpr [] = Nothing
doCRed d m mpr (rf:rfs)
 = case doStepCSearch m (crwLift $ rf d) mpr of
    Nothing      ->  doCRed d m mpr rfs
    creductions  ->  creductions
\end{code}

\HDRc{Loop Unrolling}

\begin{code}
doUnroll :: String -> Dict -> [Pred] -> Mark
           -> MPred -> Maybe (BeforeAfter)
doUnroll ns d invs m mpr
 = case M.lookup laws d of
    Just (LawEntry _ _ unr)   ->  doUnr ns d m invs mpr unr
    _                         ->  Nothing

doUnr :: String -> Dict -> Mark -> [Pred] -> MPred
      -> [String -> RWFun] -> Maybe (BeforeAfter)
doUnr ns d m invs mpr [] = Nothing
doUnr ns d m invs mpr (rf:rfs)
 = case doStepSearch m (rwLift $ rf ns d invs) mpr of
     Nothing    ->  doUnr ns d m invs mpr rfs
     unrolling  ->  unrolling
\end{code}

Hmmmm, all of the above could be abstracted down to one thing...
(Even more if we make everything use \texttt{BeforeAfters}.
