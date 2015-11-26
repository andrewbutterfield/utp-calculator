\HDRa{Calculator Predicates}\label{ha:calc-preds}
\begin{code}
module CalcPredicates where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Debug.Trace
import PrettyPrint
import CalcTypes
import StdPrecedences
\end{code}

\HDRb{Substitutions}\label{hb:SmartSubs}

Smart constructors and equality testing for substitutions.
\begin{code}
mkSub e []  = e
mkSub e sub = Sub e $ sort sub

mkPSub (_,pr) []  = pr
mkPSub mpr sub = PSub mpr $ sort sub

-- substitutions are sorted for comparison
ssame ::  (Eq s, Ord s) => Substn s -> Substn s -> Bool
ssame sub1 sub2 = sort sub1 == sort sub2
\end{code}
We treat expressions as atomic from the perspective of
pretty-printing and highlighting.

\HDRb{Marking}\label{hb:marking}

\begin{code}
noMark :: Mark m => Pred m s -> MPred m s
noMark pr = ([], pr)

reMark :: Mark m => m -> MPred m s -> MPred m s
reMark m (_, pr) = ([m], pr)

addMark :: Mark m => m -> MPred m s -> MPred m s
addMark m (ms, pr) = (m:ms, pr)
\end{code}

\begin{code}
-- build a basic predicate at the MPred level
bT, bF :: Mark m => MPred m s
bT              =  noMark T
bF              =  noMark F
bPV str         =  noMark $ PVar str
bEqual e1 e2    =  noMark $ Equal e1 e2
bAtm e          =  noMark $ Atm e
bComp str mprs  =  noMark $ Comp str mprs
bPSub mpr subs  =  noMark $ mkPSub mpr subs
\end{code}

\HDRb{Dictionary}\label{hb:DataDict}

Dictionary query and construction
\begin{code}
isPredEntry (PredEntry _ _ _ _ _) = True
isPredEntry _ = False
isExprEntry (ExprEntry _ _ _ _ _) = True
isExprEntry _ = False
isAlfEntry (AlfEntry _) = True
isAlfEntry _ = False
isPVarEntry (PVarEntry _) = True
isPVarEntry _ = False

nullDict :: Dict m s
nullDict = M.empty

plookup :: String -> Dict m s -> Maybe (Entry m s)
plookup nm d
 = case M.lookup nm d of
     Just pd@(PredEntry _ _ _ _ _)  ->  Just pd
     _                            ->  Nothing

elookup :: String -> Dict m s -> Maybe (Entry m s)
elookup nm d
 = case M.lookup nm d of
     Just ed@(ExprEntry _ _ _ _ _)  ->  Just ed
     _                            ->  Nothing

alookup :: String -> Dict m s -> Maybe (Entry m s)
alookup nm d
 = case M.lookup nm d of
     Just ad@(AlfEntry _)  ->  Just ad
     _                     ->  Nothing

vlookup :: String -> Dict m s -> Maybe (Entry m s)
vlookup nm d
 = case M.lookup nm d of
     Just ve@(PVarEntry _)  ->  Just ve
     _                    ->  Nothing
\end{code}

When we merge dictionary entries we concat \texttt{AlfEntry},
but otherwise take the first:
\begin{code}
mergeEntry :: Entry m s -> Entry m s -> Entry m s
mergeEntry (AlfEntry a1) (AlfEntry a2) = AlfEntry (a1++a2)
mergeEntry e _ = e
\end{code}


Default predicate entry functions
\begin{code}
pnone :: ( String, Pred m s)
pnone = ( "", PUndef )
nosimp :: [Pred m s] -> ( String, Pred m s)
nosimp es = pnone
pdoes :: String -> (Dict m s -> [Pred m s] -> Pred m s)
     -> Dict m s -> [Pred m s]
     -> ( String, Pred m s )
pdoes nm p d ps = ( nm, p d ps )
\end{code}


For expression definitions,
we define a default evaluator that does nothing,
and a simple wrapper for evals that always do something
\begin{code}
none :: ( String, Expr s)
none = ( "", Undef )
noeval :: [Expr s] -> ( String, Expr s)
noeval es = none
does :: String -> (Dict m s -> [Expr s] -> Expr s)
     -> Dict m s -> [Expr s]
     -> ( String, Expr s )
does nm f d es = ( nm, f d es )
\end{code}


We predefine some standard alphabet names
\begin{code}
aAlf  = "Alf"   -- entire alphabet
aObs  = "Obs"   -- all undashed variables
aObs' = "Obs'"  -- all dashed variables
aMdl  = "Mdl"   -- all undashed model variables
aMdl' = "Mdl'"  -- all dashed model variables
aScr  = "Scr"   -- all undashed script variables
aScr' = "Scr'"  -- all dashed script variables
aDyn  = "Dyn"   -- all undashed dynamic observables
aDyn' = "Dyn'"  -- all dashed dynamic observables
aStc  = "Stc"   -- all undashed static parameters
\end{code}
A consistent set of definitions should obey the following laws:
\RLEQNS{
   Alf &=& Obs \cup Obs'
\\ Obs &=& Mdl \cup Scr & \mbox{dashed similarly}
\\ Obs &=& Dyn \cup Stc & \mbox{dashed similarly}
\\ \emptyset &=& Mdl \cap Scr & \mbox{dashed similarly}
\\ \emptyset &=& Dyn \cap Stc & \mbox{dashed similarly}
\\ Stc' &=& \emptyset
}
The last law is why we do not provide a\texttt{ Stc'} alphabet entry.

In general we expect the relation to be homogeneous on the dynamic variables
\RLEQNS{
   Dyn' &=& (Dyn)'
}
In most cases, script variables will be dynamic:
\RLEQNS{
   Scr &\subseteq& Dyn & \mbox{dashed similarly}
}
A basic minimal definition adhering to all the above rules
consists of $Scr$, $nonScrDyn$ and $Stc$
with the following calculations of the rest:
\RLEQNS{
   Scr' &=& (Scr)'
\\ Dyn &=& Scr \cup nonScrDyn
\\ Dyn' &=& (Dyn)'
\\ Mdl &=& nonScrDyn \cup Stc
\\ Mdl' &=& (nonScrDyn)'
}
with $Obs$, $Alf$ etc derived as above.
\begin{code}
stdAlfDictGen :: [String] -> [String] -> [String] -> Dict m s
stdAlfDictGen scr nonScrDyn stc
 = let
    scr' = map addDash scr
    dyn = scr ++ nonScrDyn
    dyn' = map addDash dyn
    mdl = nonScrDyn ++ stc
    mdl' = map addDash nonScrDyn
    obs = mdl ++ scr
    obs' = mdl' ++ scr'
    alf = obs ++ obs'
   in M.fromList $ mapsnd (AlfEntry . sort)
     [ (aAlf, alf)
     , (aObs, obs), (aObs', obs')
     , (aMdl, mdl), (aMdl', mdl')
     , (aScr, scr), (aScr', scr')
     , (aDyn, dyn), (aDyn', dyn')
     , (aStc, stc)
     ]
\end{code}

Variable basics:
\begin{code}
isDash, notDash :: String -> Bool
isDash v = last v == '\''
notDash v = last v /= '\''

addDash, remDash :: String -> String
addDash v = v ++"'"
remDash = init
\end{code}


\HDRb{Display}

We define the display of an expression using a dictionary
to provide exceptional ways to render things.
\begin{code}
edshow :: Show s => Dict m s -> Expr s -> String
edshow d (St s)     =  show s
edshow d (B b)      =  show b
edshow d (Z i)      =  show i
edshow d (Var v)    =  v
edshow d Undef      =  "Undefined"
edshow d (App f es)
 = case elookup f d of
    Nothing  ->  stdFShow d f es
    Just (ExprEntry _ _ _ showf _) -> showf d es
edshow d (Sub e sub) = pshow d e ++ showSub d sub

dlshow d sep xs = concat (intersperse sep $ map (edshow d) xs)

pshow d e@(St _)     =  "("++edshow d e++")"
pshow d e@(App _ _)  =  "("++edshow d e++")"
pshow d e            =       edshow d e

showSub d subs
 = "[" ++ dlshow d "," es ++ "/" ++ lsshow vs ++ "]"
 where (vs,es) = unzip subs

lsshow vs = concat $ intersperse "," vs
\end{code}


By default we print \texttt{App f [e1,...,en]} as \texttt{f(e1,...,en)},
using the following helper functions:
\begin{code}
stdFShow d f es = f ++ "(" ++ dlshow d "," es ++ ")"

stdFDefn d fname vs ebody eval = (vs,ebody,stdFShow d fname,eval)
\end{code}
For now, we don't support infix function syntax.

Now, prettiness..
\begin{code}
pdshow w d = render w . showp d 0
\end{code}

Code to add parentheses when required by a change in current precedence level.
\begin{code}
paren :: Int -> Int -> PP -> PP
paren outerp innerp (PP w (PPC _ _ sepp pps))
 | innerp < outerp  =  (PP w (PPC (ppa "(") (ppa ")") sepp pps))
paren outerp innerp pp = pp
\end{code}


Pretty-printing predicates,
which now just underlines atomic values,
and colours equality green and composite names blue.
\begin{code}
showp :: (Ord s, Show s) => Dict m s -> Int -> Pred m s -> PP
showp d _ T  = pps Underline $ ppa "true"
showp d _ F  = pps Underline $ ppa "false"
showp d _ (PVar p)  = ppa p
showp d p (Equal e1 e2)
   = paren p precEq
       $ ppopen' (pps styleGreen $ ppa " = ")
                 [ppa $ edshow d e1, ppa $ edshow d e2]
showp d p (Atm e) = ppa $ edshow d e
showp d p (PSub pr sub)
   = pplist $ [showp d precSub $ snd pr, ppa $ showSub d sub]

showp d p (Comp cname pargs)
 = case plookup cname d of
    Nothing  ->  stdCshow d cname pargs
    Just (PredEntry _ _ _ showf _) -> showf d p pargs

stdCshow :: (Ord s, Show s)
         => Dict m s -> String -> [MPred m s] -> PP
stdCshow d cname pargs
 = pplist [ pps styleBlue $ ppa cname
          , ppclosed "(" ")" "," $ map (showp d 0 .snd) pargs ]
\end{code}
