\HDRa{Calculator Predicates}\label{ha:calc-preds}
\begin{code}
module CalcPredicates where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcSysTypes
import StdPrecedences
\end{code}

\HDRb{Substitutions}\label{hb:SmartSubs}

Smart constructors and equality testing for substitutions.
\begin{code}
mkSub e []  = e
mkSub e sub = Sub e $ sort sub

mkPSub :: Ord s => MPred s -> [(String, Expr s)] -> Pred s
mkPSub (_,pr) []  = pr
mkPSub mpr sub = PSub mpr $ sort sub

-- substitutions are sorted for comparison
ssame ::  (Eq s, Ord s) => Substn s -> Substn s -> Bool
ssame sub1 sub2 = sort sub1 == sort sub2
\end{code}
We treat expressions as atomic from the perspective of
pretty-printing and highlighting.

\HDRb{Marking}\label{hb:marking}

\HDRc{Basic Marking}\label{hc:basic-marking}
\begin{code}
noMark :: Pred s -> MPred s
noMark pr = ([], pr)

unMark :: MPred s -> MPred s
unMark (_, pr) = ([], pr)

addMark :: Mark -> MPred s -> MPred s
addMark m (ms, pr) = (m:ms, pr)

popMark :: MPred s -> MPred s
popMark (ms, pr) = (ttail ms, pr)

remMark :: Mark -> MPred s -> MPred s
remMark m (ms, pr) = (ms\\[m], pr)
\end{code}

We also need sometimes to strip out a remark at all levels
in a predicate:
\begin{code}
stripMark :: Mark -> MPred s -> MPred s
stripMark m (ms, pr) = (ms\\[m], stripMark' m pr)

stripMark' m (Comp n mprs)  = Comp n $ map (stripMark m) mprs
stripMark' m (PSub mpr sub) = PSub (stripMark m mpr) sub
stripMark' m pr             = pr
\end{code}

Or even more drastically, clean them all out:
\begin{code}
cleanMarks :: MPred s -> MPred s
cleanMarks (_, pr) = ([], cleanMarks' pr)

cleanMarks' (Comp n mprs)  = Comp n $ map cleanMarks mprs
cleanMarks' (PSub mpr sub) = PSub (cleanMarks mpr) sub
cleanMarks' pr             = pr

cleanCalc :: CalcLog s -> CalcLog s
cleanCalc (currpr, steps, d)
 = ( cleanMarks currpr
   , mapsnd cleanMarks steps
   , d )
\end{code}


\begin{code}
-- build a basic predicate at the MPred level
true, false :: MPred s
true           =  noMark T
false          =  noMark F
pvar str       =  noMark $ PVar str
equal e1 e2    =  noMark $ Equal e1 e2
atm e          =  noMark $ Atm e
comp str mprs  =  noMark $ Comp str mprs
psub mpr subs  =  noMark $ mkPSub mpr subs
\end{code}

\HDRb{Dictionary}\label{hb:DataDict}

\HDRc{Dictionary query}
\begin{code}
isPredEntry (PredEntry _ _ _ _ _) = True
isPredEntry _ = False
isExprEntry (ExprEntry _ _ _ _) = True
isExprEntry _ = False
isAlfEntry (AlfEntry _) = True
isAlfEntry _ = False

nullDict :: Dict s
nullDict = M.empty

plookup :: String -> Dict s -> Maybe (Entry s)
plookup nm d
 = case M.lookup nm d of
     Just pd@(PredEntry _ _ _ _ _)  ->  Just pd
     _                              ->  Nothing

elookup :: String -> Dict s -> Maybe (Entry s)
elookup nm d
 = case M.lookup nm d of
     Just ed@(ExprEntry _ _ _ _)  ->  Just ed
     _                            ->  Nothing

alookup :: String -> Dict s -> Maybe (Entry s)
alookup nm d
 = case M.lookup nm d of
     Just ad@(AlfEntry _)  ->  Just ad
     _                     ->  Nothing
\end{code}

\HDRc{Dictionary Construction}

\begin{code}
makeDict :: [(String, Entry s)] -> Dict s
makeDict = M.fromList

entry :: String -> Entry s -> Dict s
entry s e = makeDict [(s, e)]

dictVersion :: String -> Dict s
dictVersion vtxt = entry version $ AlfEntry [vtxt]

version = "Version"
laws = "laws" -- for "the" LawEntry
\end{code}

When we merge dictionary entries
we concatenate \texttt{AlfEntry} and \texttt{LawEntry},
but otherwise take the first:
\begin{code}
mergeEntry :: Entry s -> Entry s -> Entry s
mergeEntry (AlfEntry a1) (AlfEntry a2)       = AlfEntry (a1++a2)
mergeEntry (LawEntry r1 cr1 u1) (LawEntry r2 cr2 u2)
                         = LawEntry (r1++r2) (cr1++cr2) (u1++u2)
mergeEntry e _ = e

dictMrg :: Dict s -> Dict s -> Dict s
dictMrg = M.unionWith mergeEntry
\end{code}


Default expression/predicate entry functions
\begin{code}
noEq :: Dict s -> [Expr s] -> [Expr s] -> Maybe Bool
noEq _ _ _ = Nothing

pNoChg :: String -> Rewrite s
pNoChg name d mprs = Nothing

-- labelling definitions
ldefn :: String -> Pred s -> RWResult s
ldefn nm pr = Just ( "Expanded defn. of " ++ nm, pr, True )
\end{code}


For expression definitions,
we define a default evaluator that does nothing,
and a simple wrapper for evals that always do something
\begin{code}
none :: ( String, Expr s)
none = ( "", Undef )
noeval :: [Expr s] -> ( String, Expr s)
noeval es = none
does :: String -> (Dict s -> [Expr s] -> Expr s)
     -> Dict s -> [Expr s]
     -> ( String, Expr s )
does what f d es = ( what, f d es )
justMakes f d es = ( "",   f es )
\end{code}


\HDRb{Display}

We define the display of an expression using a dictionary
to provide exceptional ways to render things.
\begin{code}
edshow :: Show s => Dict s -> Expr s -> String
edshow d (St s)     =  show s
edshow d (B b)      =  show b
edshow d (Z i)      =  show i
edshow d (Var v)    =  v
edshow d Undef      =  "Undefined"
edshow d (App f es)
 = case elookup f d of
    Nothing                      ->  stdFShow d f es
    Just (ExprEntry _ showf _ _) -> showf d es
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
pdshow :: (Show s, Ord s) => Int -> Dict s -> Pred s -> String
pdshow w d pr = render w $ showp d noStyles 0 pr

pmdshow :: (Show s, Ord s)
        => Int -> Dict s -> MarkStyle -> MPred s -> String
pmdshow w d msf mpr = render w $ mshowp d msf 0 mpr
\end{code}

Pretty-printing predicates.
\begin{code}
mshowp :: (Ord s, Show s) => Dict s -> MarkStyle -> Int -> MPred s -> PP
mshowp d msf p ( ms, pr )
 = sshowp $ catMaybes $ map msf ms
 where
  sshowp []  =  showp d msf p pr
  sshowp (s:ss) = pps s $ sshowp ss

showp :: (Ord s, Show s) => Dict s -> MarkStyle -> Int -> Pred s -> PP
showp d _ _ T  = ppa "true"
showp d _ _ F  = ppa "false"
showp d _ _ (PVar p)  = ppa p
showp d _ p (Equal e1 e2)
   = paren p precEq
       $ ppopen' (ppa " = ")
                 [ppa $ edshow d e1, ppa $ edshow d e2]
showp d _ p (Atm e) = ppa $ edshow d e
showp d ms p (PSub mpr sub)
   = pplist $ [mshowp d ms precSub mpr, ppa $ showSub d sub]

showp d ms p (Comp cname pargs)
 = case plookup cname d of
    Just (PredEntry _ showf _ _ _) -> showf d ms p pargs
    _  ->  stdCshow d ms cname pargs

stdCshow :: (Ord s, Show s)
         => Dict s -> MarkStyle -> String -> [MPred s] -> PP
stdCshow d ms cname pargs
 = pplist [ ppa cname
          , ppclosed "(" ")" "," $ map (mshowp d ms 0) pargs ]
\end{code}
