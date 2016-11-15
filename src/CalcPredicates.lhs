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

mkPSub :: Ord s => Pred s -> [(String, Expr s)] -> Pred s
mkPSub pr []  = pr
mkPSub pr sub = PSub pr $ sort sub

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
noMark = buildMarks

unMark :: MPred s -> MPred s
unMark (pr, MT _ mts) = (pr, MT [] mts)

topMark :: Marks -> MPred s -> MPred s
topMark ms (pr, MT _ mts) = (pr, MT ms mts)

addMark :: Mark -> MPred s -> MPred s
addMark m (pr, MT ms mts) = (pr, MT (m:ms) mts)

popMark :: MPred s -> MPred s
popMark (pr, MT ms mts) = (pr, MT (ttail ms) mts)

remMark :: Mark -> MPred s -> MPred s
remMark m (pr, MT ms mts) = (pr, MT (ms\\[m]) mts)
\end{code}

We also need sometimes to strip out a mark at all levels
in a predicate:
\begin{code}
stripMark :: Mark -> MPred s -> MPred s
stripMark m (pr, mt) = (pr, stripMark' m mt)

stripMark' m (MT ms mts)
 = MT (ms\\[m]) $ map (stripMark' m) mts
\end{code}

Or even more drastically, clean them all out:
\begin{code}
cleanMarks :: MPred s -> MPred s
cleanMarks (pr, _) = buildMarks pr

cleanCalc :: CalcLog s -> CalcLog s
cleanCalc ((currpr, steps, is),d)
 = ( (cleanMarks currpr
     , mapsnd cleanMarks steps
     , is )
   , d )
\end{code}


\HDRb{Dictionary}\label{hb:DataDict}

\HDRc{Dictionary query}
\begin{code}
isPredEntry (PredEntry _ _ _ _ _) = True
isPredEntry _ = False
isExprEntry (ExprEntry _ _ _ _ _) = True
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
     Just ed@(ExprEntry _ _ _ _ _)  ->  Just ed
     _                              ->  Nothing

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
mergeEntry (AlfEntry a1) (AlfEntry a2)  =  AlfEntry (a1++a2)
mergeEntry (LawEntry r1 cr1 u1) (LawEntry r2 cr2 u2)
                         = LawEntry (r1++r2) (cr1++cr2) (u1++u2)
mergeEntry e _ = e

dictMrg :: Dict s -> Dict s -> Dict s
dictMrg = M.unionWith mergeEntry

mergeDicts ::[Dict s] -> Dict s
mergeDicts = foldl dictMrg M.empty
\end{code}


Default expression/predicate entry functions
\begin{code}
noEq :: Dict s -> [Expr s] -> [Expr s] -> Maybe Bool
noEq _ _ _ = Nothing

subAny =["*"]

pNoChg :: String -> Rewrite s
pNoChg _ _ _ = Nothing

noDefn _ _ = Nothing

-- labelling definitions
ldefn :: String -> Pred s -> RWResult s
ldefn nm pr = Just ( "Expanded defn. of " ++ nm, pr, True )
edefn :: String -> Expr s -> Maybe (String, Expr s)
edefn nm e = Just ( "Expanded defn. of " ++ nm, e )
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
    Nothing                        ->  stdFShow d f es
    Just (ExprEntry _ showf _ _ _) -> showf d es
edshow d (Sub e sub) = pshow d e ++ showSub d sub

dlshow :: Show s => Dict s -> String -> [Expr s] -> [Char]
dlshow d sep xs = concat (intersperse sep $ map (edshow d) xs)

pshow :: Show s => Dict s -> Expr s -> [Char]
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
stdFShow :: Show s => Dict s -> [Char] -> [Expr s] -> [Char]
stdFShow d f es = f ++ "(" ++ dlshow d "," es ++ ")"


stdFDefn d fname vs ebody eval = (vs,ebody,stdFShow d fname,eval)
\end{code}
For now, we don't support infix function syntax.

We provide a default printer for an expression entry
\begin{code}
defEPrint :: Show s => String -> Dict s -> [Expr s] -> String
defEPrint nm d es = stdFShow d nm es
\end{code}

Now, prettiness..
\begin{code}
plainShow :: (Show s, Ord s) => Int -> Dict s -> Pred s -> String
plainShow w d pr = render w $ showp d noStyles 0 pr

pmdshow :: (Show s, Ord s)
        => Int -> Dict s -> MarkStyle -> MPred s -> String
pmdshow w d msf mpr = render w $ mshowp d msf 0 mpr

pdshow :: (Show s, Ord s)
        => Int -> Dict s -> MarkStyle -> Pred s -> String
pdshow w d msf pr = render w $ mshowp d msf 0 $ buildMarks pr
\end{code}

Pretty-printing predicates.
\begin{code}
mshowp :: (Ord s, Show s)
       => Dict s -> MarkStyle -> Int -> MPred s -> PP
mshowp d msf p mpr@( pr, MT ms _)
 = sshowp $ catMaybes $ map msf ms
 where
  sshowp []  =  mshowp0 d msf p mpr
  sshowp (s:ss) = pps s $ sshowp ss

mshowp0 :: (Ord s, Show s)
        => Dict s -> MarkStyle -> Int -> MPred s -> PP
mshowp0 d _ _ (T, _)  = ppa "true"
mshowp0 d _ _ (F, _)  = ppa "false"
mshowp0 d _ _ (PVar p, _)  = ppa p
mshowp0 d _ p (Equal e1 e2, _)
   = paren p precEq
       $ ppopen' (ppa " = ")
                 [ppa $ edshow d e1, ppa $ edshow d e2]
mshowp0 d _ p (Atm e, _) = ppa $ edshow d e
mshowp0 d msf p (PSub pr sub, MT _ mts)
   = pplist $ [ subCompShow msf mts d precSub 1 pr
              , ppa $ showSub d sub ]

mshowp0 d msf p (Comp cname pargs, MT _ mts)
 = case plookup cname d of
    Just (PredEntry _ showf _ _ _)
       ->  showf (subCompShow msf mts d) d p pargs
    _  ->  stdCshow d msf cname mts pargs

subCompShow :: (Ord s, Show s)
            => MarkStyle -> [MTree] -> Dict s
            -> SubCompPrint s
subCompShow msf mts d p i subpr
 | 0 < i && i <= length mts
   = mshowp d msf p (subpr, mts !!(i-1))
 | otherwise
   = mshowp d msf p $ buildMarks subpr

stdCshow :: (Ord s, Show s)
         => Dict s -> MarkStyle -> String -> [MTree] -> [Pred s]
         -> PP
stdCshow d msf cname mts pargs
 = pplist [ ppa cname
          , ppclosed "(" ")" ","
            $ ppwalk 1 (subCompShow msf mts d 0) pargs ]

ppwalk :: (Ord s, Show s)
       => Int -> (Int -> Pred s -> PP) -> [Pred s] -> [PP]
ppwalk _ _ []            =  []
ppwalk i sCS (arg:args)  =  (sCS i arg) : ppwalk (i+1) sCS args

showp :: (Ord s, Show s)
      => Dict s -> MarkStyle -> Int -> Pred s -> PP
showp d ms p pr = mshowp d ms p $ buildMarks pr
\end{code}

\HDRb{Debugging Aids}

\begin{code}
dbg str x = trace (str++show x) x
cdbg d str pr = trace (str++plainShow 80 d pr) pr
csdbg d str prs = trace (str++unlines (map (plainShow 80 d) prs)) prs
\end{code}
