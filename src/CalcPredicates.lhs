\HDRa{Calculator Predicates}\label{ha:calc-preds}
\begin{code}
module CalcPredicates where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import NiceSymbols
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcSysTypes
import StdPrecedences
\end{code}

\HDRb{Substitutions}\label{hb:SmartSubs}

Smart constructors and equality testing for substitutions.
\begin{code}
mkSbs e []  = e
mkSbs e sub = Sub e $ sort sub

mkPSub :: Pred -> [(String, Expr)] -> Pred
mkPSub pr []  = pr
mkPSub pr sub = PSub pr $ sort sub

-- substitutions are sorted for comparison
ssame ::  Substn -> Substn -> Bool
ssame sub1 sub2 = sort sub1 == sort sub2
\end{code}
We treat expressions as atomic from the perspective of
pretty-printing and highlighting.

\HDRb{Marking}\label{hb:marking}

\HDRc{Basic Marking}\label{hc:basic-marking}
\begin{code}
noMark :: Pred -> MPred
noMark = buildMarks

unMark :: MPred -> MPred
unMark (pr, MT _ mts) = (pr, MT [] mts)

topMark :: Marks -> MPred -> MPred
topMark ms (pr, MT _ mts) = (pr, MT ms mts)

addMark :: Mark -> MPred -> MPred
addMark m (pr, MT ms mts) = (pr, MT (m:ms) mts)

popMark :: MPred -> MPred
popMark (pr, MT ms mts) = (pr, MT (ttail ms) mts)

remMark :: Mark -> MPred -> MPred
remMark m (pr, MT ms mts) = (pr, MT (ms\\[m]) mts)
\end{code}

We also need sometimes to strip out a mark at all levels
in a predicate:
\begin{code}
stripMark :: Mark -> MPred -> MPred
stripMark m (pr, mt) = (pr, stripMark' m mt)

stripMark' m (MT ms mts)
 = MT (ms\\[m]) $ map (stripMark' m) mts
\end{code}

Or even more drastically, clean them all out:
\begin{code}
cleanMarks :: MPred -> MPred
cleanMarks (pr, _) = buildMarks pr

cleanCalc :: CalcLog -> CalcLog
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

nullDict :: Dict
nullDict = M.empty

plookup :: String -> Dict -> Maybe (Entry)
plookup nm d
 = case M.lookup nm d of
     Just pd@(PredEntry _ _ _ _ _)  ->  Just pd
     _                              ->  Nothing

elookup :: String -> Dict -> Maybe (Entry)
elookup nm d
 = case M.lookup nm d of
     Just ed@(ExprEntry _ _ _ _ _)  ->  Just ed
     _                              ->  Nothing

alookup :: String -> Dict -> Maybe (Entry)
alookup nm d
 = case M.lookup nm d of
     Just ad@(AlfEntry _)  ->  Just ad
     _                     ->  Nothing
\end{code}

\HDRc{Dictionary Construction}

\begin{code}
makeDict :: [(String, Entry)] -> Dict
makeDict = M.fromList

entry :: String -> Entry -> Dict
entry s e = makeDict [(s, e)]

dictVersion :: String -> Dict
dictVersion vtxt = entry version $ AlfEntry [vtxt]

-- we want these to sort before \ESC !
version = "\bVersion"
laws = "\blaws" -- for "the" LawEntry
\end{code}

When we merge dictionary entries
we concatenate \texttt{AlfEntry} and \texttt{LawEntry},
but otherwise take the first:
\begin{code}
mergeEntry :: Entry -> Entry -> Entry
mergeEntry (AlfEntry a1) (AlfEntry a2)  =  AlfEntry (a1++a2)
mergeEntry (LawEntry r1 cr1 u1) (LawEntry r2 cr2 u2)
                         = LawEntry (r1++r2) (cr1++cr2) (u1++u2)
mergeEntry e _ = e

dictMrg :: Dict -> Dict -> Dict
dictMrg = M.unionWith mergeEntry

mergeDicts ::[Dict] -> Dict
mergeDicts = foldl dictMrg M.empty
\end{code}


Default expression/predicate entry functions
\begin{code}
noEq :: Dict -> [Expr] -> [Expr] -> Maybe Bool
noEq _ _ _ = Nothing

subAny =["*"]

pNoChg :: String -> Rewrite
pNoChg _ _ _ = Nothing

noDefn _ _ = Nothing

-- labelling definitions
ldefn :: String -> Pred -> RWResult
ldefn nm pr = Just ( "Expanded defn. of " ++ nm, pr, True )
edefn :: String -> Expr -> Maybe (String, Expr)
edefn nm e = Just ( "Expanded defn. of " ++ nm, e )
\end{code}


For expression definitions,
we define a default evaluator that does nothing,
and a simple wrapper for evals that always do something
\begin{code}
none :: ( String, Expr)
none = ( "", Undef )
--noeval :: [Expr] -> ( String, Expr)
noeval _ = none
--noEval :: Dict -> [Expr] -> (String, Expr)
noEval _ = noeval
does :: String -> (Dict -> [Expr] -> Expr)
     -> Dict -> [Expr]
     -> ( String, Expr )
does what f d es = ( what, f d es )
justMakes f d es = ( "",   f es )
\end{code}


\HDRb{Display}

We define the display of an expression using a dictionary
to provide exceptional ways to render things.
\begin{code}
edshow :: Dict -> Expr -> String
edshow d St         =  bold "s"
edshow d (B b)      =  show b
edshow d (Z i)      =  show i
edshow d (Var v)    =  v
edshow d Undef      =  "Undefined"
edshow d (App f es)
 = case elookup f d of
    Nothing                        ->  stdFShow d f es
    Just (ExprEntry _ showf _ _ _) -> showf d es
edshow d (Sub e sub) = pshow d e ++ showSub d sub

dlshow :: Dict -> String -> [Expr] -> [Char]
dlshow d sep xs = concat (intersperse sep $ map (edshow d) xs)

pshow :: Dict -> Expr -> [Char]
pshow d St     =  "("++edshow d St++")"
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
stdFShow :: Dict -> [Char] -> [Expr] -> [Char]
stdFShow d f es = f ++ "(" ++ dlshow d "," es ++ ")"


stdFDefn d fname vs ebody eval = (vs,ebody,stdFShow d fname,eval)
\end{code}
For now, we don't support infix function syntax.

We provide a default printer for an expression entry
\begin{code}
defEPrint :: String -> Dict -> [Expr] -> String
defEPrint nm d es = stdFShow d nm es
\end{code}

Now, prettiness..
\begin{code}
plainShow :: Int -> Dict -> Pred -> String
plainShow w d pr = render w $ showp d noStyles 0 pr

pmdshow :: Int -> Dict -> MarkStyle -> MPred -> String
pmdshow w d msf mpr = render w $ mshowp d msf 0 mpr

pdshow :: Int -> Dict -> MarkStyle -> Pred -> String
pdshow w d msf pr = render w $ mshowp d msf 0 $ buildMarks pr
\end{code}

Pretty-printing predicates.
\begin{code}
mshowp :: Dict -> MarkStyle -> Int -> MPred -> PP
mshowp d msf p mpr@( pr, MT ms _)
 = sshowp $ catMaybes $ map msf ms
 where
  sshowp []  =  mshowp0 d msf p mpr
  sshowp (s:ss) = pps s $ sshowp ss

mshowp0 :: Dict -> MarkStyle -> Int -> MPred -> PP
mshowp0 d _ _ (T, _)  = ppa _true
mshowp0 d _ _ (F, _)  = ppa _false
mshowp0 d _ _ (PVar p, _)  = ppa p
mshowp0 d _ p (Equal e1 e2, _)
   = paren p precEq
       $ ppopen' (ppa " = ")
                 [ppa $ edshow d e1, ppa $ edshow d e2]
mshowp0 d _ p (Atm e, _) = ppa $ edshow d e
mshowp0 d msf p (PSub pr sub, MT _ mts)
   = pplist $ [ subCompShow msf mts d precSbs 1 pr
              , ppa $ showSub d sub ]

mshowp0 d msf p (Comp cname pargs, MT _ mts)
 = case plookup cname d of
    Just (PredEntry _ showf _ _ _)
       ->  showf (subCompShow msf mts d) d p pargs
    _  ->  stdCshow d msf cname mts pargs

subCompShow :: MarkStyle -> [MTree] -> Dict
            -> SubCompPrint
subCompShow msf mts d p i subpr
 | 0 < i && i <= length mts
   = mshowp d msf p (subpr, mts !!(i-1))
 | otherwise
   = mshowp d msf p $ buildMarks subpr

stdCshow :: Dict -> MarkStyle -> String -> [MTree] -> [Pred]
         -> PP
stdCshow d msf cname mts pargs
 = pplist [ ppa cname
          , ppclosed "(" ")" ","
            $ ppwalk 1 (subCompShow msf mts d 0) pargs ]

ppwalk :: Int -> (Int -> Pred -> PP) -> [Pred] -> [PP]
ppwalk _ _ []            =  []
ppwalk i sCS (arg:args)  =  (sCS i arg) : ppwalk (i+1) sCS args

showp :: Dict -> MarkStyle -> Int -> Pred -> PP
showp d ms p pr = mshowp d ms p $ buildMarks pr

ppSuper d e = _supStr $ edshow d e
\end{code}

\HDRb{Debugging Aids}

\begin{code}
dbg str x = trace (str++show x) x
cdbg d str pr = trace (str++plainShow 80 d pr) pr
csdbg d str prs = trace (str++unlines (map (plainShow 80 d) prs)) prs
\end{code}
