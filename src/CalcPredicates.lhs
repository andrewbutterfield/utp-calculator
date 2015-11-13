\HDRa{Calculator Predicates}\label{ha:calc-preds}
\begin{code}
module CalcPredicates where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Debug.Trace
import PrettyPrint
\end{code}

Version
\begin{code}
versionCalcPredicates = "CP-0.6"
\end{code}

\HDRb{Syntax}

First, we build some infrastructure to support a flexible expression and predicate
syntax, with an emphasis on allowing tailored notations
(e.g. writing $ps(in)$ and $ps(in,out)$ rather than $in \in ps$ or $\setof{in,out} \subseteq ps$)
and effective pretty-printing of large complex nested terms.


\HDRc{Expression Datatype}\label{hc:ExprData}

We start by defining an expression space that includes
booleans, integers,
variables, function applications, and substitutions,
all parameterised by a generic state type:
\begin{code}
data Expr s
 = St s  -- a value of type State
 | B Bool
 | Z Int
 | Var String
 | App String [Expr s]
 | Sub (Expr s) (Substn s)
 | Undef
 deriving (Eq,Ord,Show)

type Substn s = [(String,Expr s)]
mkSub e []  = e
mkSub e sub = Sub e $ sort sub

-- substitutions are sorted for comparison
ssame ::  (Eq s, Ord s) => Substn s -> Substn s -> Bool
ssame sub1 sub2 = sort sub1 == sort sub2
\end{code}
\DRAFT{We shall keep expressions as-is for now,
viewing them atomically as far as highlighting goes.}


\HDRc{Predicate Datatype}\label{hc:PredData}

Now we need a  predicate syntax,
which has basic predicates
(true, false, predicate-variables, equality and lifted expressions)
along with a generic predicate composite, and substitution.
\begin{code}
data Pred s
 = T
 | F
 | PVar String
 | Equal (Expr s) (Expr s)
 | Atm (Expr s)
 | Comp String [Pred s]
 | PSub (Pred s) (Substn s)
 deriving (Eq, Ord, Show)
\end{code}


\HDRb{Dictionary}\label{hb:DataDict}

We need a dictionary that maps various names
to appropriate definitions.

A dictionary entry is a sum of  definition types defined below
\begin{code}
data Entry s
 = PredEntry (PredDef s)
 | ExprEntry (ExprDef s)
 | AlfEntry AlfDef
 | PVarEntry PVarDef

isPredEntry (PredEntry _) = True
isPredEntry _ = False
isExprEntry (ExprEntry _) = True
isExprEntry _ = False
isAlfEntry (AlfEntry _) = True
isAlfEntry _ = False
isPVarEntry (PVarEntry _) = True
isPVarEntry _ = False

thePredEntry (PredEntry pd) = pd
theExprEntry (ExprEntry fd) = fd
theAlfEntry (AlfEntry ad) = ad
thePVarEntry (PVarEntry pd) = pd

type Dict s = M.Map String (Entry s)

plookup :: String -> Dict s -> Maybe (PredDef s)
plookup nm d
 = case M.lookup nm d of
     Just (PredEntry pd)  ->  Just pd
     _                    ->  Nothing

flookup :: String -> Dict s -> Maybe (ExprDef s)
flookup nm d
 = case M.lookup nm d of
     Just (ExprEntry fd)  ->  Just fd
     _                   ->  Nothing

alookup :: String -> Dict s -> Maybe AlfDef
alookup nm d
 = case M.lookup nm d of
     Just (AlfEntry ad)  ->  Just ad
     _                   ->  Nothing

vlookup :: String -> Dict s -> Maybe PVarDef
vlookup nm d
 = case M.lookup nm d of
     Just (PVarEntry pd)  ->  Just pd
     _                    ->  Nothing
\end{code}

When we merge dictionary entries we concat \texttt{AlfEntry},
but otherwise take the first:
\begin{code}
mergeEntry :: Entry s -> Entry s -> Entry s
mergeEntry (AlfEntry a1) (AlfEntry a2) = AlfEntry (a1++a2)
mergeEntry e _ = e
\end{code}

Predicate definitions
\begin{code}
data PredDef s
 = PD [String]                -- list of formal/bound variables
      (Pred s)                 -- definition body
      (Dict s -> [Pred s] -> PP)     -- pretty printer
      (Dict s -> [Pred s] -> ( String   -- eval name
                             , Expr s )) -- evaluator

instance Show s => Show (PredDef s) where
  show (PD fvs pr _ _) = show fvs ++ " |-> " ++ show pr
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"P" |->  PredEntry (PD  ["Q1","Q2",...,"Qn"] pr pf pv)
\end{verbatim}
as defining a function:
\RLEQNS{
   P(Q_1,Q_2,\ldots,Q_n) &\defs& pr
}
with $pf_\delta(Q_1,Q_2,\ldots,Q_n)$ being a specialised print function
that renders a predicate as required,
and $pv_\delta(Q_1,Q_2,\ldots,Q_n)$ is an valuation function that
attempts to simplify the predicate..
Both are parameterised with a dictionary argument ($\delta$),
which may, or may not, be the dictionary in which the entry occurs.
The string in the result is empty if it failed,
otherwise gives the name of the predicate to be used in the justification
of a proof step.
The evaluator is free to use or ignore the definition body expression $pr$.

We define a default evaluator that does nothing,
and a simple wrapper for evals that always do something
\begin{code}
pnone :: ( String, Pred s)
pnone = ( "", F )
nosimp :: [Pred s] -> ( String, Pred s)
nosimp es = pnone
pdoes :: String -> (Dict s -> [Pred s] -> Pred s)
     -> Dict s -> [Pred s]
     -> ( String, Pred s )
pdoes nm p d ps = ( nm, p d ps )
\end{code}


Expression definitions
\begin{code}
data ExprDef s
 = ED [String]                -- list of formal/bound variables
      (Expr s)                 -- definition body
      (Dict s -> [Expr s] -> String)     -- pretty printer
      (Dict s -> [Expr s] -> ( String   -- eval name
                             , Expr s )) -- evaluator

instance Show s => Show (ExprDef s) where
  show (ED fvs e _ _) = show fvs ++ " |-> " ++ show e
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"f" |->  ExprEntry (ED ["v1","v2",...,"vn"] e pf ev)
\end{verbatim}
as defining a function:
\RLEQNS{
   f(v_1,v_2,\ldots,v_n) &\defs& e
}
with $pf_\delta(e_1,e_2,\ldots,e_n)$ being a specialised print function
that renders a function call as required,
and $ev_\delta(e_1,e_2,\ldots,e_n)$ is an evaluation function that
attempts to evaluate the call.
Both are parameterised with a dictionary argument ($\delta$),
which may, or may not, be the dictionary in which the entry occurs.
The string in the result is empty if it failed,
otherwise gives the name of the function to be used in the justification
of a proof step.
The evaluator is free to use or ignore the definition body expression $e$.

We define a default evaluator that does nothing,
and a simple wrapper for evals that always do something
\begin{code}
none :: ( String, Expr s)
none = ( "", Undef )
noeval :: [Expr s] -> ( String, Expr s)
noeval es = none
does :: String -> (Dict s -> [Expr s] -> Expr s)
     -> Dict s -> [Expr s]
     -> ( String, Expr s )
does nm f d es = ( nm, f d es )
\end{code}


We also want to define alphabets, as sets of names
\begin{code}
type AlfDef = [String]
\end{code}
An entry
\begin{verbatim}
"a" |-> AlfEntry ["v1","v2",..,"vn"]
\end{verbatim}
defines an alphabet:
\RLEQNS{
  a &\defs& \setof{v_1,v_2,\ldots,v_n}
}
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
stdAlfDictGen :: [String] -> [String] -> [String] -> Dict s
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


We sometimes want to associate extra information with given
predicate variables:
\begin{code}
type PVarDef = [String] -- for now, just its alphabet
\end{code}
An entry
\begin{verbatim}
  "P" |-> PVarEntry ["v1","v2",..,"vn"]
\end{verbatim}
declares the alphabet associated with that predicate variable:
\RLEQNS{
   \alpha P &=&  \setof{v_1,v_2,\ldots,v_n}
}

\HDRb{Display}

We define the display of an expression using a dictionary
to provide exceptional ways to render things.
\begin{code}
edshow :: Show s => Dict s -> Expr s -> String
edshow d (St s)     =  show s
edshow d (B b)      =  show b
edshow d (Var v)    =  v
edshow d Undef      =  "Undefined"
edshow d (App f es)
 = case flookup f d of
    Nothing  ->  stdFShow d f es
    Just (ED _ _ showf _) -> showf d es
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
pdshow d = render 78 . showp d 0

-- precedences, higher is tighter, 0 is "loosest"
precEq    = 5
precNot   = 6
precAnd   = 4
precOr    = 3
precImp   = 2
precCond  = 1
precSub   = 7
precSeq   = 2
precIter  = 6
precPSeq  = 3
precPPar  = 2
precPCond = 1
precPIter = 6
\end{code}

Code to add parentheses when required by a change in current precedence level.
\begin{code}
paren :: Int -> Int -> PP -> PP
paren outerp innerp (PP w (PPC _ _ sepp pps))
 | innerp < outerp  =  (PP w (PPC (ppa "(") (ppa ")") sepp pps))
paren outerp innerp pp = pp
\end{code}


Pretty-printing predicates
\begin{code}
showp :: (Ord s, Show s) => Dict s -> Int -> Pred s -> PP
showp d _ T  = ppa "true"
showp d _ F  = ppa "false"
showp d _ (PVar p)  = ppa p
showp d p (Equal e1 e2)
   = paren p precEq $ ppopen " = " [ppa $ edshow d e1, ppa $ edshow d e2]
showp d p (Atm e) = ppa $ edshow d e
showp d p (PSub pr sub)
   = pplist $ [showp d precSub pr, ppa $ showSub d sub]

showp d p (Comp cname pargs)
 = case plookup cname d of
    Nothing  ->  stdCshow d cname pargs
    Just (PD _ _ showf _) -> showf d pargs

stdCshow d cname pargs
 = pplist [ppa cname, ppclosed "(" ")" "," $ map (showp d 0) pargs]
\end{code}
