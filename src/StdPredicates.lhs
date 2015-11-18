\HDRa{Standard Predicates}\label{ha:std-preds}
\begin{code}
module StdPredicates where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Debug.Trace
import PrettyPrint
import CalcPredicates
\end{code}


\HDRb{Syntax}

We provide dictionary entries that instantiate particular composites
to produce 
a fairly standard UTP predicate language as follows:
\RLEQNS{
   p \in P &::=& \ldots & \mbox{As per \secref{hc:PredData}}
\\ &|& \top & \mbox{(Lattice) Top, a.k.a. miracle}
\\ &|& \bot & \mbox{(Lattice) Bottom, a.k.a. abort/Chaos}
\\ &|& \lnot p  & \mbox{Negation}
\\ &|& p_1 \land p_2 \land \ldots \land p_n  & \mbox{Conjunction}
\\ &|& p_1 \lor p_2 \lor \ldots \lor p_n & \mbox{Disjunction}
\\ &|& p_1 \implies p_2 & \mbox{Implication}
\\ &|& p_1 \refinedby p_2 & \mbox{Refinement}
\\ &|& p_1 \cond{p_2} p_3 & \mbox{Conditional}
\\ &|& \Skip & \mbox{Skip}
\\ &|& p_1 \seq p_2 & \mbox{Sequencing}
\\ &|& p_1 * p_2 & \mbox{Iteration}
}


Our language is a ``while'' language built over a general notion
of atomic state-transformers ($a, \A(a)$), with an added parallel construct.
\begin{eqnarray*}
  p,q ::= Idle | \A(a) | p \lseq q | p\parallel q | p \lcond c q | c \wdo p
\end{eqnarray*}
We shall often use assignments as a convenient wa
 to describe simple atomic actions.

We use $\lseq$, $\lcond{}$ and $\wdo$ here, instead of $;$, $\cond{}$ and $*$
in order to distinguish them from the similar UTP concepts.
In other words, we cannot do the usual UTP trick of modelling language features
like sequential composition or conditional by ``punning'',
because we have to add a lot of control structure to model the parallelism
and interleaving correctly.

First, we build some infrastructure to support a flexible expression and predicate
syntax, with an emphasis on allowing tailored notations
(e.g. writing $ps(in)$ and $ps(in,out)$ rather than $in \in ps$ or $\setof{in,out} \subseteq ps$)
and effective pretty-printing of large complex nested terms.

\newpage
\HDRc{Expression Datatype}

We start by defining an expression space that includes
variables and function applications,
all parameterised by a generic state type:
\begin{code}
data Expr s
 = St s  -- a value of type State
 | B Bool
 | Var String
 | App String [Expr s]
 | Set [Expr s]
 | Sub (Expr s) (Substn s)
 | Undef
 deriving (Eq,Ord,Show)

mkSet :: Ord s => [Expr s] -> Expr s
mkSet = Set . sort . nub

type Substn s = [(String,Expr s)]
mkSub e []  = e
mkSub e sub = Sub e $ sort sub

-- substitutions are sorted for comparison
ssame ::  (Eq s, Ord s) => Substn s -> Substn s -> Bool
ssame sub1 sub2 = sort sub1 == sort sub2
\end{code}
\DRAFT{We shall keep expressions as-is for now,
viewing them atomically as far as highlighting goes.}

\newpage
\HDRc{Predicate Datatype}

Now we need a logic syntax, that has key UTP notations
and the programming language embedded in it
\DRAFT{
 Will completely re-do this replacing tags like
  \texttt{And}, \texttt{Or}, and \texttt{Iter} (say)
 with \texttt{Comp "And"}, \texttt{Comp "Or"} and \texttt{Comp "Iter"}.
}
\begin{code}
data Pred s
 = T
 | F
 | PVar String
 | Equal (Expr s) (Expr s)         -- 5
 | Atm (Expr s)
 | Not (Pred s)                    -- 6
 | And [Pred s]                    -- 4
 | Or [Pred s]                     -- 3
 | Imp (Pred s) (Pred s)       -- 2
 | Cond (Pred s) (Pred s) (Pred s) -- 1
 | PSub (Pred s) (Substn s)        -- 7
 -- UTP
 | Skip
 | Seq (Pred s) (Pred s)           -- 2
 | Iter (Pred s) (Pred s)          -- 6
 | PFun String [Pred s]
 -- Parallel Prog
 | PAtm (Pred s)
 | PIdle
 | PSeq (Pred s) (Pred s)           -- 3
 | PPar (Pred s) (Pred s)           -- 2
 | PCond (Pred s) (Pred s) (Pred s) -- 1
 | PIter (Pred s) (Pred s)          -- 6
 deriving (Eq, Ord, Show)
\end{code}

\newpage
\HDRb{Dictionary}

We need a dictionary that maps various names
to appropriate definitions.

A dictionary entry is a sum of  definition types defined below
\begin{code}
data Entry s
 = FunEntry (FunDef s)
 | AlfEntry AlfDef
 | PVarEntry PVarDef

isFunEntry (FunEntry _) = True
isFunEntry _ = False
isAlfEntry (AlfEntry _) = True
isAlfEntry _ = False
isPVarEntry (PVarEntry _) = True
isPVarEntry _ = False

theFunEntry (FunEntry fd) = fd
theAlfEntry (AlfEntry ad) = ad
thePVarEntry (PVarEntry pd) = pd

type Dict s = M.Map String (Entry s)

flookup :: String -> Dict s -> Maybe (FunDef s)
flookup nm d
 = case M.lookup nm d of
     Just (FunEntry fd)  ->  Just fd
     _                   ->  Nothing

alookup :: String -> Dict s -> Maybe AlfDef
alookup nm d
 = case M.lookup nm d of
     Just (AlfEntry ad)  ->  Just ad
     _                   ->  Nothing

plookup :: String -> Dict s -> Maybe PVarDef
plookup nm d
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

\newpage
Function definitions
\begin{code}
data FunDef s
 = FD [String]                -- list of formal/bound variables
      (Expr s)                 -- definition body
      (Dict s -> [Expr s] -> String)     -- pretty printer
      (Dict s -> [Expr s] -> ( String   -- eval name
                             , Expr s )) -- evaluator

instance Show s => Show (FunDef s) where
  show (FD fvs e _ _) = show fvs ++ " |-> " ++ show e
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"f" |->  (["v1","v2",...,"vn"], e, pf, ev)
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

\newpage
We also want to define alphabets, as sets of names
\begin{code}
type AlfDef = [String]
\end{code}
An entry
\begin{verbatim}
"a" |-> ["v1","v2",..,"vn"]
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

\newpage
We sometimes want to associate extra information with given
predicate variables:
\begin{code}
type PVarDef = [String] -- for now, just its alphabet
\end{code}
An entry
\begin{verbatim}
  "P" |-> ["v1","v2",..,"vn"]
\end{verbatim}
declares the alphabet associated with that predicate variable:
\RLEQNS{
   \alpha P &=&  \setof{v_1,v_2,\ldots,v_n}
}
\newpage
\HDRb{Display}

We define the display of an expression using a dictionary
to provide exceptional ways to render things.
\begin{code}
edshow :: Show s => Dict s -> Expr s -> String
edshow d (St s)     =  show s
edshow d (B b)      =  show b
edshow d (Var v)    =  v
edshow d (Set es)   =  "{" ++ dlshow d "," es ++ "}"
edshow d Undef      =  "Undefined"
edshow d (App f es)
 = case flookup f d of
    Nothing  ->  stdFShow d f es
    Just (FD _ _ showf _) -> showf d es
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

\newpage
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

\newpage
Pretty-printing predicates
\begin{code}
showp :: (Ord s, Show s) => Dict s -> Int -> Pred s -> PP
showp d _ T  = ppa "true"
showp d _ F  = ppa "false"
showp d _ (PVar p)  = ppa p
showp d p (Equal e1 e2)
   = paren p precEq $ ppopen " = " [ppa $ edshow d e1, ppa $ edshow d e2]
showp d p (Not pr)
   = paren p precNot $ pplist [ppa "~", showp d precNot pr]
showp d p (Atm e) = ppa $ edshow d e
showp d p (And []) = ppa "true"
showp d p (And [pr]) = showp d p pr
showp d p (And prs)
   = paren p precAnd $ ppopen " /\\ " $ map (showp d precAnd) prs
showp d p (Or []) = ppa "false"
showp d p (Or [pr]) = showp d p pr
showp d p (Or prs)
 = paren p precOr $ ppopen " \\/ " $ map (showp d precOr) prs
showp d p (Imp pra prc)
    = paren p precImp $ ppopen " => " [ showp d precImp pra
                                    , showp d precImp prc ]
showp d p (Cond c prt pre)
    = paren p precCond $ pplist
                          [ showp d precCond prt
                          , ppa " <| "
                          , showp d 0 c
                          , ppa " |> "
                          , showp d precCond pre ]
showp d p (PSub pr sub)
   = pplist $ [showp d precSub pr, ppa $ showSub d sub]

showp d _ Skip  = ppa "II"
showp d p (Seq pra prc)
    = paren p precSeq $ ppopen " ; " [ showp d precSeq pra
                                    , showp d precSeq prc ]
showp d p (Iter c body)
    = paren p precIter $ ppopen " * " [ showp d precIter c
                                    , showp d precIter body ]
showp d p (PFun fname pargs)
 = pplist [ppa fname, ppclosed "(" ")" "," $ map (showp d 0) pargs]
\end{code}

\newpage
The program constructs:
\begin{code}
showp d p PIdle = ppa "Idle"
showp d p (PAtm pr)
   = pplist [ppa "A(", showp d 0 pr, ppa ")"]

showp d p (PSeq pra prc)
    = paren p precPSeq $ ppopen " ;; " [ showp d precPSeq pra
                                     , showp d precPSeq prc ]
showp d p (PPar pra prc)
    = paren p precPPar $ ppopen " || " [ showp d precPPar pra
                                     , showp d precPPar prc ]
showp d p (PCond c prt pre)
    = paren p precPCond $ pplist
                          [ showp d precCond prt
                          , ppa " <$ "
                          , showp d 0 c
                          , ppa " $> "
                          , showp d precCond pre ]
showp d p (PIter c body)
    = paren p precPIter $ ppopen " <*> " [ showp d precPIter c
                                       , showp d precPIter body ]
\end{code}
