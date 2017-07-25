\HDRa{Root}\label{ha:Root}
\begin{code}
module Root where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import POrd
import CalcPPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
import CalcAlphabets
import CalcSysTypes
import CalcSimplify
import CalcRecogniser
import CalcRun
import DictAbstractions
import StdPredicates
import StdLaws
-- import CalcZipper
-- import CalcSteps
import StdUTPPredicates
import StdUTPLaws
import UTCPCReduce
\end{code}

\begin{code}
import Debug.Trace
rdbg str x = trace (str++show x) x
\end{code}





\newpage
We do a quick run-down of the Commands\cite{conf/popl/Dinsdale-YoungBGPY13}.

\HDRb{Syntax}

\def\Atm#1{\langle#1\rangle}
\def\rr#1{r{\scriptstyle{#1}}}
\def\RR#1{R{\scriptstyle{#1}}}

\begin{eqnarray*}
   a &\in& \Atom
\\ C &::=&
 \Atm a \mid \cskip \mid C \cseq C \mid C+C \mid C \parallel C \mid C^*
\\ g &:& Gen
\\ \ell &:& Lbl
\\ G &::=&  g \mid G_{:} \mid G_1 \mid G_2
\\ L &::=& \ell_G
\end{eqnarray*}

We assign the following precedences to Views syntactical constructs,
interleaving them among the standard predicates.
\begin{code}
precVChc  = 5 + precSpacer  1
precVPar  = 5 + precSpacer  2
precVSeq  = 5 + precSpacer  3
precVIter = 5 + precSpacer  6
\end{code}


\HDRb{Domains}


\HDRc{Rooted Paths}

This Root file is a re-work of the Views semantics
replacing label generators by ``rooted'' label-paths.
Initially we work up some stuff directly in Haskell,
not using the \texttt{Expr} or \texttt{Pred} types.

We start by defining three basic ways to transform a rooted path:
``done'' ($\bullet$);
``split-one'' ($1$);
and ``split-two'' ($2$).
\RLEQNS{
   S &\defs& \setof{1,2}
}
\begin{code}
showConst str _ _ = str  -- constant pretty-printer
evalConst _ = noeval -- constant (non-)evaluator

donen   = "*" ; step   = App donen   []
split1n = "1" ; split1 = App split1n []
split2n = "2" ; split2 = App split2n []

stepEntry
 = ( donen,   ExprEntry [] (showConst donen) noDefn  evalConst noEq )
split1Entry
 = ( split1n, ExprEntry [] (showConst split1n) noDefn evalConst noEq )
split2Entry
 = ( split2n, ExprEntry [] (showConst split2n) noDefn evalConst noEq )

data RootStep = Done | Split1 | Split2 deriving (Eq,Ord)
instance Show RootStep where
 show Done = "*"
 show Split1 = "1"
 show Split2 = "2"
\end{code}

We now define a rooted path as an expression of the form
of the variable $r$ followed by zero or more $S$ transforms,
optionaly finished off with a done marker.
\RLEQNS{
   \sigma,\varsigma &\defs& S^*
\\ R &::=& r\sigma | r\sigma\bullet
}
These have to be expressions as we shall want to substitute for $r$
in them.
\begin{code}
rootn = "r" ; root = Var rootn

rpathn = "R"
rpath rp s = App rpathn [rp, s]
rPath [rp, s] = rpath rp s

rstep rp   =   rpath rp step
rsplit1 rp  =  rpath rp split1
rsplit2 rp  =  rpath rp split2

rpShow d [rp, s] = edshow d rp ++ edshow d s

rpathEntry :: ( String, Entry )
rpathEntry
 = ( rpathn
   , ExprEntry subAny rpShow noDefn (justMakes rPath) noEq )

newtype RootPath = RootPath [RootStep] deriving Eq
instance Show RootPath where
  show (RootPath rs) = 'r':(concat (map show rs))
instance Read RootPath where
  readsPrec _ ('r':rest) = [readPath [] rest]
  readsPrec _ _ = []

readPath path "" = (RootPath $ reverse path,"")
readPath path str@(c:cs)
 | c == '*'   =  readPath (Done:path) cs
 | c == '1'   =  readPath (Split1:path) cs
 | c == '2'   =  readPath (Split2:path) cs
 | otherwise  =  (RootPath $ reverse path,str)
\end{code}


Build the rooted paths dictionary:
\begin{code}
rPathDict :: Dict
rPathDict
 = makeDict
    [ stepEntry
    , split1Entry
    , split2Entry
    , rpathEntry
    ]
\end{code}


\newpage
\HDRc{Set Expressions}

We use sets in two key ways:
checking for membership/subset inclusion;
and updating by removing elements.
\begin{code}
setn = "set"
set = App setn

sngl e = set [e]

emp = set []

mkSet :: [Expr] -> Expr
mkSet = set . sort . nub

showSet d [elm] = edshow d elm
showSet d elms = "{" ++ dlshow d "," elms ++ "}"

-- an alternate way to show a set
flatSet d [] = "."
flatSet d elms = dlshow d "," elms

evalSet _ _ = none

eqSet d es1 es2
 = let ns1 = nub $ sort $ es1
       ns2 = nub $ sort $ es2
   in if all (isGround d) (ns1++ns2)
      then Just (ns1==ns2)
      else Nothing
\end{code}

We want some code to check and analyse both forms of singleton sets:
\begin{code}
isSingleton (App ns es)  =  ns == setn && length es == 1
isSingleton _ = True

-- assumes isSingleton above
theSingleton (App _ es)  =  head es
theSingleton e           =  e
\end{code}


\HDRd{Set Membership/Subset}\label{hd:membership}~

This is complicated by the fact we interpret
non-set expressions as singleton sets,
so $x \subseteq y$ when both are not sets
is considered to be $\setof x \subseteq \setof  y$
(which of course is really $x=y$).
\begin{code}
subsetn = "subset"
subset e set = App subsetn [e,set]
evalSubset d [App "set" es1,App "set" es2] = dosubset d es1 es2
evalSubset d [es1,App "set" es2] = dosubset d [es1] es2
evalSubset d [App "set" es1,es2] = dosubset d es1 [es2]
evalSubset d [es1,es2] = dosubset d [es1] [es2]
evalSubset _ _ = none
dosubset d es1 es2 -- is es1 a subset of es2 ?
  | null es1lesses2  =  ( "subset", B True )
  | all (isGround d) (es1lesses2 ++ es2)
                     =  ( "subset", B False )
  | otherwise        =  none
  where
    es1lesses2 = es1 \\ es2

-- the following should be re-located
matchls (App ns [ ell, Var "ls" ])
 | ns == subsetn  =  (True, ell)
matchls _  =  (False, error "not an ls(..)")
\end{code}

Set binary operator precedence ordering,
loosest to tightest:
$\cup,\cap,\setminus$.
\begin{code}
-- expression precedences not supported yet!
precUnion = precSpacer  11
precIntsc = precSpacer  12
precSDiff = precSpacer  13
\end{code}

\HDRd{Set Binary Operators}\label{hd:set-binops}~

\begin{code}
unionn = "U"
u s1 s2 = App unionn [s1,s2]
evalUnion d [App "set" es1,App "set" es2] = dounion d es1 es2
evalUnion d [es1,App "set" es2] = dounion d [es1] es2
evalUnion d [App "set" es1,es2] = dounion d es1 [es2]
evalUnion d [es1,es2] = dounion d [es1] [es2]
evalUnion _ _ = none
dounion d es1 es2
  | all (isGround d) es1es2  =  ( "union", mkSet es1es2 )
  | otherwise        =  none
  where
    es1es2 = es1 ++ es2
ppUnion d ss = "("  ++ dlshow d " U " ss ++ ")"
\end{code}

\begin{code}
intn = "I"
i s1 s2 = App intn [s1,s2]
evalIntsct d [App "set" es1,App "set" es2] = dointsct d es1 es2
evalIntsct d [es1,App "set" es2] = dointsct d [es1] es2
evalIntsct d [App "set" es1,es2] = dointsct d es1 [es2]
evalIntsct d [es1,es2] = dointsct d [es1] [es2]
evalIntsct _ _ = none
dointsct d es1 es2
  | all (isGround d) es1es2  =  ( "intersect", mkSet es1es2 )
  | otherwise        =  none
  where
    es1es2 = es1 `intersect` es2
ppIntsct d ss = "("  ++ dlshow d " I " ss ++ ")"
\end{code}


\begin{code}
sdiffn = "\\"
sdiff s1 s2 = App sdiffn [s1,s2]
evalSDiff d [App "set" es1,App "set" es2] = dosdiff d es1 es2
evalSDiff d [es1,App "set" es2] = dosdiff d [es1] es2
evalSDiff d [App "set" es1,es2] = dosdiff d es1 [es2]
evalSDiff d [es1,es2] = dosdiff d [es1] [es2]
evalSDiff _ _ = none
dosdiff d es1 es2
  | all (isGround d) es1es2  =  ( "setminus", mkSet es1es2 )
  | otherwise        =  none
  where
    es1es2 = es1 \\ es2
ppSDiff d ss = "("  ++ dlshow d " \\ " ss ++ ")"
\end{code}

\HDRd{Set Utilities}

It can be useful to turn a set into a list
of its elements:
\begin{code}
setElems :: Expr -> [Expr]
setElems (App sn es) | sn == setn  =  sort $ nub $ es
setElems e = []
\end{code}
Also determining subsets (subsequences)
\begin{code}
isSubSeqOf [] _ = True
isSubSeqOf _ [] = False
isSubSeqOf a@(x:a') (y:b) | x==y       =  isSubSeqOf a' b
                          | otherwise  =  isSubSeqOf a  b
\end{code}
From GHC 7.10 onwards this is \texttt{Data.List.subSequencesOf}.

\HDRb{Shorthands}

We support a shorthand (that views a set as its own collection
of corresponding $n$-ary characteristic functions)
that denotes $x \in S$ by $S(x)$ and $ X \subseteq S$ by $S(X)$,
and omits $\{$ and $\}$ from around enumerations when context makes
it clear a set is expected

\begin{eqnarray*}
   ls(\ell) &\defs& \ell \in ls
\\ ls(L) &\defs& L \subseteq ls
\\ ls(\B\ell) &\defs& \ell \notin ls
\\ ls(\B L) &\defs& L \cap ls = \emptyset
\end{eqnarray*}

\begin{code}
showSubSet d [App "set" elms,App "set" [set]]
 = edshow d set ++ "(" ++ dlshow d "," elms ++ ")"
showSubSet d [App "set" elms,set]
 = edshow d set ++ "(" ++ dlshow d "," elms ++ ")"
showSubSet d [e,set]
 = edshow d set ++ "(" ++ edshow d e ++ ")"
\end{code}

\HDRd{Set Swapping}

We update a set by removing some elements
and replacing them with new ones:
\RLEQNS{
   A \ominus (B,C) &\defs& (A \setminus B) \cup C
}
\begin{code}
sswapn = "sswap"
sswap start old new = App sswapn [start,old,new]
showSSwap d [start,old,new]
 = edshow d start
   ++ " (-/+) ("
   ++ edshow d old
   ++ ","
   ++ edshow d new
   ++ ")"

evalSSwap d args@[starts,olds,news]
 | all (isGround d) args
 = setswap (setify starts) (setify olds) (setify news)
evalSSwap _ _ = none
setify (App "set" es) = es
setify e        = [e]
setswap starts olds news
                   = ("sswap", mkSet ((starts\\olds)++news))
\end{code}

The Set Dictionary:
\begin{code}
vSetDict :: Dict
vSetDict
 = makeDict
    [ (setn,(ExprEntry subAny showSet noDefn evalSet eqSet))
    , (unionn,(ExprEntry subAny ppUnion noDefn evalUnion noEq))
    , (intn,(ExprEntry subAny ppIntsct noDefn evalIntsct noEq))
    , (sdiffn,(ExprEntry subAny ppSDiff noDefn evalSDiff noEq))
    , (subsetn,(ExprEntry subAny showSubSet noDefn evalSubset noEq))
    , (sswapn, (ExprEntry subAny showSSwap noDefn evalSSwap noEq))
    ]
\end{code}



\HDRc{The Expression Dictionary}\label{hc:Root-expr-dict}

\begin{code}
dictVE :: Dict
dictVE = rPathDict `dictMrg` vSetDict
\end{code}


\newpage
\HDRb{Alphabet}

\begin{eqnarray*}
   s, s' &:& \mathcal S
\\ ls, ls' &:& \mathcal P (R)
\\ r &:& R
\end{eqnarray*}

\begin{code}
s   = Var "s"  ; s'  = Var "s'"
ls  = Var "ls" ; ls' = Var "ls'"
r   = Var "r"
\end{code}

We define our dictionary alphabet entries,
and also declare that the predicate variables $a$, $b$ and $c$
will refer to atomic state-changes,
and so only have alphabet $\setof{s,s'}$.
\begin{code}
vStatic = ["r"]
vDynamic = ["ls","ls'","s","s'"]
vObs = vDynamic ++ vStatic
ss' = ["s", "s'"]

vAlfDict
 = dictMrg dictAlpha dictAtomic
 where
   dictAlpha = stdAlfDictGen ["s"] ["ls"] vStatic
   dictAtomic = mergeDicts
                $ map snd [ pvarEntry "a" ss'
                          , pvarEntry "b" ss'
                          , pvarEntry "c" ss' ]
\end{code}

\newpage
\HDRb{``Standard'' UTP Constructs}

\begin{eqnarray*}
   P \cond c Q
   &\defs&
   c \land P \lor \lnot c \land Q
\\ P ; Q
   &\defs&
   \exists s_m,ls_m \bullet P[s_m,ls_m/s',ls'] \land Q[s_m,ls_m/s,ls]
\\ c * P
   &=&
   P ; c * P \cond c \Skip
\end{eqnarray*}

We need to update some definitions from standard UTP as follows:

\HDRd{Updating UTP Skip ($\Skip$)}\label{hd:updating-UTP-II}

We know have a concrete definition for $\Skip$,
as well as a known alphabet.
\RLEQNS{
   \Skip &=& ls'=ls \land s'=s
\\ \alpha \Skip &=& \setof{ls,ls',s,s'}
}
\begin{code}
defnSkip d _ = ldefn shSkip $ mkAnd [Equal ls' ls, Equal s' s]

skipEntry' -- in stdUTPDict
  = ( nSkip
     , (snd skipEntry){ alfa = ["ls","ls'","s","s'"]
                      , pdefn = defnSkip } )
\end{code}

\HDRd{Updating Sequential Composition Printing}

\HDRd{Updating the Standard UTP Dictionary}~

\begin{code}
vStdUTPDict :: Dict
vStdUTPDict
  = makeDict [ skipEntry -- don't want to expand such defns
             ] `dictMrg` stdUTPDict
\end{code}

\newpage
\HDRb{WwW Basic Shorthands}

Atomic actions have a basic behaviour that is described by
\[
ls(E) \land s' \in \sem a s \land ls' = (ls\setminus E) \cup N
\]
where $E$ is the set of necessary enabling labels,
$a$ is a relation over shared state,
and $N$ is the set of new labels deposited upon completion.
We shall abstract the above as
\[
A(E|a|N)
\]
There is a slightly more general form that removes labels
that may differ from those doing the enabling:
\[
ls(E) \land s' \in \sem a s \land ls' = (ls\setminus R) \cup A
\]
where $R$ and $A$ are sets of labels respectively removed, then added
on the action is complete.
We abstract this as
\[
  X(E|a|R|A)
\]
and note that
\[
  A(E|a|N) = X(E|a|E|N).
\]


\HDRc{Generic Atomic Behaviour}

\begin{eqnarray*}
   X(E|a|R|A)
   &\defs&
   ls(E) \land [a] \land ls'=(ls\setminus R)\cup A
\end{eqnarray*}

\begin{code}
nX = "X"
isX (_,Comp n [_,_,_,_]) | n==nX = True; isX _ = False

mkX e act r a  = Comp nX [Atm e, act, Atm r, Atm a]

pFlatShow d (Atm (App ns es))
 | ns == setn  = flatSet d es
pFlatShow d (Atm e) = flatSet d [e]
pFlatShow _ _ = "?"

ppX sCP vd p prs@[e,act,r,a]
 = ppclosed "X(" ")" "|"
    [ ppa $ pFlatShow vd e
    , sCP 0 2 act
    , ppa $ pFlatShow vd r
    , ppa $ pFlatShow vd a ]
ppX _ _ _ _ = pps styleRed $ ppa ("invalid-"++nX)

-- we don't want to expand the definition of this
defnX = pNoChg nX
\end{code}

We do want the following simplification:
\begin{eqnarray*}
  X(E|a|E|N) &=& A(E|a|N)
\end{eqnarray*}
\begin{code}
simpX vd [ (Atm e1)   -- E
         , as         -- a
         , (Atm e2)   -- E?
         , (Atm n) ]  -- N
  | psimp vd (Equal e1 e2) /= T  =  Nothing
  | otherwise  =  Just ( "X-is-A", mkA e1 as n, diff )
\end{code}

Now, put it all together
\begin{code}
vXEntry :: (String, Entry)
vXEntry
 = ( nX
   , PredEntry vStatic ppX vObs defnX simpX )
\end{code}

\begin{eqnarray*}
   A(E|a|N)
   &\defs&
   X(E|a|E|N)
\end{eqnarray*}

\begin{code}
nA = "A"
isA (Comp n [_,_,_]) | n==nA = True; isA _ = False

mkA e act n  = Comp nA [Atm e, act, Atm n]

ppA sCP vd p mprs@[e,act,n]
 = ppclosed "A(" ")" "|"
    [ ppa $ pFlatShow vd e
    , sCP 0 2 act
    , ppa $ pFlatShow vd n ]
ppA _ _ _ _ = pps styleRed $ ppa ("invalid-"++nA)

-- we don't want to expand the definition of this, or simplify it
defnA = pNoChg nA
simpA = pNoChg nA

vAEntry :: (String, Entry)
vAEntry
 = ( nA
   , PredEntry vStatic ppA vObs defnA simpA )
\end{code}


\newpage
\HDRc{Coding Label-Set Invariants}

We have a key invariant as part of the healthiness
condition associated with every semantic predicate,
namely that the labels $r$ and $\rr\bullet$ never occur in  $ls$ at
the same time:
\[
 ( r \in ls \implies \rr\bullet \notin ls )
 \land
 ( \rr\bullet \in ls \implies r \notin ls )
\]
This is the Label Exclusivity invariant.

Given the way we shall use substitution of $r$ by
other rooted paths, for sub-components,
we shall see that we will get a number of instances of this.
We adopt a shorthand notation,
so that the above invariant is simply
\[
  [r|\rr\bullet]
\]
So we define the following general shorthand:
\RLEQNS{
   ~[L_1|L_2|\dots|L_n]
   &\defs&
   \forall_{i,j \in 1\dots n}
    @
    i \neq j \implies
     ( L_i \cap ls \neq \emptyset \implies L_j \cap ls = \emptyset )
\\ \multicolumn{3}{c}{\elabel{short-lbl-exclusive}}
}
What needs to be kept in mind regarding this shorthand notation
is that $ls$ is mentioned under the hood,
and it is really all about what can be present in the global label-set
at any instant in time.

We refer to the $L$ above as \texttt{LESet},
and use \texttt{LEInv} to denote the full invariant.
We start with the ``LE-sets'', as expressions
\begin{code}
nLESet = "LESet"

leSet es = App nLESet es
leElem e = leSet [e]

isLESet (Comp n _)
 | n == nLESet  =  True
 | otherwise    =  False

showLESet d [] = ""
showLESet d [e] = edshow d e
showLESet d (e:es) = edshow d e ++ ',':showLESet d es

vLESetEntry :: (String, Entry)
vLESetEntry
 = ( nLESet
   , ExprEntry subAny showLESet noDefn (justMakes leSet) noEq )
\end{code}

\newpage
We then move onto the ``LE-invariant'', as predicates
\begin{code}
nLEInv = "LEInv"

leInv es = Comp nLEInv $ map liftLE es
liftLE e@(App nm _)
 | nm == nLESet  =  Atm e
liftLE e         =  Atm $ leElem e

isLEInv (Comp n es)
 | n == nLEInv  =  all isLESet es
 | otherwise    =  False

precInv = -1

ppLEInv sCP d p prs
 = ppclosed "[" "]" "|" $ map (sCP precInv 1) prs

vLEInvEntry :: (String, Entry)
vLEInvEntry
 = ( nLEInv
   , PredEntry anyVars ppLEInv vStatic (pNoChg nLEInv) (pNoChg nLEInv) )
\end{code}

Now, we need to define invariant satisfaction.
Our invariant applies to $A$ and $X$ atomic actions:
\RLEQNS{
   A(E|a|N) \textbf{ sat } I
   &\defs&
   E \textbf{ lsat } I \land N \textbf{ lsat } I
\\ X(E|a|R|A)  \textbf{ sat } I
   &\defs&
   E \textbf{ lsat } I \land A \textbf{ lsat } I
}
\begin{code}
labelSetInv :: InvChecker
labelSetInv d inv pr@(Comp nm [Atm e,_,Atm n])
 | nm == nA = labelSetReport( lsat d e inv
                            , lsat d n inv )
labelSetInv d inv pr@(Comp nm [Atm e,_,_,Atm a])
 | nm == nX = labelSetReport( lsat d e inv
                            , lsat d a inv )
labelSetInv _ _ _ = Nothing

labelSetReport (rep1, rep2)  =  Just (rep1 && rep2)
\end{code}

\newpage
Now we have to code up \textbf{lsat}:
\RLEQNS{
   \textbf{lsat}_S [L_1|\dots|L_n]
   &\defs&
   \#(filter ~\textbf{lsat'}_S \seqof{L_1,\ldots,L_n}) < 2
\\ \textbf{lsat'}_S \setof{\ell_1,\dots,\ell_n}
  &\defs&
  \exists i @ \textbf{lsat''}_S \ell_i
\\ \textbf{lsat''}_S \ell &\defs& \ell \in S
}
\begin{code}
lsat :: Dict -> Expr -> Pred -> Bool
lsat d lset (Comp nm ells)
 | nm == nLEInv
   = case filter (lsat' d lset) ells of
      []   ->  True
      [_]  ->  True
      _    ->  False
 | otherwise  =  False
lsat _ _ _ = False

lsat' :: Dict -> Expr -> Pred -> Bool
lsat' d lset (Atm (App nm lse))
 | nm == nLESet  =  any (lsat'' d lset) lse
 | otherwise     =  False
lsat' _ _ _      =  False

lsat'' :: Dict -> Expr -> Expr -> Bool
lsat'' d lset ell
 = case esimp d $ subset ell lset of
      (_,B b)  ->  b
      _        ->  False -- no occupancy!
\end{code}


\HDRc{Invariant Trimming}

We can use the invariant to trim removal sets,
given an enabling label or label-set.
\RLEQNS{
   I \textbf{ invTrims } X(E|a|E,L|A)
   &\defs&
   \lnot(\setof{E,L} \textbf{ lsat } I)
}
We need a function that establishes when the invariant is not satisfies
for at least one invariant in a supplied list.
\begin{code}
someInvFails :: Dict
             -> [Pred]  -- Invariants
             -> Expr  -- enable label being removed
             -> Expr  -- other label being removed
             -> Bool
someInvFails d invs ena other = findFail (set [ena,other]) invs
 where
   findFail lpair []          =  False
   findFail lpair (inv:invs)
    | not $ lsat d lpair inv  =  True
    | otherwise               =  findFail lpair  invs
\end{code}

\newpage
\HDRc{Wheels within Wheels}\label{hc:WwW}

The wheels-within-wheels healthiness condition
insists that $r$ and $\rr\bullet$ are never simultaneously in
the label-set $ls$,
and that our semantic predicates are closed under mumbling.
\RLEQNS{
   \W(C)
   &\defs&
   [r|\rr\bullet] \land \left(~\bigvee_{i\in 0\dots} C^i~\right)
\\ ii &\defs& s'=s
}
We will code a version that keeps the top-level invariant out of the picture,
\begin{code}
nW = "W"
isW (Comp n [_]) | n==nW = True; isW _ = False

mkW pr  = Comp nW [pr]

ppW sCP vd p [pr]
 = ppclosed "W(" ")" "" [ sCP 0 1 pr ]
ppW _ _ _ _ = pps styleRed $ ppa ("invalid-"++nW)

r' = rstep r
invWWW = leInv [r,r']

-- we don't want to expand the definition of this
defnW = pNoChg nW
\end{code}

We want to simplify $\W$ with the obvious generalisation of the following
``nested $\W$-absorption'' law:
\RLEQNS{
  \W(P \lor \W(Q)) &=& \W(P \lor Q)
}
as well as the ``$\W-\Skip$ absorption law''
\RLEQNS{
  \W(\Skip \lor P) &=& \W(P)
}
\begin{code}
simpW d [pr]  =  case deepUnwrap nOr mkOr nW nSkip pr of
                  Nothing   ->  Nothing
                  Just pr'  ->  Just ( "nested W-absorption"
                                     , mkW pr'
                                     , True                  )
simpW _ _ = Nothing
\end{code}

Now, the dictionary entry
\begin{code}
vWEntry :: (String, Entry)
vWEntry
 = ( nW
   , PredEntry ["r"] ppW vObs defnW simpW )
\end{code}

\newpage
Unrolling $\W(C)$, using $I$ for $[r|\rr\bullet]$,
and noting that
$
\bigvee_{i \in \Nat} C^i
= \Skip \lor (C\seq\bigvee_{i \in \Nat} C^i)
$.
\RLEQNS{
   \W(C) &=& I \land \bigvee C^i
\\ &=& I \land (\Skip \lor C\seq\bigvee C^i)
\\ &=& I \land (\Skip \lor C\seq((\Skip \lor C\seq\bigvee C^i)))
\\ &=& I \land (\Skip \lor C \lor C^2\seq\bigvee C^i)
\\ &=& I \land (\Skip \lor C \lor C^2\seq((\Skip \lor C\seq\bigvee C^i)))
\\ &=& I \land (\Skip \lor C \lor C^2 \lor C^3\seq\bigvee C^i)
\\ &\vdots&
\\ &=& I \land (\Skip \lor C \lor \dots C^{k-1} \lor C^k\seq\bigvee C^i)
\\ &=& I \land (~(\bigvee_{i < k} C^i) \lor (\bigvee_{i \geq k} C^i)~)
}
We assume $\seq$ binds tighter than $\lor$.
\begin{code}
wUnroll :: String -> RWFun
-- to be re-done properly if ever it is required
-- wUnroll arg d _ wpr@(Comp nw [pr])
--  | nw == nW
--    = case numfrom arg of
--       0 -> Just ( "W-unroll"
--                 , mkSeq (mkOr [mkSkip, pr]) wpr , True )
--       n -> Just ( "W-unroll."++arg
--                 ,  wunroll n
--                 , True )
--
--  where
--    numfrom "" = 0
--    numfrom (c:_) | isDigit c = digitToInt c
--                  | otherwise = 42
--
--    wunroll n = mkOr (mkSkip : dupPr pr n)
--    dupPr dups 0 = []
--    dupPr dups n = dups : dupPr (mkSeq dups pr) (n-1)

wUnroll _ _ _ _ = Nothing
\end{code}

\newpage
\HDRb{WwW Semantic Definitions}

The definitions, using the new shorthands:
\RLEQNS{
   \W(C) &\defs& \left(\bigvee_{i\in 0\dots} C^i\right)
\\ ii &\defs& s'=s
\\
\\ \Atm a &\defs&\W(A(r|a|\rr\bullet))
\\
\\ \cskip
   &\defs&
   \Atm{ii}
}
The following are all under review (they lack sufficient invariants).
\RLEQNS{
   C \cseq D
   &\defs&
   \W(~    A(r|ii|\rr1)
      \lor C[\rr1/r]
      \lor A(\rr{1\bullet}|ii|\rr2)
      \lor D[\rr2/r]
      \lor A(\rr{2\bullet}|ii|\rr\bullet) ~)
\\
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(r|ii|\rr1) \lor A(r|ii|\rr2)
\\ && \qquad {} \lor
   C[\rr1/r] \lor D[\rr2/r]
\\ && \qquad {} \lor A(\rr{1\bullet}|ii|\rr\bullet) \lor A(\rr{2\bullet}|ii|\rr\bullet) ~)
\\
\\ C \parallel D
   &\defs&
   \W(\quad\phlor A(r|ii|\rr1,\rr2)
\\ && \qquad {}\lor
   C[\rr1/r]
   \lor D[\rr2/r]
\\ && \qquad {}\lor
   A(\rr{1\bullet},\rr{2\bullet}|ii|\rr\bullet)~)
\\
\\ C^*
   &\defs&
   \W(\quad  \phlor A(r|ii|\rr1) \lor A(\rr1|ii|\rr\bullet)
\\ && \qquad {}\lor C[\rr1/r]    \lor A(\rr{1\bullet}|ii|\rr1) ~)
}

\newpage
\HDRc{Coding Atomic Semantics}

\RLEQNS{
   \Atm a &\defs&\W(A(r|a|\rr\bullet))
}

\begin{code}
nAtom = "Atom" -- internal abstract name
isAtom (Comp n [_]) | n==nAtom = True; isAtom _ = False

atom pr = Comp nAtom [pr]

ppAtom sCP d p [pr] = ppbracket "<" (sCP 0 1 pr) ">"
ppAtom _ _ _ _ = pps styleRed $ ppa ("invalid-"++nAtom)

defnAtom d [a] = ldefn nAtom $ wp $ mkA r a r'

wp x = Comp "W" [x]

vAtmEntry :: (String, Entry)
vAtmEntry
 = ( nAtom
   , PredEntry ["s","s'"] ppAtom [] defnAtom (pNoChg nAtom) )
\end{code}

Calculation on $\Atm a$ results in $\Skip \lor A(r|a|\rr\bullet)$,
so we add a variant dictionary entry:
\begin{code}
defnAtomCalc d [a]
 = ldefn (nAtom++" calculation")
         $ mkOr [mkSkip, mkA r a r']

vAtmCalcEntry :: (String, Entry)
vAtmCalcEntry
 = ( nAtom
   , PredEntry ["s","s'"] ppAtom [] defnAtomCalc (pNoChg nAtom) )
\end{code}


\newpage
\HDRc{Coding Skip}

\RLEQNS{
   ii &\defs& s'=s
\\ \cskip
   &\defs&
   \Atm{ii}
}
\begin{code}
nVSkip = "VSkip" -- internal abstract name
isVSkip (_,Comp n []) | n==nVSkip = True; isVSkip _ = False

vskip  = Comp nVSkip []

ppVSkip d ms p [] = ppa "<skip>"
ppVSkip d ms p mprs = pps styleRed $ ppa ("invalid-"++nVSkip)

defnVSkip d [] = ldefn nVSkip $ wp $ mkA r ii r'

invVSkip = leInv [leElem r, leElem r']

vSkipEntry :: (String, Entry)
vSkipEntry
 = ( nVSkip
   , PredEntry ["s","s'"] ppVSkip [] defnVSkip (pNoChg nSkip) )

-- atomic skip
nii = "ii"
ii = PVar nii
ppii d ms p [] = ppa nii

iiCalcEntry :: (String, Entry)
iiCalcEntry
 = ( nii
   , PredEntry [] ppii ss' (pNoChg nii) (pNoChg nii) )
\end{code}
The calculation of $\Atm{ii}$ also leads us to the following calculation
for \verb"<skip>": $\Skip \lor A(r|ii|r')$,
so we add a variant dictionary entry:
\begin{code}
defnVSkipCalc d []
 = ldefn (nVSkip++" calculation")
         $ mkOr [mkSkip, mkA r ii r']

vSkipCalcEntry :: (String, Entry)
vSkipCalcEntry
 = ( nVSkip
   , PredEntry ["s","s'"] ppVSkip [] defnVSkipCalc (pNoChg nAtom) )
\end{code}





\newpage
\HDRc{Coding Sequential Composition}

\RLEQNS{
   C \cseq D
   &\defs& [r|\rr1|\rr{1\bullet}|\rr2|\rr{2\bullet}|\rr\bullet] \land {}
\\ && \W(\quad {}\phlor A(r|ii|\rr1)
\\ && \qquad {} \lor C[\rr1/r]
\\ && \qquad {} \lor A(\rr{1\bullet}|ii|\rr2)
\\ && \qquad {} \lor D[\rr2/r]
\\ && \qquad {} \lor A(\rr{2\bullet}|ii|\rr\bullet)~)
}
Ignoring invariants for now.
\begin{code}
nVSeq = "VSeq"
isVSeq (Comp n [_,_]) | n==nVSeq = True; isVSeq _ = False

vseq p q = Comp nVSeq [p,q]

shVSeq = ";;"
ppVSeq sCP d p [pr1,pr2]
 = paren p precVSeq
     $ ppopen  (pad shVSeq) [ sCP precVSeq 1 pr1
                            , sCP precVSeq 2 pr2 ]
ppVSeq _ _ _ _ = pps styleRed $ ppa ("invalid-"++shVSeq)

r1 = rsplit1 r
r1' = rstep r1
r2 = rsplit2 r
r2' = rstep r2

invVSeq = leInv [r,r1,r1',r2,r2',r']

pSeq p q
 = mkOr [ mkA r ii r1
        , PSub p [("r",r1)]
        , mkA r1' ii r2
        , PSub q [("r",r2)]
        , mkA r2' ii r' ]

defnVSeq d [p,q] = ldefn shVSeq $ wp $ pSeq p q
vSeqEntry :: (String, Entry)
vSeqEntry
 = ( nVSeq
   , PredEntry [] ppVSeq [] defnVSeq (pNoChg nVSeq) )
\end{code}


\newpage
\HDRc{Coding (Non-Det.) Choice}

\RLEQNS{
   C + D
   &\defs& [r|\rr1|\rr{1\bullet}|\rr2|\rr{2\bullet}|\rr\bullet] \land {}
\\&& \W(\quad {}\phlor A(r|ii|\rr1) \lor A(r|ii|\rr2)
\\ && \qquad {} \lor
   C[\rr1/r] \lor D[\rr2/r]
\\ && \qquad {} \lor A(\rr{1\bullet}|ii|\rr\bullet) \lor A(\rr{2\bullet}|ii|\rr\bullet) ~)
}
Ignoring invariants for now.
\begin{code}
nVChc = "VChc"
isVChc (Comp n [_,_]) | n==nVChc = True; isVChc _ = False

vchc p q = Comp nVChc [p,q]

shVChc = "+"
ppVChc sCP d p [pr1,pr2]
 = paren p precVChc
     $ ppopen  (pad shVChc) [ sCP precVChc 1 pr1
                            , sCP precVChc 2 pr2 ]
ppVChc _ _ _ _ = pps styleRed $ ppa ("invalid-"++shVChc)

invVChc = invVSeq -- not a complete coincidence !

pChc p q
 = mkOr [ mkA r ii r1
        , mkA r ii r2
        , PSub p [("r",r1)]
        , PSub q [("r",r2)]
        , mkA r1' ii r'
        , mkA r2' ii r' ]

defnVChc d [p,q]
 = ldefn shVChc $ wp $ pChc p q

vChcEntry :: (String, Entry)
vChcEntry
 = ( nVChc
   , PredEntry [] ppVChc [] defnVChc (pNoChg nVChc) )
\end{code}


\newpage
\HDRc{Coding Parallel Composition}

\RLEQNS{
   C \parallel D
   &\defs& ~
   [r|\rr1,\rr2,\rr{1\bullet},\rr{2\bullet}|\rr\bullet] \land
   [\rr1|\rr{1\bullet}] \land
   [\rr2|\rr{2\bullet}] \land {}
\\&& \W(\quad\phlor A(r|ii|\rr1,\rr2)
\\ && \qquad {}\lor
   C[\rr1/r]
   \lor D[\rr2/r]
\\ && \qquad {}\lor
   A(\rr{1\bullet},\rr{2\bullet}|ii|\rr\bullet)~)
}
Ignoring invariants for now.
\begin{code}
nVPar = "VPar"
isVPar (Comp n [_,_]) | n==nVPar = True; isVPar _ = False
--
vpar p q = Comp nVPar [p,q]
--
shVPar = "||"
ppVPar sCP d p [pr1,pr2]
 = paren p precVPar
     $ ppopen  (pad shVPar) [ sCP precVPar 1 pr1
                            , sCP precVPar 2 pr2 ]
ppVPar _ _ _ _ = pps styleRed $ ppa ("invalid-"++shVPar)
--

invVPar1 = leInv [r,leSet [r1,r2,r1',r2'], r']
invVPar2 = leInv [r1,r1']
invVPar3 = leInv [r2,r2']

invVPars = [ invVPar1, invVPar2, invVPar3 ]

invVPar = mkAnd invVPars

pPar p q
 = mkOr [ mkA r ii (set [r1,r2])
           , PSub p [("r",r1)]
           , PSub q [("r",r2)]
           , mkA (set [r1',r2']) ii r' ]

defnVPar d [p,q]
 = ldefn shVPar $ wp $ pPar p q

vParEntry :: (String, Entry)
vParEntry
 = ( nVPar
   , PredEntry [] ppVPar [] defnVPar (pNoChg nVPar) )
\end{code}

\newpage
\HDRc{Coding Iteration}

\RLEQNS{
   C^*
   &\defs& [r|\rr2|\rr1|\rr{1\bullet}|\rr\bullet] \land {}
\\&& \W(\quad  \phlor A(r|ii|\rr2)
\\ && \qquad {}\lor A(\rr2|ii|\rr1)
               \lor C[\rr1/r]
               \lor A(\rr{1\bullet}|ii|\rr2)
\\ && \qquad {}\lor A(\rr2|ii|\rr\bullet) ~)
}
Ignoring invariants for now.
\begin{code}
nVIter = "VIter"
isVIter (Comp n [_]) | n==nVIter = True; isVIter _ = False
--
viter p = Comp nVIter [p]
--
shVIter = "*"
ppVIter sCP d p [pr]
 = paren p precVIter
     $ ppclosed  "(" ")*" "" [sCP 0 1 pr]

ppVIter _ _ _ _ = pps styleRed $ ppa ("invalid-"++shVIter)

invVIter = leInv [r,r2,r1,r1',r']

pIter p
 = mkOr [ mkA r ii r2
        , mkA r2 ii r1
        , PSub p [("r",r1)]
        , mkA r1' ii r2
        , mkA r2 ii r' ]

defnVIter d [p]
 = ldefn shVIter $ wp $ pIter p

vIterEntry :: (String, Entry)
vIterEntry
 = ( nVIter
   , PredEntry [] ppVIter [] defnVIter (pNoChg nVIter) )
\end{code}



\newpage
\HDRc{The Predicate Dictionary}\label{hc:Root-pred-dict}

\begin{code}
dictVP, dictVPCalc :: Dict
dictVP = makeDict [ vXEntry
                  , vAEntry
                  , vWEntry
                  , vLESetEntry
                  , vLEInvEntry
                  -- , vIElemEntry
                  -- , vIDisjEntry
                  -- , vIJoinEntry
                  , vAtmEntry
                  , vSkipEntry
                  , iiCalcEntry
                  , vSeqEntry
                  , vChcEntry
                  , vParEntry
                  , vIterEntry
                  ]

dictVPCalc = makeDict [ vAtmCalcEntry
                      , vSkipCalcEntry
                      ]
\end{code}



\HDRb{Reductions for WWW}\label{hb:Root-reduce}

\HDRc{Recognisers for WWW}\label{hc:v-recog}

\RLEQNS{
   ls'=ls\ominus(S_1,S_2)
   &\rightsquigarrow&
   \seqof{S_1,S_2}
   & \ecite{sswap-$;$-prop.}
}
\begin{code}
mtchLabelSetSSwap :: Recogniser
mtchLabelSetSSwap (Equal v' (App nm [v, s1, s2]))
 | v == ls && v' == ls'  =  Just [Atm s1, Atm s2]
mtchLabelSetSSwap _      =  Nothing
\end{code}

\newpage
\HDRc{\texttt{vReduce}}\label{hc:vReduce}

\begin{code}
vReduce :: RWFun
        -- Dict
        -- -> [Pred]  -- Invariants
        -- -> Pred    -- Target Predicate
        -- -> Maybe (String, Pred, Bool)
\end{code}



\newpage
\HDRd{$A$ then $A$}

\RLEQNS{
  && A(E_1|a|N_1) \seq A(E_2|b|N_2)
\EQ{proof in Views.tex }
\\&& X(E_1 \cup (E_2\setminus N_1)
       |a\seq b
       |E_1 \cup E_2
       |N_1 \setminus E_2 \cup  N_2)
       \land (E_2\setminus N_1) \cap E_1 = \emptyset
}
\begin{code}
vReduce vd _ (Comp ns [ (Comp na1 [ (Atm e1)    -- A(E1
                                , as          --  |a
                                , (Atm n1) ]) --  |N1)
                    , (Comp na2 [ (Atm e2)    -- A(E2
                                , bs          --  |b
                                , (Atm n2) ]) --  |N2)
                    ])
 | ns == nSeq && na1 == nA && na2 == nA
   =  lred "A-then-A"
       $ mkAnd [ mkX e' abs r' n'
               , Equal (e2ln1 `i` e1) emp]
 where
   e2ln1 = snd $ esimp vd (e2 `sdiff` n1)
   e'  = snd $ esimp vd (e1 `u` e2ln1)
   abs = mkSeq as bs
   r'  = snd $ esimp vd (e1 `u` e2)
   n'  = snd $ esimp vd ((n1 `sdiff` e2) `u` n2)
\end{code}


\newpage
\HDRd{$X$ then $A$}

\RLEQNS{
  && X(E_1|a|R_1|A_1) \seq A(E_2|b|N_2)
\EQ{proof in Views.tex }
\\&& X(E_1 \cup (E_2\setminus A_1)
       |a\seq b
       |R_1 \cup E_2
       |A_1 \setminus E_2 \cup  N_2)
       \land (E_2\setminus A_1) \cap R_1 = \emptyset
}
\begin{code}
vReduce vd _ (Comp ns [ (Comp nx1 [ (Atm e1)    -- X(E1
                                , as          --  |a
                                , (Atm r1)    --  |R1
                                , (Atm a1) ]) --  |A1)
                    , (Comp na2 [ (Atm e2)    -- A(E2
                                , bs          --  |b
                                , (Atm n2) ]) --  |N2)
                    ])
 | ns == nSeq && nx1 == nX && na2 == nA
   =  lred "X-then-A"
        $mkAnd [ mkX e' abs r' a'
               , Equal (e2la1 `i` r1) emp]
 where
   e2la1 = snd $ esimp vd (e2 `sdiff` a1)
   e'  = snd $ esimp vd (e1 `u` e2la1)
   abs = mkSeq as bs
   r'  = snd $ esimp vd (r1 `u` e2)
   a'  = snd $ esimp vd ((a1 `sdiff` e2) `u` n2)
\end{code}

\newpage
\HDRd{$A$ then $X$}

\RLEQNS{
  && A(E_1|a|N_1) \seq X(E_2|b|R_2|A_2)
\EQ{proof in Views.tex}
\\&& X(E_1 \cup (E_2 \setminus N_1)
      | a\seq b
      | E_1 \cup R_2
      | N_1 \setminus R_2 \cup A_2)
     \land
     (E_2 \setminus N_1) \cap E_1 = \emptyset
}
\begin{code}
vReduce vd _ (Comp ns [ (Comp na1 [ (Atm e1)    -- A(E1
                                , as          --  |a
                                , (Atm n1) ]) --  |N1)
                    , (Comp nx2 [ (Atm e2)    -- A(E2
                                , bs          --  |b
                                , (Atm r2)    --  |R2
                                , (Atm a2) ]) --  |A2)
                    ])
 | ns == nSeq && na1 == nA && nx2 == nX
   =  lred "A-then-X"
        $mkAnd [ mkX e' abs r' a'
               , Equal (e2ln1 `i` e1) emp]
 where
   e2ln1 = snd $ esimp vd (e2 `sdiff` n1)
   e'  = snd $ esimp vd (e1 `u` e2ln1)
   abs = mkSeq as bs
   r'  = snd $ esimp vd (e1 `u` r2)
   a'  = snd $ esimp vd ((n1 `sdiff` r2) `u` a2)
\end{code}


\newpage
\HDRd{$X$ then $X$}

\RLEQNS{
  && X(E_1|a|R_1|A_1) \seq X(E_2|b|R_2|A_2)
\EQ{proof in Views.tex }
\\&& X(E_1 \cup (E_2\setminus A_1)
       |a\seq b
       |R_1 \cup R_2
       |A_1 \setminus R_2 \cup  A_2)
       \land (E_2\setminus A_1) \cap R_1 = \emptyset
}
\begin{code}
vReduce vd _ (Comp ns [ (Comp nx1 [ (Atm e1)   -- X(E1
                                , as           --  |a
                                , (Atm r1)     --  |R1
                                , (Atm a1)  ]) --  |A1)
                    , (Comp nx2 [ (Atm e2)     -- X(E2
                                , bs           --  |b
                                , (Atm r2)     --  |R2
                                , (Atm a2)  ]) --  |A2)
                      ])
 | ns == nSeq && nx1 == nX && nx2 == nX
   =  lred "X-then-X"
        $ mkAnd [ mkX e' abs r' a'
                , Equal (e2la1 `i` r1) emp]
 where
   e2la1 = snd $ esimp vd (e2 `sdiff` a1)
   e'  = snd $ esimp vd (e1 `u` e2la1)
   abs = mkSeq as bs
   r'  = snd $ esimp vd (r1 `u` r2)
   a'  = snd $ esimp vd ((a1 `sdiff` r2) `u` a2)
\end{code}

\newpage
\HDRd{$I$ collapses $X$ to $A$}
\RLEQNS{
   \lnot(\setof{E,L} \textbf{ lsat } I)
   &\implies&  X(E|a|E,L|N) = A(E|a|N)
}
Given $I$ and $X(E|a|R|A)$, we proceed as follows:
\begin{enumerate}
  \item Let $D = R \setminus E$
  \item Compute
    $D' =
       \setof{  d | d \in D,
                    \lnot (E\cup\setof d \textbf{ lsat } I)}
    $
  \item
    If $D = D'$ then return $A(E|a|A)$
  \item
    Else, return $X(E|a|E\cup(D \setminus D')|A)$.
\end{enumerate}
\begin{code}
vReduce vd invs (Comp nx [ Atm e   -- X(E
                         , as      --  |a
                         , Atm r   --  |R
                         , Atm a   --  |A)
                         ])
 | nx == nX && applicable
   = lred "Inv collapses X to A" $ mkA e as a
  where
    applicable = es `isSubSeqOf` rs
                 && ds == ds'
    es = setElems e
    rs = setElems r
    ds = rs \\ es
    ds' = filter (someInvFails invs) ds

    someInvFails [] _ = False
    someInvFails (inv:invs) d
     | lsat vd ed inv  =  someInvFails invs d
     | otherwise  =  True
     where
       ed = snd $ esimp vd (e `u` set [d])
\end{code}


\newpage
\HDRd{General Stuff}~

If $a$ and $b$ have alphabet $\setof{s,s'}$,
then
$(a \seq b)[G,L,M/g,r,r') = a\seq b$.
\begin{code}
vReduce d _ (PSub ab@(Comp ns [PVar a, PVar b]) sub)
 | ns == nSeq && isSS' a && isSS' b && isStaticSub sub
   =  lred "a;b is static-free" ab
 where
   isSS' nm = case M.lookup nm d of
     Just (PredEntry _ _ alf _ _)  ->  null (alf \\ ss')
     Just (AlfEntry alf)           ->  null (alf \\ ss')
     _                             ->  False
   isStaticSub sub = null (map fst sub \\ vStatic)
\end{code}



\begin{eqnarray*}
   A \land (B \lor C) &=& (A \land B) \lor (A \land C)
\end{eqnarray*}
\begin{code}
vReduce d _ (Comp na [ pr, (Comp no prs) ])
 | na == nAnd && no == nOr
      =  lred "and-or-distr" $ mkOr $ map f prs
 where f pr' = mkAnd [pr , pr']
\end{code}

\begin{eqnarray*}
   A \seq (B \lor C) &=& (A \seq B) \lor (A \seq C)
\end{eqnarray*}
\begin{code}
vReduce d _ (Comp ns [ pr, (Comp no prs) ])
 | ns == nSeq && no == nOr
      =  lred ";-or-distr" $  mkOr $ map f prs
 where f pr' = mkSeq pr pr'
\end{code}

\begin{eqnarray*}
  (A \lor B) \seq C &=& (A \seq C) \lor (B \seq C)
\end{eqnarray*}
\begin{code}
vReduce d _ (Comp ns [ (Comp no prs), pr ])
 | ns == nSeq && no == nOr
      =  lred "or-;-distr" $ mkOr $ map f prs
 where f pr' = mkSeq pr' pr
\end{code}

We prefer sequential chains to associate to the left:
\begin{eqnarray*}
   A \seq (B \seq C) &=& (A \seq B) \seq C
\end{eqnarray*}
\begin{code}
vReduce d _ (Comp ns1 [ prA, (Comp ns2 [prB, prC]) ])
 | ns1 == nSeq && ns2 == nSeq
     =  lred  ";-left-assoc" $ mkSeq (mkSeq prA prB) prC
\end{code}



\newpage
Default case: no change.
\begin{code}
vReduce _ _ _ = Nothing
\end{code}

\HDRc{The Reduction Entry}\label{hc:Root-reduce-ent}

\begin{code}
vRedEntry :: Dict
vRedEntry = entry laws $ LawEntry [vReduce] [] []
\end{code}


\HDRb{Conditional Reductions for Root}\label{hb:Root-creduce}

\begin{code}
vCReduce :: CRWFun
\end{code}

Default case: no change.
\begin{code}
vCReduce _ mpr = Nothing
\end{code}

\HDRc{The Conditional Reduction Entry}\label{hc:Root-reduce-ent}

\begin{code}
vCRedEntry :: Dict
vCRedEntry = entry laws $ LawEntry [] [vCReduce] []
\end{code}

\HDRb{Loop Unrolling for Views}\label{hb:Root-unroll}

Iteration  satisfies the loop-unrolling law:
\[
  c * P  \quad=\quad (P ; c * P ) \cond c \Skip
\]
But we also support several styles and degrees of unrolling:
\begin{eqnarray*}
   c*P
   &=_0& (P\seq c*P) \cond c \Skip
\\ &=_1& \lnot c \land \Skip
         \lor
         c \land P ; c * P
\\ &=_2& \lnot c \land \Skip
         \lor
         c \land P ; \lnot c \land \Skip
         \lor
         c \land P ; c \land P ; c * P
\\ &=_3& \lnot c \land \Skip
         \lor
         c \land P ; \lnot c \land \Skip
         \lor
         c \land P ; c \land P ; \lnot c \land \Skip
         \lor
         c \land P ; c \land P ; c \land P ; c *P
\\ && \vdots
\\ &=_n& \left(
           \bigvee_{i=0}^{n-1}  (c \land P)^i \seq \lnot c \land \Skip
         \right)
         \lor
         (c \land P)^n \seq c *P
\end{eqnarray*}
\begin{code}
vUnroll :: String -> RWFun
vUnroll ns d _ iter@(Comp nm  [c, pr])
 | nm == nIter = lred ("loop-unroll" ++ ntag ns) $ vunroll n
 where

   ntag "" = ""
   ntag ns = '.':ns

   n | null ns = 0
     | isDigit $ head ns = digitToInt $ head ns
     | otherwise = 0

   vunroll 0  =  mkCond (mkSeq pr iter) c mkSkip
   vunroll 1  =  mkOr [ loopdone
                      , mkSeq (loopstep 1) iter]
   vunroll 2  =  mkOr [ loopdone
                      , mkSeq (loopstep 1) loopdone
                      , mkSeq (loopstep 2) iter]
   vunroll 3  =  mkOr [ loopdone
                      , mkSeq (loopstep 1) loopdone
                      , mkSeq (loopstep 2) loopdone
                      , mkSeq (loopstep 3) iter]
   vunroll _  =  mkCond (mkSeq pr iter) c mkSkip

   loopdone   = mkAnd [mkNot c, mkSkip]
   loopstep 1 = mkAnd [c, pr]
   loopstep n = mkSeq (loopstep (n-1)) (loopstep 1)

vUnroll _ _ _ _ = Nothing
\end{code}

\HDRc{The Unroll Entry}\label{hc:Root-reduce-ent}

\begin{code}
vLoopEntry :: Dict
vLoopEntry = entry laws $ LawEntry [] [] [wUnroll,vUnroll]
\end{code}


\HDRb{Dictionary for Roots}\label{hb:Root-Dict}

\begin{code}
rDict :: Dict
rDict
 =  dictVersion "Root 0.3"
     -- supersede dictVP below as calcs rollout
    `dictMrg` dictVPCalc
    `dictMrg` vAlfDict
    `dictMrg` dictVE
    `dictMrg` dictVP
    `dictMrg` vRedEntry
    `dictMrg` vCRedEntry
    `dictMrg` vLoopEntry
    `dictMrg` lawsUTCPDict
    `dictMrg` vStdUTPDict
    `dictMrg` stdDict
\end{code}


\HDRb{Root Calculator}\label{hb:Root-CALC}


\begin{code}
rshow :: Pred -> String
rshow = pmdshow 80 rDict noStyles . buildMarks

rput :: Pred -> IO ()
rput = putStrLn . rshow

rcalc pr = calcREPL rDict [noInvariant]  pr

ivcalc inv pr
 = calcREPL rDict [(labelSetInv, inv)]  pr

ivscalc invs pr
 = calcREPL rDict (map lsi invs) pr
 where lsi inv = (labelSetInv, inv)


rputcalc :: Pred -> IO ()
rputcalc pr = printREPL rDict [noInvariant] pr

ivputc inv pr
 = printREPL rDict [(labelSetInv, inv)] pr

rsavecalc fp pr
 = do calc <- rcalc pr
      saveCalc fp calc

rsimp :: Pred -> (String, Pred)
rsimp pr
  = case simplify rDict 42 $ buildMarks pr of
     Nothing               ->  ("", pr)
     Just (_,what,(pr',_)) ->  (what,pr')
rsimp2 :: (String, Pred) -> (String, Pred)
rsimp2 = rsimp . snd

vcsave fp inv pr
 = do calc <- ivcalc inv pr
      saveCalc fp calc
\end{code}


\HDRb{Test Constructs}\label{hB:test-constructs}

\HDRc{Ab Initio}
\begin{code}
pP = PVar "P" ; pQ = PVar "Q"  -- general programs
a = PVar "a"
b = PVar "b"
c = PVar "c"

subII :: Pred
subII = PSub mkSkip [("r",r1')]

-- an invariant that always fails
noGood _ _ _ = Just False

xcalc :: Pred -> IO ()
xcalc = printREPL rDict [(noGood, F)]
\end{code}

\begin{code}
--defvseq :: [Pred] -> Pred
defvseq = defnVSeq (rDict :: Dict)
--athenbBody :: Pred
athenbBody = case defvseq [actionA,actionB] of
              Just (_,Comp _ [body],_)  ->  body
              _                         ->  PVar "??"

testpr = PSub (mkOr [pr, mkSeq pr pr]) [("r",r1)]
 where pr = mkA r ii r'

disp Nothing = putStrLn "\nNo change"
disp (Just (before,_,after))
 = do putStrLn ""
      rput $ fst before
      putStrLn "\n\tbecomes\n"
      rput $ fst after

test :: Maybe BeforeAfter
test = simplify rDict 42 $ buildMarks testpr
\end{code}

\newpage
\HDRb{Calculation Results}

Given the idiom $\true * (\Skip \lor Q)$
we look for pre-computed $Q$-cores,
noting that our final semantics will have the form
\[
  I \land ( \Skip \lor Q \lor Q^2 \lor \dots Q^k)
\]
where $I$ is the label-set invariant
and $Q^i = \false$ for all $i > k$.

When we change from:
\RLEQNS{
   \W(C) &\defs& \true * (\Skip \lor C)
\\ \Atm a &\defs&\W(A(r|a|r')) \land [r|r']
}
\noindent
to:
\RLEQNS{
   \W(C) &\defs& \true * C
\\ \Atm a &\defs&\W(\Skip \lor A(r|a|r')) \land [r|r']
}
\noindent
the calculation outcomes
for \texttt{athenb}, \texttt{aorb}, \texttt{awithb} and \texttt{itera} are unchanged,
and consequently so are all the other calculations.

\HDRc{Atomic Actions}

\begin{verbatim}
invAtom = [r|r']
\end{verbatim}
\begin{code}
actionA = atom a
actionB = atom b
actionC = atom c
\end{code}
\begin{verbatim}
Q(actionA) = A(r|a|r')
\end{verbatim}
\begin{code}
q_actionA = mkA r a r'
q_actionB = mkA r b r'
\end{code}
\begin{verbatim}
q_actionA^2 = false
\end{verbatim}
\begin{code}
v_actionA
 = mkOr [ mkSkip
        , q_actionA ]
v_actionB
 = mkOr [ mkSkip
        , q_actionB ]
\end{code}
\begin{verbatim}
v_actionA
 = [r|r'] /\
   ( II \/ A(r|a|r') )
\end{verbatim}

\newpage
\HDRc{Sequential Composition}

\begin{verbatim}
invVSeq = [r|r']
invVAtom = [r|r']
invVAtom.a = [r|lg]
invVatom.b = [lg|r']
\end{verbatim}
\begin{code}
athenb = actionA `vseq` actionB
\end{code}

\begin{verbatim}
athenb
 = W(A(r|ii|r1) \/ A(r1|a|r1*) \/ A(r1*|ii|r2) \/ A(r2|b|r2*) \/ A(r2*|ii|r*))
Q(athenb)
  = A(r|ii|r1) \/ A(r1|a|r1*) \/ A(r1*|ii|r2) \/ A(r2|b|r2*) \/ A(r2*|ii|r*)
\end{verbatim}
We note that the result is virtually identical to that of the label-generator
version!
\begin{code}
q_athenb
 = mkOr [ mkA r ii r1
        , mkA r1 a r1'
        , mkA r1' ii r2
        , mkA r2 b r2'
        , mkA r2' ii r' ]
\end{code}

\begin{verbatim}
q_athenb^2 =
   A(r  |ii;a|r1*)
 \/ A(r1 |a;ii|r2)
 \/ A(r1*|ii;b|r2*)
 \/ A(r2 |b;ii|r*)
\end{verbatim}
Again, this is the same as the label-generated version!
\begin{code}
q_athenb_2
 = mkOr [ mkA r   a r1'
        , mkA r1  a r2
        , mkA r1' b r2'
        , mkA r2  b r' ]
\end{code}
We
\begin{verbatim}
q_athenb^3 =
    A(r|ii ; a|r2)
 \/ A(r1|a ; b|r2:)
 \/ A(r1:|ii ; b|r:)
\end{verbatim}
\begin{code}
ab = mkSeq a b
q_athenb_3
 = mkOr [ mkA r a r2
        , mkA r1 ab r2'
        , mkA r1' b r' ]
\end{code}

\begin{verbatim}
q_athenb^4 =
    A(r|ii ; a ; b|r2:)
 \/ A(r1|a ; b|r:)
\end{verbatim}
\begin{code}
q_athenb_4
 = mkOr [ mkA r ab r2'
        , mkA r1 ab r' ]
\end{code}

\begin{verbatim}
q_athenb^5 =
    A(r|ii ; a ; b|r:)
\end{verbatim}
\begin{code}
q_athenb_5
 = mkOr [ mkA r ab r' ]
\end{code}

\begin{verbatim}
q_athenb^6 = false
\end{verbatim}
\begin{code}
q_athenb_all
 = mkOr [ mkSkip
        , q_athenb
        , q_athenb_2
        , q_athenb_3
        , q_athenb_4
        , q_athenb_5 ]
\end{code}
\begin{verbatim}
v_athenb
 = [r|r1|r1'|r2|r2'|r'] /\
    A(r|ii|r1) \/ A(r1|a|r1:) \/ A(r1:|ii|r2) \/ A(r2|b|r2:) \/ A(r2:|ii|r:)
 \/ A(r|a|r1:) \/ A(r1|a|r2) \/ A(r1:|b|r2:) \/ A(r2|b|r:)
 \/ A(r|a|r2) \/ A(r1|ab|r2:) \/ A(r1:|b|r:)
 \/ A(r|ab|r2:) \/ A(r1|ab|r:)
 \/ A(r|ab|r:)
\end{verbatim}
\begin{code}
v_athenb = mkAnd [invVSeq, q_athenb_all ]
\end{code}

\newpage
\HDRc{Non-deterministic Choice}

\begin{verbatim}
invVChc = [r|lg1|lg2|r']
\end{verbatim}
\begin{code}
aorb = actionA `vchc` actionB
\end{code}
\begin{verbatim}
Q(aorb) = A(r|ii|r1) \/ A(r|ii|r2)
          \/ A(r1|a|r1:) \/ A(r2|b|r2:)
          \/ A(r1:|ii|r:) \/ A(r2:|ii|r:)
\end{verbatim}
\begin{code}
q_aorb
  = mkOr [ mkA r ii r1
         , mkA r ii r2
         , mkA r1  a r1'
         , mkA r2  b r2'
         , mkA r1' ii r'
         , mkA r2' ii r' ]
\end{code}

\begin{verbatim}
q_aorb^2 = A(r|a|r1:) \/ A(r|b|r2:) \/ A(r1|a|r:) \/ A(r2|b|r:)
\end{verbatim}
\begin{code}
q_aorb_2
  = mkOr [ mkA r a r1'
         , mkA r b r2'
         , mkA r1 a r'
         , mkA r2 b r' ]
\end{code}

\begin{verbatim}
q_aorb^3 = A(r|a|r:) \/ A(r|b|r:)
\end{verbatim}
\begin{code}
q_aorb_3
 = mkOr [ mkA r a r', mkA r b r' ]
\end{code}
\begin{verbatim}
q_aorb^4 = false
\end{verbatim}
\begin{code}
q_aorb_all
 = mkOr [ mkSkip
        , q_aorb
        , q_aorb_2
        , q_aorb_3 ]
\end{code}
\begin{verbatim}
v_aorb
 = [r|r1|r1:|r2|r2:|r:] /\
   ( II
     \/ A(r|ii|r1) \/ A(r|ii|r2)
     \/ A(r1|a|r1:) \/ A(r2|b|r2:)
     \/ A(r1:|ii|r:) \/ A(r2:|ii|r:)
     \/ A(r|a|r1:) \/ A(r|b|r2:) \/ A(r1|a|r:) \/ A(r2|b|r:)
     \/ A(r|a|r:) \/ A(r|b|r:) )
\end{verbatim}
\begin{code}
v_aorb = mkAnd [ invVChc, q_aorb_all ]
\end{code}



\newpage
\HDRc{Parallel Composition}

\begin{verbatim}
invVPar = [r|r1,r1',r2,r2'|r'] /\ [r1|r1*] /\ [r1|r2*]
\end{verbatim}
\begin{code}
awithb = actionA `vpar` actionB
\end{code}
\begin{verbatim}
Q(awithb)
  =   A(r|ii|r1,r2)
    \/ A(r1|a|r1*)
    \/ A(r2|b|r2*)
    \/ A(r1*,r2*|ii|r*))
\end{verbatim}
\begin{code}
q_awithb
  = mkOr [ mkA r ii $ set [r1,r2]
         , mkA r1 a r1'
         , mkA r2 b r2'
         , mkA (set [r1',r2']) ii r' ]
\end{code}

\begin{verbatim}
q_awithb^2
 =  A(r|a|r2,r1:)
 \/ A(r1,r2|ba|r1:,r2:)
 \/ A(r|b|r1,r2:)
 \/ A(r1,r2|ab|r1:,r2:)
 \/ A(r1,r2:|a|r:)
 \/ A(r2,r1:|b|r:)
\end{verbatim}


\begin{code}
q_awithb_2
  = mkOr [ mkA r a $ set [r1',r2]
         , mkA (set [r1,r2]) ba $ set [r1',r2']
         , mkA r b $ set [r2',r1]
         , mkA (set [r1,r2]) ab $ set [r1',r2']
         , mkA (set [r2',r1]) a r'
         , mkA (set [r1',r2]) b r' ]
ba = mkSeq b a
\end{code}

\begin{verbatim}
q_awithb^3
 =  A(r|ba|r1:,r2:)
 \/ A(r|ab|r1:,r2:)
 \/ A(r1,r2|ba|r:)
 \/ A(r1,r2|ab|r:)
\end{verbatim}
\begin{code}
q_awithb_3
 = mkOr [ mkA r ba $ set [r1',r2']
        , mkA r ab $ set [r1',r2']
        , mkA (set [r1,r2]) ba r'
        , mkA (set [r1,r2]) ab r' ]
\end{code}
\begin{verbatim}
q_awithb^4
 = A(r|ba|r:) \/ A(r|ab|r:)
\end{verbatim}
Tidy up
\begin{code}
q_awithb_4
 = mkOr [ mkA r (mkSeq b a) r'
        , mkA r (mkSeq a b) r' ]
\end{code}
\begin{verbatim}
q_awithb^5 = false
\end{verbatim}
\begin{code}
q_awithb_all
 = mkOr [ mkSkip
        , q_awithb
        , q_awithb_2
        , q_awithb_3
        , q_awithb_4 ]

v_awithb = mkAnd [ invVPar, q_awithb_all ]
\end{code}
\begin{verbatim}
v_awithb
 = [r|[lg1|lg1:],[lg2|lg2:]|r'] /\
   ( II \/ A(r|ii|lg1,lg2)           \/ A(lg1:,lg2:|ii|r')
        \/ A(lg1|a|lg1:)              \/ A(lg2|b|lg2:)
        \/ A(r|a|lg1:,lg2)           \/ A(r|b|lg2:,lg1)
        \/ A(lg1,lg2|b ; a|lg1:,lg2:) \/ A(lg1,lg2|a ; b|lg1:,lg2:)
        \/ A(lg2:,lg1|a|r')          \/ A(lg1:,lg2|b|r')
        \/ A(r|b ; a|lg1:,lg2:)      \/ A(r|a ; b|lg1:,lg2:)
        \/ A(lg1,lg2|b ; a|r')       \/ A(lg1,lg2|a ; b|r')
        \/ A(r|b ; a|r')            \/ A(r|a ; b|r') )
\end{verbatim}

\newpage
\HDRc{ Atomic Iteration}

\begin{verbatim}
invVIter = [r|lg|r']
invVAtom = [r|r']
invVatom.a [lg|r]
\end{verbatim}
\begin{code}
itera = viter actionA
\end{code}

\begin{verbatim}
Q(itera)
 =  A(r|ii|r2)
 \/ A(r2|ii|r1)
 \/ A(r1|a|r1:)
 \/ A(r1:|ii|r2)
 \/ A(r2|ii|r:)
\end{verbatim}
\begin{code}
q_itera
  = mkOr [ mkA r ii r2
         , mkA r2 ii r1
         , mkA r1  a  r1'
         , mkA r1' ii r2
         , mkA r2 ii r' ]
\end{code}





\begin{verbatim}
q_itera^2
  = A(r|ii|r1)
 \/ A(r1:|ii|r1)
 \/ A(r2|a|r1:)
 \/ A(r1|a|r2)
 \/ A(r|ii|r:)
 \/ A(r1:|ii|r:)
\end{verbatim}
\begin{code}
q_itera_2
 = mkOr [ mkA r ii r1
        , mkA r1' ii r1
        , mkA r2 a r1'
        , mkA r1 a r2
        , mkA r ii r'     -- 1st zero iter, end-to-end
        , mkA r1' ii r' ]
\end{code}

\begin{verbatim}
q_itera^3
  = A(r1|a|r1)
 \/ A(r|a|r1:)
 \/ A(r1:|a|r1:)
 \/ A(r2|a|r2)
 \/ A(r1|a|r:)
\end{verbatim}
\begin{code}
q_itera_3
 = mkOr [ mkA r1 a r1
        , mkA r a r1'
        , mkA r1' a r1'
        , mkA r2 a r2
        , mkA r1 a r' ]
\end{code}

\begin{verbatim}
q_itera^4
  = A(r2|a|r1)
 \/ A(r1|aa|r1:)
 \/ A(r|a|r2)
 \/ A(r1:|a|r2)
 \/ A(r2|a|r:)
\end{verbatim}
\begin{code}
q_itera_4
 = mkOr [ mkA r2 a r1
        , mkA r1 aa r1' -- 1st double!
        , mkA r a r2
        , mkA r1' a r2
        , mkA r2 a r' ]

aa = mkSeq a a
\end{code}

\begin{verbatim}
q_itera^5
  = A(r|a|r1)
 \/ A(r1:|a|r1)
 \/ A(r2|aa|r1:)
 \/ A(r1|aa|r2)
 \/ A(r|a|r:)
 \/ A(r1:|a|r:)
\end{verbatim}
\begin{code}
q_itera_5
 = mkOr [ mkA r a r1
        , mkA r1' a r1
        , mkA r2 aa r1'
        , mkA r1 aa r2
        , mkA r a r'    -- 1st single iter, end-to-end
        , mkA r1' a r' ]
\end{code}

\begin{verbatim}
q_itera^6
  = A(r1|aa|r1)
 \/ A(r|aa|r1:)
 \/ A(r1:|aa|r1:)
 \/ A(r2|aa|r2)
 \/ A(r1|aa|r:)
\end{verbatim}
\begin{code}
q_itera_6
 = mkOr [ mkA r1 aa r1
        , mkA r aa r1'
        , mkA r1' aa r1'
        , mkA r2 aa r2
        , mkA r1 aa r'
        ]
\end{code}
Now the pattern repeats, with a \verb"q_itera_n" cycle of length 3

\newpage
\HDRc{ Sequence Iteration}

\begin{code}
iterseq = viter v_athenb
\end{code}

\newpage
\HDRb{Code for generic library somewhere}

Deep unwrapping:
\RLEQNS{
   T( \dots \oplus T(P) \oplus \dots) &=& T(\dots \oplus P \oplus \dots)
\\ T( U \oplus P) &=& T(P)
}
Here we have the predicate representing $\dots \oplus T(P) \oplus \dots$.
\begin{code}
deepUnwrap :: String  -- top-level connective (oplus)
           -> ([Pred]->Pred) -- connective builder
           -> String  -- unwrap target (T)
           -> String  -- unit (U)
           -> Pred  -- predicate (P1 oplus P2 oplus ... oplus Pn)
           -> Maybe Pred -- outcome, if any change
deepUnwrap nConn mkConn nTarget nUnit (Comp nm [pr]) -- immediate nesting of T
 | nm == nTarget  =  case deepUnwrap nConn mkConn nTarget nUnit pr of
                      Nothing  ->  Just pr
                      jpr'     ->  jpr'
deepUnwrap nConn mkConn nTarget nUnit (Comp nt [u@(Comp nu [])]) -- just U
 | nt == nTarget && nu == nUnit  =  Just u
deepUnwrap nConn mkConn nTarget nUnit (Comp nm prs) -- top-level connective
 | nm == nConn  =  case deepUnwraps nConn mkConn nTarget nUnit False [] prs of
                      Nothing    ->  Nothing
                      Just prs'  ->  Just $ mkConn prs'
deepUnwrap _ _ _ _ _ = Nothing
\end{code}

Tail recursive unwrap of predicate list:
\begin{code}
deepUnwraps nConn mkConn nTarget nUnit chgd srp' []
 | chgd       =  Just $ reverse srp'
 | otherwise  =  Nothing
deepUnwraps nConn mkConn nTarget nUnit chgd srp' (pr:prs)
 | pHasName nUnit pr  =  deepUnwraps nConn mkConn nTarget nUnit True srp' prs
 | otherwise
   = case deepUnwrap nConn mkConn nTarget nUnit pr of
       Nothing   ->  deepUnwraps nConn mkConn nTarget nUnit chgd (pr:srp')  prs
       Just pr'  ->  deepUnwraps nConn mkConn nTarget nUnit True (pr':srp') prs
\end{code}
