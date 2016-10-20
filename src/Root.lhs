\HDRa{Root}\label{ha:Root}
\begin{code}
module Root where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import POrd
import PrettyPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
import CalcAlphabets
import CalcSysTypes
import CalcSimplify
import CalcRecogniser
import CalcRun
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
``step'' ($:$);
``split-one'' ($1$);
and ``split-two'' ($2$).
\RLEQNS{
   S &\defs& \setof{:,1,2}
}
\begin{code}
showConst str _ _ = str  -- constant pretty-printer
evalConst _ = noeval -- constant (non-)evaluator

stepn   = ":" ; step   = App stepn   []
split1n = "1" ; split1 = App split1n []
split2n = "2" ; split2 = App split2n []

stepEntry
 = ( stepn,   ExprEntry [] (showConst stepn)   evalConst noEq )
split1Entry
 = ( split1n, ExprEntry [] (showConst split1n) evalConst noEq )
split2Entry
 = ( split2n, ExprEntry [] (showConst split2n) evalConst noEq )

data RootStep = Step | Split1 | Split2 deriving (Eq,Ord)
instance Show RootStep where
 show Step = ":"
 show Split1 = "1"
 show Split2 = "2"
\end{code}

We now define a rooted path as an expression of the form
of the variable $r$ followed by zero or more $S$ transforms.
\RLEQNS{
   \sigma,\varsigma &\defs& S^*
\\ R &::=& r | R S
\\   & = & r\sigma
}
These have to be expressions as we shall want to substitute for $r$
in them.
\begin{code}
rootn = "r" ; root = Var rootn

rpathn = "R"
rpath rp s = App rpathn [rp, s]
rPath [rp, s] = rpath rp s

rpShow d [rp, s] = edshow d rp ++ edshow d s

rpathEntry :: Show s => ( String, Entry s )
rpathEntry
 = ( rpathn
   , ExprEntry subAny rpShow (justMakes rPath) noEq )

newtype RootPath = RootPath [RootStep] deriving Eq
instance Show RootPath where
  show (RootPath rs) = 'r':(concat (map show rs))
instance Read RootPath where
  readsPrec _ ('r':rest) = [readPath [] rest]
  readsPrec _ _ = []

readPath path "" = (RootPath $ reverse path,"")
readPath path str@(c:cs)
 | c == ':'   =  readPath (Step:path) cs
 | c == '1'   =  readPath (Split1:path) cs
 | c == '2'   =  readPath (Split2:path) cs
 | otherwise  =  (RootPath $ reverse path,str)
\end{code}

\newpage
\HDRc{Path Ordering}
\RLEQNS{
   R &\le& R\sigma
\\ R1\sigma &<& R\!:\!\varsigma
\\ R2\sigma &<& R\!:\!\varsigma
}
\begin{code}
instance POrd RootPath where
  pcmp (RootPath rp1) (RootPath rp2) = compRP rp1 rp2

compRP :: [RootStep] -> [RootStep] -> POrdering
\end{code}
\RLEQNS{
   r &\le& r\sigma
}
\begin{code}
compRP  [] [] = PEQ
compRP [] (_:_) = PLT
compRP (_:_) [] = PGT
\end{code}
\RLEQNS{
   R1\sigma &<& R\!:\!\varsigma
}
\begin{code}
compRP (Split1:_) (Step:_) = PLT
compRP (Step:_) (Split1:_) = PGT
\end{code}
\RLEQNS{
   R2\sigma &<& R\!:\!\varsigma
}
\begin{code}
compRP (Split2:_) (Step:_) = PLT
compRP (Step:_) (Split2:_) = PGT
\end{code}
\RLEQNS{
   R &\le& R\sigma
}
\begin{code}
compRP (s1:ss1) (s2:ss2)
 | s1 == s2  =  compRP ss1 ss2
 | otherwise =  PNC
\end{code}

Build the rooted paths dictionary:
\begin{code}
rPathDict :: Show s => Dict s
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

mkSet :: Ord s => [Expr s] -> Expr s
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
vSetDict :: (Eq s, Ord s, Show s) => Dict s
vSetDict
 = makeDict
    [ (setn,(ExprEntry subAny showSet evalSet eqSet))
    , (unionn,(ExprEntry subAny ppUnion evalUnion noEq))
    , (intn,(ExprEntry subAny ppIntsct evalIntsct noEq))
    , (sdiffn,(ExprEntry subAny ppSDiff evalSDiff noEq))
    , (subsetn,(ExprEntry subAny showSubSet evalSubset noEq))
    , (sswapn, (ExprEntry subAny showSSwap evalSSwap noEq))
    ]
\end{code}

\newpage
\HDRc{Label Generation}

Imagine that we have a mechanism for generating labels as follows:
\RLEQNS{
  g &\in& G & \text{a label generator}
\\ \ell &\in& L & \text{labels}
\\ new &:& G \fun L \times G & \text{generating a new label}
\\ split &:& G \fun G \times G & \text{split one generator into two}
}

Coding the function projections
$new_i = \pi_i \circ new$
and $split_i = \pi_i \circ split$.
\begin{code}
-- deprecated:
new1n = "new1"
new1 g = App new1n [g]
gNew1 [g] = new1 g

new2n = "new2"
new2 g = App new2n [g]
gNew2 [g] = new2 g

xxxsplit1n = "xxxsplit1"
xxxsplit1 g = App xxxsplit1n [g]
gSplit1 [g] = xxxsplit1 g

xxxsplit2n = "xxxsplit2"
xxxsplit2 g = App xxxsplit2n [g]
gSplit2 [g] = xxxsplit2 g
\end{code}

\HDRd{Generator Shorthand}

To make calculation easier, we shall introduce the following shorthands:
\RLEQNS{
\\ \ell_g &\defs& new_1(g)
\\ \g:    &\defs& new_2(g)
\\ \g1    &\defs& split_1(g)
\\ \g2    &\defs& split_2(g)
}
\begin{code}
showGNew1   d [g] = 'l':edshow d g
showGNew2   d [g] = edshow d g ++ ":"
showGSplit1 d [g] = edshow d g ++ "1"
showGSplit2 d [g] = edshow d g ++ "2"
\end{code}

We can now define a generator dictionary:
\begin{code}
vGenDict :: (Eq s, Ord s, Show s) => Dict s
vGenDict
 = makeDict
    [ (new1n,(ExprEntry subAny showGNew1 (justMakes gNew1) noEq))
    , (new2n,(ExprEntry subAny showGNew2 (justMakes gNew2) noEq))
    , (xxxsplit1n,(ExprEntry subAny showGSplit1 (justMakes gSplit1) noEq))
    , (xxxsplit2n,(ExprEntry subAny showGSplit2 (justMakes gSplit2) noEq))
    ]
\end{code}

\HDRc{The Expression Dictionary}\label{hc:WWW-expr-dict}

\begin{code}
dictVE :: (Ord s, Show s) => Dict s
dictVE = rPathDict `dictMrg` vSetDict -- `dictMrg` vGenDict
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
-- deprecated:
g   = Var "g"
inp = Var "in" -- "in" is a Haskell keyword
out = Var "out"
\end{code}

We define our dictionary alphabet entries,
and also declare that the predicate variables $a$, $a$ and $a$
will refer to atomic state-changes,
and so only have alphabet $\setof{s,s'}$.
\begin{code}
vAlfDict
 = dictMrg dictAlpha dictAtomic
 where
   dictAlpha = stdAlfDictGen ["s"] ["ls"] vStatic
   dictAtomic = makeDict [ pvarEntry "a" ss'
                         , pvarEntry "b" ss'
                         , pvarEntry "c" ss' ]
   ss' = ["s", "s'"]

vStatic = ["r"]
vDynamic = ["ls","ls'","s","s'"]
vObs = vDynamic ++ vStatic
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
vStdUTPDict :: (Show s, Ord s) => Dict s
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
   X(E|ss'|R|A)
   &\defs&
   ls(E) \land [ss'] \land ls'=(ls\setminus R)\cup A
\end{eqnarray*}

\begin{code}
nX = "X"
isX (_,Comp n [_,_,_,_]) | n==nX = True; isX _ = False

mkX e ss' r a  = Comp nX [Atm e, ss', Atm r, Atm a]

pFlatShow d (Atm (App ns es))
 | ns == setn  = flatSet d es
pFlatShow d (Atm e) = flatSet d [e]
pFlatShow _ _ = "?"

ppX sCP vd p prs@[e,ss',r,a]
 = ppclosed "X(" ")" "|"
    [ ppa $ pFlatShow vd e
    , sCP 0 2 ss'
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
vXEntry :: (Show s, Ord s) => (String, Entry s)
vXEntry
 = ( nX
   , PredEntry vStatic ppX vObs defnX simpX )
\end{code}

\begin{eqnarray*}
   A(E|ss'|N)
   &\defs&
   X(E|ss'|E|N)
\end{eqnarray*}

\begin{code}
nA = "A"
isA (Comp n [_,_,_]) | n==nA = True; isA _ = False

mkA e ss' n  = Comp nA [Atm e, ss', Atm n]

ppA sCP vd p mprs@[e,ss',n]
 = ppclosed "A(" ")" "|"
    [ ppa $ pFlatShow vd e
    , sCP 0 2 ss'
    , ppa $ pFlatShow vd n ]
ppA _ _ _ _ = pps styleRed $ ppa ("invalid-"++nA)

-- we don't want to expand the definition of this, or simplify it
defnA = pNoChg nA
simpA = pNoChg nA

vAEntry :: (Show s, Ord s) => (String, Entry s)
vAEntry
 = ( nA
   , PredEntry vStatic ppA vObs defnA simpA )
\end{code}


\newpage
\HDRc{Coding Label-Set Invariants}

We have a key invariant as part of the healthiness
condition associated with every semantic predicate,
namely that the labels $r$ and $\rr:$ never occur in  $ls$ at
the same time:
\[
 ( r \in ls \implies \rr: \notin ls )
 \land
 ( \rr: \in ls \implies r \notin ls )
\]
This is the Label Exclusivity invariant.

Given the way we shall use substitution of $r$ by
other rooted paths, for sub-components,
we shall see that we will get a number of instances of this.
We adopt a shorthand notation,
so that the above invariant is simply
\[
  [r|\rr:]
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

vLESetEntry :: Show s => (String, Entry s)
vLESetEntry
 = ( nLESet
   , ExprEntry subAny showLESet (justMakes leSet) noEq )
\end{code}

\newpage
We then move onto the ``LE-invariant'', as predicates
\begin{code}
nLEInv = "LEInv"

leInv es = Comp nLEInv $ map Atm es

isLEInv (Comp n es)
 | n == nLEInv  =  all isLESet es
 | otherwise    =  False

precInv = -1

ppLEInv sCP d p prs
 = ppclosed "[" "]" "|" $ map (sCP precInv 1) prs

vLEInvEntry :: (Show s, Ord s) => (String, Entry s)
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
labelSetInv :: (Ord s, Show s) => InvChecker s
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
lsat :: (Ord s, Show s) => Dict s -> Expr s -> Pred s -> Bool
lsat d lset (Comp nm ells)
 | nm == nLEInv
   = case filter (lsat' d lset) ells of
      []   ->  True
      [_]  ->  True
      _    ->  False
 | otherwise  =  False
lsat _ _ _ = False

lsat' :: (Ord s, Show s) => Dict s -> Expr s -> Pred s -> Bool
lsat' d lset (Atm (App nm lse))
 | nm == nLESet  =  any (lsat'' d lset) lse
 | otherwise     =  False
lsat' _ _ _      =  False

lsat'' :: (Ord s, Show s) => Dict s -> Expr s -> Expr s -> Bool
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
\begin{code}
invTrims :: (Ord s, Show s)
         => Dict s
         -> Pred s  -- Invariant
         -> Expr s  -- enable label being removed
         -> Expr s  -- other label being removed
         -> Bool
invTrims d inv ena other = not $ lsat d (set [ena,other]) inv
\end{code}

\newpage
\HDRc{Wheels within Wheels}\label{hc:WwW}

The wheels-within-wheels healthiness condition
insists that $r$ and $\rr:$ are never simultaneously in
the label-set $ls$,
and that our semantic predicates are closed under mumbling.
\RLEQNS{
   \W(C)
   &\defs&
   [r|\rr:] \land \left(~\bigvee_{i\in 0\dots} C^i~\right)
\\ ii &\defs& s'=s
}
\begin{code}
nW = "W"
isW (Comp n [_]) | n==nW = True; isW _ = False

mkW pr  = Comp nW [pr]

ppW sCP vd p [pr]
 = ppclosed "W(" ")" "" [ sCP 0 1 pr ]
ppW _ _ _ _ = pps styleRed $ ppa ("invalid-"++nW)

-- we don't want to expand the definition of this, or simplify it
defnW = pNoChg nW
simpW = pNoChg nW

vWEntry :: (Show s, Ord s) => (String, Entry s)
vWEntry
 = ( nW
   , PredEntry [] ppW vObs defnW simpW )
\end{code}

\newpage
Unrolling $\W(C)$, using $I$ for $[r|\rr:]$,
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
We assume $\seq$ binds tighter then $\lor$.
\begin{code}
wUnroll :: Ord s => String -> RWFun s
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
   \W(C) &\defs& [r|\rr:]
                 \land
                 \left(\bigvee_{i\in 0\dots} C^i\right)
\\ ii &\defs& s'=s
\\
\\ \Atm a &\defs&\W(A(r|a|\rr:))
\\
\\ C \cseq D
   &\defs&
   \W(~    A(r|ii|\rr1)
      \lor C[\rr1/r]
      \lor A(\rr{1:}|ii|\rr2)
      \lor D[\rr2/r]
      \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(r|ii|\rr1) \lor A(r|ii|\rr2)
\\ && \qquad {} \lor
   C[\rr1/r] \lor D[\rr2/r]
\\ && \qquad {} \lor A(\rr{1:}|ii|\rr:) \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C \parallel D
   &\defs&
   \W(\quad\phlor A(r|ii|\rr1,\rr2)
\\ && \qquad {}\lor
   C[\rr1/r]
   \lor D[\rr2/r]
\\ && \qquad {}\lor
   A(\rr{1:},\rr{2:}|ii|\rr:)~)
\\
\\ C^*
   &\defs&
   \W(\quad  \phlor A(r|ii|\rr1) \lor A(\rr1|ii|\rr:)
\\ && \qquad {}\lor C[\rr1/r]    \lor A(\rr{1:}|ii|\rr1) ~)
\\
\\ \cskip
   &\defs&
   \Atm{ii}
}

\newpage
\HDRc{Coding Atomic Semantics}

\RLEQNS{
 \Atm a &\defs&\W(\Skip \lor A(in|a|out)) \land [in|out]
}
\RLEQNS{
   \W(C) &\defs& [r|\rr:]
                 \land
                 \left(\bigvee_{i\in 0\dots} C^i\right)
\\ ii &\defs& s'=s
\\
\\ \Atm a &\defs&\W(A(r|a|\rr:))
\\
\\ C \cseq D
   &\defs&
   \W(~    A(r|ii|\rr1)
      \lor C[\rr1/r]
      \lor A(\rr{1:}|ii|\rr2)
      \lor D[\rr2/r]
      \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(r|ii|\rr1) \lor A(r|ii|\rr2)
\\ && \qquad {} \lor
   C[\rr1/r] \lor D[\rr2/r]
\\ && \qquad {} \lor A(\rr{1:}|ii|\rr:) \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C \parallel D
   &\defs&
   \W(\quad\phlor A(r|ii|\rr1,\rr2)
\\ && \qquad {}\lor
   C[\rr1/r]
   \lor D[\rr2/r]
\\ && \qquad {}\lor
   A(\rr{1:},\rr{2:}|ii|\rr:)~)
\\
\\ C^*
   &\defs&
   \W(\quad  \phlor A(r|ii|\rr1) \lor A(\rr1|ii|\rr:)
\\ && \qquad {}\lor C[\rr1/r]    \lor A(\rr{1:}|ii|\rr1) ~)
\\
\\ \cskip
   &\defs&
   \Atm{ii}
}

\begin{code}
nAtom = "Atom" -- internal abstract name
isAtom (Comp n [_]) | n==nAtom = True; isAtom _ = False

atom pr = Comp nAtom [pr]

ppAtom sCP d p [pr] = ppbracket "<" (sCP 0 1 pr) ">"
ppAtom _ _ _ _ = pps styleRed $ ppa ("invalid-"++nAtom)

defnAtom d [a]
 = ldefn nAtom $ wp $ mkOr $ [mkSkip, mkA inp a out]

invAtom = leInv [leSet [inp], leSet [out]]

wp x = Comp "W" [x]

sinp = sngl inp
sout = sngl out

vAtmEntry :: (Show s, Ord s) => (String, Entry s)
vAtmEntry
 = ( nAtom
   , PredEntry ["s","s'"] ppAtom [] defnAtom (pNoChg nAtom) )
\end{code}

Running the calculator on $Atm(a)$ results in the following:
\begin{verbatim}
II \/ A(in|a|out)
\end{verbatim}
So we add a variant dictionary entry:
\begin{code}
defnAtomCalc d [a]
 = ldefn (nAtom++" calculation") $ mkOr [mkSkip, mkA inp a out]

vAtmCalcEntry :: (Show s, Ord s) => (String, Entry s)
vAtmCalcEntry
 = ( nAtom
   , PredEntry ["s","s'"] ppAtom [] defnAtomCalc (pNoChg nAtom) )
\end{code}


\newpage
\HDRc{Coding Skip}

\RLEQNS{
   \cskip
   &\defs&
   \W(\Skip \lor A(in|ii|out)) \land [in|out]
}
\RLEQNS{
   \W(C) &\defs& [r|\rr:]
                 \land
                 \left(\bigvee_{i\in 0\dots} C^i\right)
\\ ii &\defs& s'=s
\\
\\ \Atm a &\defs&\W(A(r|a|\rr:))
\\
\\ C \cseq D
   &\defs&
   \W(~    A(r|ii|\rr1)
      \lor C[\rr1/r]
      \lor A(\rr{1:}|ii|\rr2)
      \lor D[\rr2/r]
      \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(r|ii|\rr1) \lor A(r|ii|\rr2)
\\ && \qquad {} \lor
   C[\rr1/r] \lor D[\rr2/r]
\\ && \qquad {} \lor A(\rr{1:}|ii|\rr:) \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C \parallel D
   &\defs&
   \W(\quad\phlor A(r|ii|\rr1,\rr2)
\\ && \qquad {}\lor
   C[\rr1/r]
   \lor D[\rr2/r]
\\ && \qquad {}\lor
   A(\rr{1:},\rr{2:}|ii|\rr:)~)
\\
\\ C^*
   &\defs&
   \W(\quad  \phlor A(r|ii|\rr1) \lor A(\rr1|ii|\rr:)
\\ && \qquad {}\lor C[\rr1/r]    \lor A(\rr{1:}|ii|\rr1) ~)
\\
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

defnVSkip d []
 = ldefn nVSkip $ wp $ mkOr $ [mkSkip, mkA inp ii out]

invVSkip = leInv [leElem inp, leElem out]

vSkipEntry :: (Show s, Ord s) => (String, Entry s)
vSkipEntry
 = ( nVSkip
   , PredEntry ["s","s'"] ppVSkip [] defnVSkip (pNoChg nSkip) )

-- atomic skip
nii= "ii"
ii = PVar nii
\end{code}
The calculation of $Atm(ii)$ also leads us to the following calculation
for \verb"<skip>":
\begin{verbatim}
II \/ A(in|ii|out)
\end{verbatim}
So we add a variant dictionary entry:
\begin{code}
defnVSkipCalc d []
 = ldefn (nVSkip++" calculation") $ mkOr [mkSkip, mkA inp ii out]

vSkipCalcEntry :: (Show s, Ord s) => (String, Entry s)
vSkipCalcEntry
 = ( nVSkip
   , PredEntry ["s","s'"] ppVSkip [] defnVSkipCalc (pNoChg nAtom) )
\end{code}





\newpage
\HDRc{Coding Sequential Composition}

\RLEQNS{
   C \cseq D
   &\defs&
   \W(C[g_{:1},\ell_g/g,out] \lor D[g_{:2},\ell_g/g,in])
   \land [in|\ell_g|out]
}
\RLEQNS{
   \W(C) &\defs& [r|\rr:]
                 \land
                 \left(\bigvee_{i\in 0\dots} C^i\right)
\\ ii &\defs& s'=s
\\
\\ \Atm a &\defs&\W(A(r|a|\rr:))
\\
\\ C \cseq D
   &\defs&
   \W(~    A(r|ii|\rr1)
      \lor C[\rr1/r]
      \lor A(\rr{1:}|ii|\rr2)
      \lor D[\rr2/r]
      \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(r|ii|\rr1) \lor A(r|ii|\rr2)
\\ && \qquad {} \lor
   C[\rr1/r] \lor D[\rr2/r]
\\ && \qquad {} \lor A(\rr{1:}|ii|\rr:) \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C \parallel D
   &\defs&
   \W(\quad\phlor A(r|ii|\rr1,\rr2)
\\ && \qquad {}\lor
   C[\rr1/r]
   \lor D[\rr2/r]
\\ && \qquad {}\lor
   A(\rr{1:},\rr{2:}|ii|\rr:)~)
\\
\\ C^*
   &\defs&
   \W(\quad  \phlor A(r|ii|\rr1) \lor A(\rr1|ii|\rr:)
\\ && \qquad {}\lor C[\rr1/r]    \lor A(\rr{1:}|ii|\rr1) ~)
\\
\\ \cskip
   &\defs&
   \Atm{ii}
}
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

defnVSeq d [p,q]
 = ldefn shVSeq $ wp $ mkOr [PSub p sub1, PSub q sub2]
 where
   sub1 = [("g",g'1),("out",lg)]
   sub2 = [("g",g'2),("in",lg)]

lg = new1 g
g' = new2 g
g'1 = xxxsplit1 g'
g'2 = xxxsplit2 g'

invVSeq = leInv[leElem inp, leElem lg, leElem out]

vSeqEntry :: (Show s, Ord s) => (String, Entry s)
vSeqEntry
 = ( nVSeq
   , PredEntry [] ppVSeq [] defnVSeq (pNoChg nVSeq) )
\end{code}


\newpage
\HDRc{Coding (Non-Det.) Choice}

\RLEQNS{
   C + D
   &\defs&
   \W(\quad {}\phlor A(in|ii|\ell_{g1})
\\ && \qquad {} \lor
                     A(in|ii|\ell_{g2})
\\ && \qquad {} \lor
   C[g_{1:},\ell_{g1}/g,in] \lor D[g_{2:},\ell_{g2}/g,in]~)
\\&& {} \land [in|\ell_{g1}|\ell_{g2}|out]
}
\RLEQNS{
   \W(C) &\defs& [r|\rr:]
                 \land
                 \left(\bigvee_{i\in 0\dots} C^i\right)
\\ ii &\defs& s'=s
\\
\\ \Atm a &\defs&\W(A(r|a|\rr:))
\\
\\ C \cseq D
   &\defs&
   \W(~    A(r|ii|\rr1)
      \lor C[\rr1/r]
      \lor A(\rr{1:}|ii|\rr2)
      \lor D[\rr2/r]
      \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(r|ii|\rr1) \lor A(r|ii|\rr2)
\\ && \qquad {} \lor
   C[\rr1/r] \lor D[\rr2/r]
\\ && \qquad {} \lor A(\rr{1:}|ii|\rr:) \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C \parallel D
   &\defs&
   \W(\quad\phlor A(r|ii|\rr1,\rr2)
\\ && \qquad {}\lor
   C[\rr1/r]
   \lor D[\rr2/r]
\\ && \qquad {}\lor
   A(\rr{1:},\rr{2:}|ii|\rr:)~)
\\
\\ C^*
   &\defs&
   \W(\quad  \phlor A(r|ii|\rr1) \lor A(\rr1|ii|\rr:)
\\ && \qquad {}\lor C[\rr1/r]    \lor A(\rr{1:}|ii|\rr1) ~)
\\
\\ \cskip
   &\defs&
   \Atm{ii}
}
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

defnVChc d [p,q]
 = ldefn shVChc $ wp
    $ mkOr [ mkA inp ii lg1
           , mkA inp ii lg2
           , PSub p sub1
           , PSub q sub2 ]
 where
   sub1 = [("g",g1'),("in",lg1)]
   sub2 = [("g",g2'),("in",lg2)]

g1 = xxxsplit1 g
g2 = xxxsplit2 g
lg1 = new1 g1
lg2 = new1 g2
g1' = new2 g1
g2' = new2 g2

invVChc = leInv [leElem inp, leElem lg1, leElem lg2, leElem out]

vChcEntry :: (Show s, Ord s) => (String, Entry s)
vChcEntry
 = ( nVChc
   , PredEntry [] ppVChc [] defnVChc (pNoChg nVChc) )
\end{code}


\newpage
\HDRc{Coding Parallel Composition}

\RLEQNS{
   C \parallel D
   &\defs&
   \W(\quad\phlor A(in|ii|\ell_{g1},\ell_{g2})
\\ && \qquad {}\lor
   C[g_{1::},\ell_{g1},\ell_{g1:}/g,in,out]
   \lor D[g_{2::},\ell_{g2},\ell_{g2:}/g,in,out]
\\ && \qquad {}\lor
   A(\ell_{g1:},\ell_{g2:}|ii|out)~)
\\&& {} \land [in|(\ell_{g1}|\ell_{g1:}),(\ell_{g2}|\ell_{g2:})|out]
}
\RLEQNS{
   \W(C) &\defs& [r|\rr:]
                 \land
                 \left(\bigvee_{i\in 0\dots} C^i\right)
\\ ii &\defs& s'=s
\\
\\ \Atm a &\defs&\W(A(r|a|\rr:))
\\
\\ C \cseq D
   &\defs&
   \W(~    A(r|ii|\rr1)
      \lor C[\rr1/r]
      \lor A(\rr{1:}|ii|\rr2)
      \lor D[\rr2/r]
      \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(r|ii|\rr1) \lor A(r|ii|\rr2)
\\ && \qquad {} \lor
   C[\rr1/r] \lor D[\rr2/r]
\\ && \qquad {} \lor A(\rr{1:}|ii|\rr:) \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C \parallel D
   &\defs&
   \W(\quad\phlor A(r|ii|\rr1,\rr2)
\\ && \qquad {}\lor
   C[\rr1/r]
   \lor D[\rr2/r]
\\ && \qquad {}\lor
   A(\rr{1:},\rr{2:}|ii|\rr:)~)
\\
\\ C^*
   &\defs&
   \W(\quad  \phlor A(r|ii|\rr1) \lor A(\rr1|ii|\rr:)
\\ && \qquad {}\lor C[\rr1/r]    \lor A(\rr{1:}|ii|\rr1) ~)
\\
\\ \cskip
   &\defs&
   \Atm{ii}
}
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
defnVPar d [p,q]
 = ldefn shVPar $ wp
    $ mkOr [ mkA inp ii (set [lg1,lg2])
           , PSub p sub1
           , PSub q sub2
           , mkA s12' ii out ]
 where
   sub1 = [("g",g1''),("in",lg1),("out",lg1')]
   sub2 = [("g",g2''),("in",lg2),("out",lg2')]

lg1' = new1 g1'
lg2' = new1 g2'
g1'' = new2 g1'
g2'' = new2 g2'
s12' = set [lg1',lg2']

invVPar = leInv [ leElem inp
                , leSet [ lg1, lg1' ]
                , leSet [ lg2, lg2' ]
                , leElem out
                ]

vParEntry :: (Show s, Ord s) => (String, Entry s)
vParEntry
 = ( nVPar
   , PredEntry [] ppVPar [] defnVPar (pNoChg nVPar) )
\end{code}

\newpage
\HDRc{Coding Iteration}

\RLEQNS{
   C^*
   &\defs&
   \W(\quad  \phlor A(in|ii|out)
\\ && \qquad {}\lor A(in|ii|\ell_g)
\\ && \qquad {}\lor C[g_{:},\ell_g,in/g,in,out]~)
\\&& {} \land [in|\ell_g|out]
}
\RLEQNS{
   \W(C) &\defs& [r|\rr:]
                 \land
                 \left(\bigvee_{i\in 0\dots} C^i\right)
\\ ii &\defs& s'=s
\\
\\ \Atm a &\defs&\W(A(r|a|\rr:))
\\
\\ C \cseq D
   &\defs&
   \W(~    A(r|ii|\rr1)
      \lor C[\rr1/r]
      \lor A(\rr{1:}|ii|\rr2)
      \lor D[\rr2/r]
      \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(r|ii|\rr1) \lor A(r|ii|\rr2)
\\ && \qquad {} \lor
   C[\rr1/r] \lor D[\rr2/r]
\\ && \qquad {} \lor A(\rr{1:}|ii|\rr:) \lor A(\rr{2:}|ii|\rr:) ~)
\\
\\ C \parallel D
   &\defs&
   \W(\quad\phlor A(r|ii|\rr1,\rr2)
\\ && \qquad {}\lor
   C[\rr1/r]
   \lor D[\rr2/r]
\\ && \qquad {}\lor
   A(\rr{1:},\rr{2:}|ii|\rr:)~)
\\
\\ C^*
   &\defs&
   \W(\quad  \phlor A(r|ii|\rr1) \lor A(\rr1|ii|\rr:)
\\ && \qquad {}\lor C[\rr1/r]    \lor A(\rr{1:}|ii|\rr1) ~)
\\
\\ \cskip
   &\defs&
   \Atm{ii}
}
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
--
defnVIter d [p]
 = ldefn shVIter $ wp
    $ mkOr [ mkA inp ii out
           , mkA inp ii lg
           , PSub p sub
           ]
 where
   sub = [("g",g'),("in",lg),("out",inp)]

invVIter = leInv [ leElem inp
                 , leElem lg
                 , leElem out
                 ]

vIterEntry :: (Show s, Ord s) => (String, Entry s)
vIterEntry
 = ( nVIter
   , PredEntry [] ppVIter [] defnVIter (pNoChg nVIter) )
\end{code}



\newpage
\HDRc{The Predicate Dictionary}\label{hc:WWW-pred-dict}

\begin{code}
dictVP, dictVPCalc :: (Ord s, Show s) => Dict s
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
                  , vSeqEntry
                  , vChcEntry
                  , vParEntry
                  , vIterEntry
                  ]

dictVPCalc = makeDict [ vAtmCalcEntry
                      , vSkipCalcEntry
                      ]
\end{code}



\HDRb{Reductions for WWW}\label{hb:WWW-reduce}

\HDRc{Recognisers for WWW}\label{hc:v-recog}

\RLEQNS{
   ls'=ls\ominus(S_1,S_2)
   &\rightsquigarrow&
   \seqof{S_1,S_2}
   & \ecite{sswap-$;$-prop.}
}
\begin{code}
mtchLabelSetSSwap :: Eq s => Recogniser s
mtchLabelSetSSwap (Equal v' (App nm [v, s1, s2]))
 | v == ls && v' == ls'  =  Just [Atm s1, Atm s2]
mtchLabelSetSSwap _      =  Nothing
\end{code}

\newpage
\HDRc{\texttt{vReduce}}\label{hc:vReduce}

\begin{code}
vReduce :: (Ord s, Show s) => RWFun s
        -- Dict s
        -- -> Pred s    -- Invariant
        -- -> Pred s    -- Target Predicate
        -- -> Maybe (String, Pred s, Bool)
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
\begin{code}
vReduce vd inv (Comp nx [ Atm ee               -- X(E
                        , as                   --  |a
                        , Atm (App ns [l1,l2]) --  | E,L or L,E
                        , Atm en               --  |N)
                        ])
 | nx == nX && ns == setn && isSingleton ee && isSingleton en
   && l1==e && invTrims vd inv l1 l2
    = lred "Inv collapses X to A" equivA
 | nx == nX && ns == setn && isSingleton ee && isSingleton en
   && l2==e && invTrims vd inv l2 l1
    = lred "Inv collapses X to A" equivA
 where
   e = theSingleton ee
   n = theSingleton en
   equivA = mkA e as n
\end{code}


\newpage
\HDRd{General Stuff}~

If $a$ and $b$ have alphabet $\setof{s,s'}$,
then
$(a \seq b)[G,L,M/g,in,out) = a\seq b$.
\begin{code}
vReduce d _ (PSub ab@(Comp ns [PVar a, PVar b]) sub)
 | ns == nSeq && isSS' a && isSS' b && isStaticSub sub
   =  lred "a;b is static-free" ab
 where
   ss' = ["s","s'"]
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

\HDRc{The Reduction Entry}\label{hc:WWW-reduce-ent}

\begin{code}
vRedEntry :: (Ord s, Show s) => Dict s
vRedEntry = entry laws $ LawEntry [vReduce] [] []
\end{code}


\HDRb{Conditional Reductions for WWW}\label{hb:WWW-creduce}

\begin{code}
vCReduce :: CRWFun s
\end{code}

Default case: no change.
\begin{code}
vCReduce _ mpr = Nothing
\end{code}

\HDRc{The Conditional Reduction Entry}\label{hc:WWW-reduce-ent}

\begin{code}
vCRedEntry :: (Ord s, Show s) => Dict s
vCRedEntry = entry laws $ LawEntry [] [vCReduce] []
\end{code}



\HDRb{Loop Unrolling for Views}\label{hb:WWW-unroll}

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
vUnroll :: Ord s => String -> RWFun s
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

\HDRc{The Unroll Entry}\label{hc:WWW-reduce-ent}

\begin{code}
vLoopEntry :: (Ord s, Show s) => Dict s
vLoopEntry = entry laws $ LawEntry [] [] [wUnroll,vUnroll]
\end{code}


\HDRb{Dictionary for Views}\label{hb:View-Dict}

\begin{code}
vDict :: (Ord s, Show s) => Dict s
vDict
 =  dictVersion "Views 0.3"
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


\HDRb{WWW Calculator}\label{hb:WWW-CALC}


\begin{code}
vshow :: (Show s, Ord s) => Pred s -> String
vshow = pmdshow 80 vDict noStyles . buildMarks

vput :: (Show s, Ord s) => Pred s -> IO ()
vput = putStrLn . vshow

vcalc pr = calcREPL vDict [noInvariant] $ buildMarks pr

ivcalc inv pr
 = calcREPL vDict [(labelSetInv, inv)] $ buildMarks pr

vputcalc :: (Ord s, Show s) => Pred s -> IO ()
vputcalc pr = printREPL vDict [noInvariant] $ buildMarks pr

ivputc inv pr
 = printREPL vDict [(labelSetInv, inv)] $ buildMarks pr

vsavecalc fp pr
 = do calc <- vcalc pr
      saveCalc fp calc

vsimp :: (Show s, Ord s) => Pred s -> (String, Pred s)
vsimp pr
  = case simplify vDict 42 $ buildMarks pr of
     Nothing               ->  ("", pr)
     Just (_,what,(pr',_)) ->  (what,pr')
vsimp2 :: (Show s, Ord s) => (String, Pred s) -> (String, Pred s)
vsimp2 = vsimp . snd

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

subII :: (Show s, Ord s) => Pred s
subII = PSub mkSkip [("g",g'1),("out",lg)]

-- an invariant that always fails
noGood _ _ _ = Just False

xcalc :: (Ord s, Show s) => Pred s -> IO ()
xcalc = printREPL vDict [(noGood, F)] . buildMarks
\end{code}

\begin{code}
--defvseq :: (Ord s, Show s) => [Pred s] -> Pred s
defvseq = defnVSeq (vDict :: Dict ())
--athenbBody :: (Ord s, Show s) => Pred s
athenbBody = case defvseq [actionA,actionB] of
              Just (_,Comp _ [body],_)  ->  body
              _                         ->  PVar "??"

testpr = PSub (mkOr [pr, mkSeq pr pr]) [("in",lg)]
 where pr = mkA inp ii out

disp Nothing = putStrLn "\nNo change"
disp (Just (before,_,after))
 = do putStrLn ""
      vput $ fst before
      putStrLn "\n\tbecomes\n"
      vput $ fst after

test :: Maybe (BeforeAfter ())
test = simplify vDict 42 $ buildMarks testpr
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
\\ \Atm a &\defs&\W(A(in|a|out)) \land [in|out]
}
\noindent
to:
\RLEQNS{
   \W(C) &\defs& \true * C
\\ \Atm a &\defs&\W(\Skip \lor A(in|a|out)) \land [in|out]
}
\noindent
the calculation outcomes
for \texttt{athenb}, \texttt{aorb}, \texttt{awithb} and \texttt{itera} are unchanged,
and consequently so are all the other calculations.

\HDRc{Atomic Actions}

\begin{verbatim}
invAtom = [in|out]
\end{verbatim}
\begin{code}
actionA = atom a
actionB = atom b
\end{code}
\begin{verbatim}
Q(actionA) = A(in|a|out)
\end{verbatim}
\begin{code}
q_actionA = mkA inp a out
q_actionB = mkA inp b out
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
 = [in|out] /\
   ( II \/ A(in|a|out) )
\end{verbatim}

\newpage
\HDRc{Sequential Composition}

\begin{verbatim}
invVSeq = [in|lg|out]
invVAtom = [in|out]
invVAtom.a = [in|lg]
invVatom.b = [lg|out]
\end{verbatim}
\begin{code}
athenb = actionA `vseq` actionB
\end{code}
\begin{verbatim}
Q(athenb) = A(in|a|lg) \/ A(lg|b|out)
\end{verbatim}
\begin{code}
q_athenb
  = mkOr [ mkA inp a  lg
         , mkA lg  b out ]
\end{code}

\begin{verbatim}
q_athenb^2 = X(in|a;b|in,lg|out)
\end{verbatim}
The invariant means that the removal of $\ell_g$ above is redundant,
so the $X$ becomes an $A$
\begin{code}
q_athenb_2 = mkA inp ab out
ab = mkSeq a b
\end{code}

\begin{verbatim}
q_athenb^3 = false
\end{verbatim}
\begin{code}
v_athenb
 = mkOr [ mkSkip
        , q_athenb
        , q_athenb_2 ]
\end{code}
\begin{verbatim}
v_athenb
 = [in|lg|out] /\
   ( II \/ A(in|a|lg) \/ A(lg|b|out) \/ A(in|a ; b|out) )
\end{verbatim}


\newpage
\HDRc{Non-deterministic Choice}

\begin{verbatim}
invVChc = [in|lg1|lg2|out]
\end{verbatim}
\begin{code}
aorb = actionA `vchc` actionB
\end{code}
\begin{verbatim}
Q(aorb) = A(in|ii|lg1) \/ A(in|ii|lg2) \/ A(lg1|a|out) \/ A(lg2|b|out)
\end{verbatim}
\begin{code}
q_aorb
  = mkOr [ mkA inp ii lg1
         , mkA inp ii lg2
         , mkA lg1  a out
         , mkA lg2  b out ]
\end{code}

\begin{verbatim}
q_aorb^2 = X(in|ii ; a|in,lg1|out) \/ X(in|ii ; b|in,lg2|out)
\end{verbatim}
We manually note that \texttt{ii;a = a} and if \texttt{in} is in \texttt{ls},
then the invariant ensures that \texttt{lg1} (or \texttt{lg2}) is not,
and so the removal of \texttt{in,lg1}
can be replaced by \texttt{in}, and so we can use the A-form:
\begin{verbatim}
X(in|ii;a|in,lg1|out) = A(in|a|out)
\end{verbatim}
\begin{code}
q_aorb_2
  = mkOr [ mkA inp a out
         , mkA inp b out ]
\end{code}

\begin{verbatim}
q_aorb^3 = false
\end{verbatim}
\begin{code}
v_aorb
 = mkOr [ mkSkip
        , q_aorb
        , q_aorb_2 ]
\end{code}
\begin{verbatim}
v_aorb
 = [in|lg1|lg2|out] /\
   ( II \/ A(in|ii|lg1) \/ A(in|ii|lg2)
        \/ A(lg1|a|out) \/ A(lg2|b|out)
        \/ A(in|a|out)  \/ A(in|b|out) )
\end{verbatim}



\newpage
\HDRc{Parallel Composition}

\begin{verbatim}
invVPar = [in|[lg1|lg1:],[lg2|lg2:]|out]
\end{verbatim}
\begin{code}
awithb = actionA `vpar` actionB
\end{code}
\begin{verbatim}
Q(awithb)
  =    A(in|ii|lg1,lg2)
    \/ A(lg1|a|lg1:) \/ A(lg2|b|lg2:)
    \/ A(lg1:,lg2:|ii|out)
\end{verbatim}
\begin{code}
q_awithb
  = mkOr [ mkA inp ii $ set [lg1,lg2]
         , mkA lg1 a lg1'
         , mkA lg2 b lg2'
         , mkA (set [lg1',lg2']) ii out ]
\end{code}

\begin{verbatim}
q_awithb^2
 =    X(in|ii ; a|in,lg1|lg1:,lg2)
   \/ X(lg1,lg2|b ; a|lg1,lg2|lg1:,lg2:)
   \/ X(in|ii ; b|in,lg2|lg2:,lg1)
   \/ X(lg1,lg2|a ; b|lg1,lg2|lg1:,lg2:)
   \/ X(lg2:,lg1|a ; ii|lg1:,lg2:,lg1|out)
   \/ X(lg1:,lg2|b ; ii|lg1:,lg2:,lg2|out)
\end{verbatim}
We manually note that \texttt{ii;a = a} and if \texttt{in} is in \texttt{ls},
then the invariant ensures that \texttt{lg1} (or \texttt{lg2}) is not,
and so the removal of \texttt{in,lg1}
can be replaced by \texttt{in}, and so we can use the A-form:
\begin{verbatim}
X(in|ii;a|in,lg1|lg1:,lg2) = A(in|a|lg1:,lg2)
\end{verbatim}
\begin{code}
q_awithb_2
  = mkOr [ mkA inp a $ set [lg1',lg2]
         , mkA (set [lg1,lg2]) (mkSeq b a) $ set [lg1',lg2']
         , mkA inp b $ set [lg2',lg1]
         , mkA (set [lg1,lg2]) (mkSeq a  b) $ set [lg1',lg2']
         , mkA (set [lg2',lg1]) a out
         , mkA (set [lg1',lg2]) b out ]
\end{code}

\begin{verbatim}
q_awithb^3
 =    X(in|ii ; b ; a|in,lg1,lg2|lg1:,lg2:)
   \/ X(in|ii ; a ; b|in,lg1,lg2|lg1:,lg2:)
   \/ X(lg1,lg2|b ; a|lg2:,lg1,lg2|out)
   \/ X(lg1,lg2|a ; b|lg1:,lg1,lg2|out)
\end{verbatim}
We do the same tidy-up.
The assymetry here (why \texttt{ii;a;b} and \texttt{a;b} but not \texttt{a;b;ii}?)
is an artefact of the earlier tidy-up we did for \verb"q_awithb_2".
\begin{code}
q_awithb_3
 = mkOr [ mkA inp (mkSeq b a) $ set [lg1',lg2']
        , mkA inp (mkSeq a b) $ set [lg1',lg2']
        , mkA (set [lg1,lg2]) (mkSeq b a) out
        , mkA (set [lg1,lg2]) (mkSeq a b) out ]
\end{code}
\begin{verbatim}
q_awithb^4
 = X(in|ii ; b ; a|in,lg1,lg2|out) \/ X(in|ii ; a ; b|in,lg1,lg2|out)
\end{verbatim}
Tidy up
\begin{code}
q_awithb_4
 = mkOr [ mkA inp (mkSeq b a) out
        , mkA inp (mkSeq a b) out ]
\end{code}
\begin{verbatim}
q_awithb^5 = false
\end{verbatim}
\begin{code}
v_awithb
 = mkOr [ mkSkip
        , q_awithb
        , q_awithb_2
        , q_awithb_3
        , q_awithb_4 ]
\end{code}
\begin{verbatim}
v_awithb
 = [in|[lg1|lg1:],[lg2|lg2:]|out] /\
   ( II \/ A(in|ii|lg1,lg2)           \/ A(lg1:,lg2:|ii|out)
        \/ A(lg1|a|lg1:)              \/ A(lg2|b|lg2:)
        \/ A(in|a|lg1:,lg2)           \/ A(in|b|lg2:,lg1)
        \/ A(lg1,lg2|b ; a|lg1:,lg2:) \/ A(lg1,lg2|a ; b|lg1:,lg2:)
        \/ A(lg2:,lg1|a|out)          \/ A(lg1:,lg2|b|out)
        \/ A(in|b ; a|lg1:,lg2:)      \/ A(in|a ; b|lg1:,lg2:)
        \/ A(lg1,lg2|b ; a|out)       \/ A(lg1,lg2|a ; b|out)
        \/ A(in|b ; a|out)            \/ A(in|a ; b|out) )
\end{verbatim}

\newpage
\HDRc{ Atomic Iteration}

\begin{verbatim}
invVIter = [in|lg|out]
invVAtom = [in|out]
invVatom.a [lg|in]
\end{verbatim}
\begin{code}
itera = viter actionA
\end{code}

\begin{verbatim}
Q(itera) = A(in|ii|out) \/ A(in|ii|lg) \/ A(lg|a|in)
\end{verbatim}
\begin{code}
q_itera
  = mkOr [ mkA inp ii out
         , mkA inp ii lg
         , mkA lg  a  inp ]
\end{code}

\begin{verbatim}
q_itera^2
  =    X(lg|a ; ii|in,lg|out)
    \/ X(lg|a ; ii|in,lg|lg)
    \/ X(in|ii ; a|in,lg|in)
\end{verbatim}
We can simplify to use $A$:
\begin{code}
q_itera_2
 = mkOr [ mkA lg  a out
        , mkA lg  a lg
        , mkA inp a inp ]
\end{code}

\begin{verbatim}
q_itera^3
  =    X(in|ii ; a|in,lg|out)
    \/ X(in|ii ; a|in,lg|lg)
    \/ X(lg|a ; a|in,lg|in)
\end{verbatim}
\begin{code}
q_itera_3
 = mkOr [ mkA inp a  out
        , mkA inp a  lg
        , mkA lg  a2 inp ]
a2 = mkSeq a a
\end{code}

\begin{verbatim}
q_itera^4
 =    X(lg|a ; a|in,lg|out)
   \/ X(lg|a ; a|in,lg|lg)
   \/ X(in|ii ; a ; a|in,lg|in)
\end{verbatim}
\begin{code}
q_itera_4
 = mkOr [ mkA lg  a2 out
        , mkA lg  a2 lg
        , mkA inp a2 inp ]
\end{code}

\begin{verbatim}
q_itera^5
 =    X(in|ii ; a ; a|in,lg|out)
   \/ X(in|ii ; a ; a|in,lg|lg)
   \/ X(lg|a ; a ; a|in,lg|in)
\end{verbatim}
\begin{code}
q_itera_5
 = mkOr [ mkA inp a2 out
        , mkA inp a2 lg
        , mkA lg  a3 inp ]
a3 = mkSeq a2 a
\end{code}

\begin{verbatim}
 q_itera^6
  =    X(lg|a ; a ; a|in,lg|out)
    \/ X(lg|a ; a ; a|in,lg|lg)
    \/ X(in|ii ; a ; a ; a|in,lg|in)
\end{verbatim}
\begin{code}
q_itera_6
 = mkOr [ mkA lg  a3 out
        , mkA lg  a3 lg
        , mkA inp a3 inp ]
\end{code}

We notice that we are getting Q pairs of the following form:
\begin{verbatim}
q_2itera i  -- i in 0..
 =    A(in|a^i|out)   \/ A(in|a^i|lg)   \/ A(lg|a^i+1|in)
   \/ A(lg|a^i+1|out) \/ A(lg|a^i+1|lg) \/ A(in|a^i+1|in)
\end{verbatim}
\begin{code}
as_2itera i
 = [ mkA inp ai  out
   , mkA inp ai  lg
   , mkA lg  ai' inp
   , mkA lg  ai' out
   , mkA lg  ai' lg
   , mkA inp ai' inp ]
 where
   ai  = doa i
   ai' = doa (i+1)

doa 0 = ii
doa n = doa' a (n-1)

doa' as 0 = as
doa' as n = doa' (mkSeq as a) (n-1)

q_2itera = mkOr . as_2itera
\end{code}

\newpage
Putting it all together\dots
\begin{code}
v_itera -- be lazy, be very lazy ! No calculation!
 = mkOr (mkSkip : mk2itera 0)
 where
   mk2itera i = as_2itera i ++ mk2itera (i+1)

v_itera_n i -- finite prefix of behaviour
 = mkOr (mkSkip : concat (map as_2itera [0..i]))
\end{code}
\begin{verbatim}
v_actionA
 = [in|lg|out] /\ [in|out]
   ( II
     \/ A(in|ii|out)
     \/ A(in|ii|lg)
     \/ A(lg|a|in)
     \/ A(lg|a|out)
     \/ A(lg|a|lg)
     \/ A(in|a|in)
     \/ A(in|a|out)
     \/ A(in|a|lg)
     \/ A(lg|a ; a|in)
     \/ A(lg|a ; a|out)
     \/ A(lg|a ; a|lg)
     \/ A(in|a ; a|in)
     \/ A(in|a ; a|out)
     \/ A(in|a ; a|lg)
     \/ A(lg|a ; a ; a|in)
     \/ A(lg|a ; a ; a|out)
     \/ A(lg|a ; a ; a|lg)
     \/ A(in|a ; a ; a|in)
     \/ ... )
\end{verbatim}

\newpage
\HDRc{ Sequence Iteration}

\begin{verbatim}
invVIter = [in|lg|out]
invVSeq = [in|lg|out]
invVAtom = [in|out]
invVSeq.seq = [lg|lg:|in]
invVAtom.seq.a = [lg|lg:]
invVatom.seq.b = [lg:|in]
\end{verbatim}
\begin{code}
iterseq = viter v_athenb
inv_iterseq
 = leInv [ leElem inp
         , leElem lg
         , leElem lg'
         , leElem out ]
lg' = new1 g'
\end{code}

\begin{verbatim}
Q(iterseq) =    A(in|ii|out) \/ A(in|ii|lg)
             \/ A(lg|a|lg:) \/ A(lg:|b|in) \/ A(lg|a;b|in)
\end{verbatim}
\begin{code}
q_iterseq
 = mkOr [ mkA inp ii out
        , mkA inp ii lg
        , mkA lg   a lg'
        , mkA lg  ab inp
        , mkA lg'  b inp ]
\end{code}

\begin{verbatim}
q_iterseq^2
 =    X(lg:|b ; ii|in,lg:|out) \/ X(lg|a ; b ; ii|in,lg|out)
   \/ X(lg:|b ; ii|in,lg:|lg) \/ X(lg|a ; b ; ii|in,lg|lg)
   \/ X(in|ii ; a|in,lg|lg:)
   \/ X(lg|a ; b|lg,lg:|in)
   \/ X(in|ii ; a ; b|in,lg|in)
\end{verbatim}
\begin{code}
q_iterseq_2
 = mkOr [ mkA inp a  lg'
        , mkA inp ab inp
        , mkA lg  ab out
        , mkA lg  ab lg
        , mkA lg  ab inp
        , mkA lg' b  lg
        , mkA lg' b  out  ]
\end{code}

\begin{verbatim}
q_iterseq^3
 =    X(lg|a ; b|lg,lg:|out)
   \/ X(in|ii ; a ; b|in,lg|out)
   \/ X(lg|a ; b|lg,lg:|lg)
   \/ X(in|ii ; a ; b|in,lg|lg)
   \/ X(lg:|b ; a|in,lg:|lg:) \/ X(lg|a ; b ; a|in,lg|lg:)
   \/ X(in|ii ; a ; b|in,lg|in)
   \/ X(lg:|b ; a ; b|in,lg:|in) \/ X(lg|a ; b ; a ; b|in,lg|in)
\end{verbatim}
\begin{code}
q_iterseq_3
 = mkOr [ mkA inp ab   out
        , mkA inp ab   lg
        , mkA inp ab   inp
        , mkA lg  ab   out
        , mkA lg  ab   lg
        , mkA lg  aba  lg'
        , mkA lg  abab inp
        , mkA lg' ba   lg'
        , mkA lg' bab  inp ]
ba = mkSeq b a
aba = mkSeq ab a
bab = mkSeq ba b
abab = mkSeq aba b
\end{code}

\begin{verbatim}
q_iterseq^4
 =    X(lg|a ; b ; a ; b|in,lg|out)
   \/ X(lg:|b ; a ; b|in,lg:|out)
   \/ X(lg|a ; b ; a ; b|in,lg|lg)
   \/ X(lg:|b ; a ; b|in,lg:|lg)
   \/ X(lg|a ; b ; a ; b|in,lg|in)
   \/ X(lg:|b ; a ; b|in,lg:|in)
   \/ X(in|ii ; a ; b|in,lg|out)
   \/ X(in|ii ; a ; b|in,lg|lg)
   \/ X(in|ii ; a ; b ; a|in,lg|lg:)
   \/ X(in|ii ; a ; b ; a ; b|in,lg|in)
   \/ X(lg|a ; b ; a|lg,lg:|lg:)
   \/ X(lg|a ; b ; a ; b|lg,lg:|in)
\end{verbatim}
