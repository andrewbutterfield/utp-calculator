\HDRa{Views}\label{ha:Views}
\begin{code}
module Views where
import Utilities
-- import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
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
dbg str x = trace (str++show x) x
\end{code}

We do a quick run-down of the Commands\cite{conf/popl/Dinsdale-YoungBGPY13}.

\HDRb{Syntax}

\def\Atm#1{Atm(#1)}

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

\begin{eqnarray*}
   s &\in& \mathcal S
\\ \sem{-} &:& \Atom \fun \mathcal S \fun \mathcal P(\mathcal S)
\\ S \ominus (T|V)
   &\defs& (S \setminus T) \cup V
\end{eqnarray*}

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
new1n = "new1"
new1 g = App new1n [g]
gNew1 [g] = new1 g

new2n = "new2"
new2 g = App new2n [g]
gNew2 [g] = new2 g

split1n = "split1"
split1 g = App split1n [g]
gSplit1 [g] = split1 g

split2n = "split2"
split2 g = App split2n [g]
gSplit2 [g] = split2 g
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
    , (split1n,(ExprEntry subAny showGSplit1 (justMakes gSplit1) noEq))
    , (split2n,(ExprEntry subAny showGSplit2 (justMakes gSplit2) noEq))
    ]
\end{code}

\HDRc{The Expression Dictionary}\label{hc:WWW-expr-dict}

\begin{code}
dictVE :: (Ord s, Show s) => Dict s
dictVE = vSetDict `dictMrg` vGenDict
\end{code}


\newpage
\HDRb{Alphabet}

\begin{eqnarray*}
   s, s' &:& \mathcal S
\\ ls, ls' &:& \mathcal P (Lbl)
\\ g &:& Gen
\\ in, out &:& Lbl
\end{eqnarray*}

\begin{code}
s   = Var "s"  ; s'  = Var "s'"
ls  = Var "ls" ; ls' = Var "ls'"
g   = Var "g"
inp = Var "in" -- "in" is a Haskell keyword
out = Var "out"
\end{code}

We define our dictionary alphabet entries,
and also declare that the predicate variables $a$, $a$ and $a$
will refer to atomic state-changes, and so only have alphabet $\setof{s,s'}$.
\begin{code}
vAlfDict
 = dictMrg dictAlpha dictAtomic
 where
   dictAlpha = stdAlfDictGen ["s"] ["ls"] vStatic
   dictAtomic = makeDict [ pvarEntry "a" ss'
                         , pvarEntry "b" ss'
                         , pvarEntry "c" ss' ]
   ss' = ["s", "s'"]

vStatic = ["g","in","out"]
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

\HDRd{Updating the Standard UTP Dictionary}~

\begin{code}
vStdUTPDict :: (Show s, Ord s) => Dict s
vStdUTPDict
  = makeDict [ skipEntry'
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

-- we don't want to expand the definition of this, or simplify it
defnX = pNoChg nX
simpX = pNoChg nX

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

\NOTE{
Redo this to handle $\W(P) = \true * (\Skip \lor P)$
}
\begin{code}
wUnroll :: Ord s => String -> RWFun s
wUnroll _ _ _ = Nothing
\end{code}

\newpage
\HDRb{WwW Semantic Definitions}

The definitions, using the new shorthands:
\begin{eqnarray*}
   \W(C) &\defs& \true * (\Skip \lor C)
\\       &=& \bigvee_{i\in 0\dots} \Skip\seq C^i
\\ ii &\defs& s'=s
\\
\\ \Atm a &\defs&\W(A(in|a|out)) \land [in|out]
\\ \cskip
   &\defs&
   \W(A(in|ii|out)) \land [in|out]
\\
\\ C \cseq D
   &\defs&
   \W(C[g_{:1},\ell_g/g,out] \lor D[g_{:2},\ell_g/g,in])
\\&& {}\land [in|\ell_g|out]
\\
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(in|ii|\ell_{g1})
\\ && \qquad {} \lor
                     A(in|ii|\ell_{g2})
\\ && \qquad {} \lor
   C[g_{1:},\ell_{g1}/g,in] \lor D[g_{2:},\ell_{g2}/g,in]~)
\\&& {} \land [in|\ell_{g1}|\ell_{g2}|out]
\\
\\ C \parallel D
   &\defs&
   \W(\quad\phlor A(in|ii|\ell_{g1},\ell_{g2})
\\ && \qquad {}\lor
   C[g_{1::},\ell_{g1},\ell_{g1:}/g,in,out]
   \lor D[g_{2::},\ell_{g2},\ell_{g2:}/g,in,out]
\\ && \qquad {}\lor
   A(\ell_{g1:},\ell_{g2:}|ii|out)~)
\\&& {} \land [in|(\ell_{g1}|\ell_{g1:}),(\ell_{g2}|\ell_{g2:})|out]
\\
\\ C^*
   &\defs&
   \W(\quad  \phlor A(in|ii|out)
\\ && \qquad {}\lor X(in|ii|\ell_g)
\\ && \qquad {}\lor C[g_{:},\ell_g,in/g,in,out]~)
\\&& {} \land [in|\ell_g|out]
\end{eqnarray*}

\newpage
\HDRc{Coding Label-Set Invariants}

\RLEQNS{
   i \in I_\tau &::=& \tau \mid \otimes(i,\ldots,i) \mid \cup (i,\ldots,i)
}
We shall code this structure directly in Haskell
as it eases invariant satisfaction calculation.
\begin{code}
data I t = I t | U [I t] | X [I t] deriving Show
\end{code}
We refer to these three variants as
 \texttt{IElem}, \texttt{IDisj} and \texttt{IJoin}:
\begin{code}
nIElem = "IElem"
nIDisj = "IDIsj"
nIJoin = "IJoin"

isLSInv (Comp n _)
 | n==nIElem || n==nIDisj || n==nIJoin  =  True
isLSInv _ = False

isIElem (Comp n [_])   | n==nIElem = True; isIElem _ = False
isIDisj (Comp n (_:_)) | n==nIDisj = True; isIDisj _ = False
isIJoin (Comp n (_:_)) | n==nIJoin = True; isIJoin _ = False

ielem e          =  Comp nIElem [Atm e]
idisj prs@(_:_)  =  Comp nIDisj prs
ijoin prs@(_:_)  =  Comp nIJoin prs

ppIElem sCP d p [pr@(Atm e)] = sCP 0 1 pr
ppIElem _ _ _ _ = pps styleRed $ ppa ("invalid-"++nIElem)

precInv = -1

ppIDisj sCP d p prs = ppclosed "[" "]" "|" $ map (sCP precInv 1) prs

ppIJoin sCP d p prs
 = paren p precInv
     $ ppopen  "," $ ppwalk 1 (sCP precInv) prs

vIElemEntry :: (Show s, Ord s) => (String, Entry s)
vIElemEntry
 = ( nIElem
   , PredEntry anyVars ppIElem vStatic (pNoChg nIElem) (pNoChg nIElem) )

vIDisjEntry :: (Show s, Ord s) => (String, Entry s)
vIDisjEntry
 = ( nIDisj
   , PredEntry anyVars ppIDisj vStatic (pNoChg nIDisj) (pNoChg nIDisj) )

vIJoinEntry :: (Show s, Ord s) => (String, Entry s)
vIJoinEntry
 = ( nIJoin
   , PredEntry anyVars ppIJoin vStatic (pNoChg nIJoin) (pNoChg nIJoin) )
\end{code}

\newpage
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
 | nm == nA = if lsat d e inv && lsat d n inv
              then Just True
              else Just False
labelSetInv d inv pr@(Comp nm [Atm e,_,_,Atm a])
 | nm == nX = if lsat d e inv && lsat d a inv
              then Just True
              else Just False
labelSetInv _ _ _ = Nothing
\end{code}

Now we have to code up \textbf{lsat}:
\RLEQNS{
}
\begin{code}
lsat :: (Ord s, Show s) => Dict s -> Expr s -> Pred s -> Bool
lsat d ls inv = isJust $ loccChk $ locc d ls inv
\end{code}

We want to take an invariant over labels
and a label-set to get the same structure over booleans.
This is the label occupancy structure:
\RLEQNS{
   occ &:& \power \Int \fun I_\Int \fun I_\Bool
\\ occ_L~\ell &\defs& \ell \in L
\\ occ_L~\otimes(i_1,\ldots,i_n)
   &\defs&
   \otimes(occ_L~i_1,\ldots,occ_L~i_n)
\\ occ_L~\cup(i_1,\ldots,i_n)
   &\defs&
   \cup(occ_L~i_1,\ldots,occ_L~i_n)
}
\begin{code}
-- occ :: Eq t => [t] -> I t -> I Bool
locc :: (Ord s, Show s) => Dict s -> Expr s -> Pred s -> I Bool

-- occ ls (I ell) = I (ell `elem`ls)
locc d lset (Comp nm [Atm ell])
 | nm == nIElem
   = case  esimp d $ subset ell lset of
      (_,B b)  ->  I b
      _        ->  I False -- no occupancy!

-- occ ls (U invs) = U $ map (occ ls) invs
locc d lset (Comp nm prs)
 | nm == nIJoin  =  U $ map (locc d ls) prs

-- occ ls (X invs) = X $ map (occ ls) invs
 | nm == nIDisj  =  X $ map (locc d ls) prs

locc d lset pr  = I False -- no occupancy
\end{code}

\newpage
We now take a $I_\Bool$ and check that occupancy
satisfies the constraints in order
to reduce it to a boolean.
In effect we look for failures
(can only come from $\oplus$)
and propagate these up.
\RLEQNS{
   occChk &:& I_\Bool \fun (\setof{ok,fail}\times \Bool)
\\ occChk(b) &\defs& (ok,true)
\\ occChk(\cup(i_1,\ldots,i_n))
   &\defs&
   (fail,\_),
   \textbf{ if }\exists j @ occChk(i_j) = (fail,\_)
\\ && (ok,b_1 \lor \dots \lor b_n),
   \textbf{ if }\forall j @ occChk(i_j) = (ok,b_j)
\\ occChk(\otimes(i_1,\ldots,i_n))
   &\defs&
   (fail,\_),
   \textbf{ if }\exists j @ occChk(i_j) = (fail,\_)
\\&& (fail,\_) \mbox{ if more than one $(ok,true)$}
\\&& (ok,false) \mbox{ if all are $(ok,false)$}
\\&& (ok,true) \mbox{ if  exactly one $(ok,true)$}
}
\begin{code}
loccChk :: I Bool -> Maybe Bool
loccChk (I b) = Just b
loccChk (U occs) -- we go all monadic !!!
 = do ps <- sequence $ map loccChk occs
      return $ any id ps
loccChk (X occs)
 = do ps <- sequence $ map loccChk occs
      let ps' = filter id ps
      case length ps' of
        0  ->  return False
        1  ->  return True
        _  ->  fail "not-exclusive"
\end{code}


\newpage
\HDRc{Coding Atomic Semantics}

\RLEQNS{
 \Atm a &\defs&\W(A(in|a|out)) \land [in|out]
}

\begin{code}
nAtom = "Atom" -- internal abstract name
isAtom (Comp n [_]) | n==nAtom = True; isAtom _ = False

atom pr = Comp nAtom [pr]

ppAtom sCP d p [pr] = ppbracket "<" (sCP 0 1 pr) ">"
ppAtom _ _ _ _ = pps styleRed $ ppa ("invalid-"++nAtom)

defnAtom d [a]
 = ldefn nAtom $ wp $ mkA inp a out

invAtom = idisj [ielem inp, ielem out]

wp x = Comp "W" [x]

sinp = sngl inp
sout = sngl out

vAtmEntry :: (Show s, Ord s) => (String, Entry s)
vAtmEntry
 = ( nAtom
   , PredEntry ["s","s'"] ppAtom [] defnAtom (pNoChg nAtom) )
\end{code}


\newpage
\HDRc{Coding Skip}

\RLEQNS{
   \cskip
   &\defs&
   \W(A(in|ii|out)) \land [in|out]
}
\begin{code}
nVSkip = "VSkip" -- internal abstract name
isVSkip (_,Comp n [_]) | n==nVSkip = True; isVSkip _ = False

vskip mpr = Comp nVSkip [mpr]

ppVSkip d ms p [mpr] = ppa "<skip>"
ppVSkip d ms p mprs = pps styleRed $ ppa ("invalid-"++nSkip)

defnVSkip d [a]
 = ldefn nVSkip $ wp $ mkA inp ii out

invVSkip = idisj [ielem inp, ielem out]

vSkipEntry :: (Show s, Ord s) => (String, Entry s)
vSkipEntry
 = ( nVSkip
   , PredEntry ["s","s'"] ppVSkip [] defnVSkip (pNoChg nSkip) )

-- atomic skip
nii= "ii"
ii = PVar nii
\end{code}




\newpage
\HDRc{Coding Sequential Composition}

\RLEQNS{
   C \cseq D
   &\defs&
   \W(C[g_{:1},\ell_g/g,out] \lor D[g_{:2},\ell_g/g,in])
   \land [in|\ell_g|out]
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
g'1 = split1 g'
g'2 = split2 g'

invVSeq = idisj[ielem inp, ielem lg, ielem out]

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
   \W(\quad {}\phlor X(in|\emptyset|ii|in|\ell_{g1})
\\ && \qquad {} \lor
                     X(in|\emptyset|ii|in|\ell_{g2})
\\ && \qquad {} \lor
   C[g_{1:},\ell_{g1}/g,in] \lor D[g_{2:},\ell_{g2}/g,in]~)
\\ && {} \lor  [in|\ell_{g1}|\ell_{g2}|out]
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
    $ mkOr [ mkX inp ii inp lg1
           , mkX inp ii inp lg2
           , PSub p sub1
           , PSub q sub2 ]
 where
   sub1 = [("g",g1'),("in",lg1)]
   sub2 = [("g",g2'),("in",lg2)]

g1 = split1 g
g2 = split2 g
lg1 = new1 g1
lg2 = new1 g2
g1' = new2 g1
g2' = new2 g2

invVChc = idisj [ielem inp, ielem lg1, ielem lg2, ielem out]

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
   \W(\quad\phlor X(in|\emptyset|ii|in|\ell_{g1},\ell_{g2})
\\ && \qquad {}\lor
   C[g_{1::},\ell_{g1},\ell_{g1:}/g,in,out]
   \lor D[g_{2::},\ell_{g2},\ell_{g2:}/g,in,out]
\\ && \qquad {}\lor
   X(\ell_{g1:},\ell_{g2:}|\emptyset|ii|\ell_{g1:},\ell_{g2:}|out)~)
\\&& {} \land [in \mid [\ell_{g1}|\ell_{g1:}],[\ell_{g2}|\ell_{g2:}] \mid out]
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
    $ mkOr [ mkX inp ii inp (set [lg1,lg2])
           , PSub p sub1
           , PSub q sub2
           , mkX s12' ii s12' out ]
 where
   sub1 = [("g",g1''),("in",lg1),("out",lg1')]
   sub2 = [("g",g2''),("in",lg2),("out",lg2')]

lg1' = new1 g1'
lg2' = new1 g2'
g1'' = new2 g1'
g2'' = new2 g2'
s12' = set [lg1',lg2']

invVPar = idisj [ ielem inp
                , ijoin [ idisj [ ielem lg1, ielem lg1' ]
                        , idisj [ ielem lg2, ielem lg2' ]
                        ]
                , ielem out
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
   \W(\quad  \phlor X(in|\emptyset|ii|in|out)
\\ && \qquad {}\lor X(in|\emptyset|ii|in|\ell_g)
\\ && \qquad {}\lor C[g_{:},\ell_g,in/g,in,out]~)
\\ && {} \land [in|\ell_g|out]
}


\HDRc{The Predicate Dictionary}\label{hc:WWW-pred-dict}

\begin{code}
dictVP :: (Ord s, Show s) => Dict s
dictVP = makeDict [ vXEntry
                  , vAEntry
                  , vIElemEntry
                  , vIDisjEntry
                  , vIJoinEntry
                  , vAtmEntry
                  , vSkipEntry
                  , vSeqEntry
                  , vChcEntry
                  , vParEntry
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
        -- Dict s -> Pred s -> Maybe (String, Pred s, Bool)
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
vReduce vd (Comp ns [ (Comp na1 [ (Atm e1)    -- A(E1
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
vReduce vd (Comp ns [ (Comp nx1 [ (Atm e1)    -- X(E1
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
vReduce vd (Comp ns [ (Comp nx1 [ (Atm e1)     -- X(E1
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



\begin{eqnarray*}
   A \land (B \lor C) &=& (A \land B) \lor (A \land C)
\end{eqnarray*}
\begin{code}
vReduce d (Comp na [ pr, (Comp no prs) ])
 | na == nAnd && no == nOr
      =  lred "and-or-distr" $ mkOr $ map f prs
 where f pr' = mkAnd [pr , pr']
\end{code}

\begin{eqnarray*}
   A \seq (B \lor C) &=& (A \seq B) \lor (A \seq C)
\end{eqnarray*}
\begin{code}
vReduce d (Comp ns [ pr, (Comp no prs) ])
 | ns == nSeq && no == nOr
      =  lred ";-or-distr" $  mkOr $ map f prs
 where f pr' = mkSeq pr pr'
\end{code}

\begin{eqnarray*}
  (A \lor B) \seq C &=& (A \seq C) \lor (B \seq C)
\end{eqnarray*}
\begin{code}
vReduce d (Comp ns [ (Comp no prs), pr ])
 | ns == nSeq && no == nOr
      =  lred "or-;-distr" $ mkOr $ map f prs
 where f pr' = mkSeq pr' pr
\end{code}

We prefer sequential chains to associate to the left:
\begin{eqnarray*}
   A \seq (B \seq C) &=& (A \seq B) \seq C
\end{eqnarray*}
\begin{code}
vReduce d (Comp ns1 [ prA, (Comp ns2 [prB, prC]) ])
 | ns1 == nSeq && ns2 == nSeq
     =  lred  ";-left-assoc" $ mkSeq (mkSeq prA prB) prC
\end{code}



\newpage
Default case: no change.
\begin{code}
vReduce _ _ = Nothing
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
vUnroll ns d iter@(Comp nm  [c, pr])
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

vUnroll _ _ _ = Nothing
\end{code}

\HDRc{The Unroll Entry}\label{hc:WWW-reduce-ent}

\begin{code}
vLoopEntry :: (Ord s, Show s) => Dict s
vLoopEntry = entry laws $ LawEntry [] [] [wUnroll,vUnroll]
\end{code}


\HDRb{Dictionary for WWW}\label{hb:WWW-laws}

\begin{code}
vDict :: (Ord s, Show s) => Dict s
vDict
 =  dictVersion "WWW 0.1"
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

vcalc pr = calcREPL vDict noInvariant $ buildMarks pr

ivcalc inv pr
 = calcREPL vDict (labelSetInv, inv) $ buildMarks pr

vputcalc :: (Ord s, Show s) => Pred s -> IO ()
vputcalc pr = printREPL vDict noInvariant $ buildMarks pr

ivputc inv pr
 = printREPL vDict (labelSetInv, inv) $ buildMarks pr

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
\end{code}


\HDRb{Building the Theory}\label{hb:building-WWW}

We need to establish the laws we need for easy calculation
in this theory.
We start with the calculation of the expansion of $\A(B)$%
\footnote{Noting that the full expansion may just become
a single reduction step}%
:
\RLEQNS{
  && \A(B)
\EQ{\texttt{'d'},defn. $\A$}
\\&& \W(ls(in) \land B \land ls'=ls\ominus(in|out))
\EQ{\texttt{'d'}, defn. $\W$}
\\&&\lnot ls(out) * (ls(in) \land B \land ls'=ls\ominus(in|out))
\EQ{\texttt{'l'}, loop unroll, obvious fold as shorthand}
\\&& (ls(in) \land B \land ls'=ls\ominus(in|out) ; \W(\_))
     \cond{\lnot ls(out)} \Skip
\EQ{\texttt{'d'}, defn. $\cond{}$}
\\&& \lnot ls(out) \land ls(in) \land B \land ls'=ls\ominus(in|out) ; \W(\_)
\\&\lor& ls(out) \land \Skip
\EQ{\texttt{'r'}, \ref{hd:prop-new-labels}}
\\&& \lnot ls(out) \land ls(in) \land B \land ls'=ls\ominus(in|out)
     ; ls(out) \land \W(\_)
\\&\lor& ls(out) \land \Skip
\EQ{\texttt{'r'}, $ls(out)\land\W(\_) = ls(out)\land \Skip$, or $c\land(\lnot c * P) = c \land \Skip$}
\\&& \lnot ls(out) \land ls(in) \land B \land ls'=ls\ominus(in|out)
     ; ls(out) \land \Skip)
\\&\lor& ls(out) \land \Skip
\EQ{\texttt{'r'} doing \ref{hd:prop-new-labels} backwards}
\\&& \lnot ls(out) \land ls(in) \land B \land ls'=ls\ominus(in|out)
     ; \Skip
\\&\lor& ls(out) \land \Skip
\EQ{\texttt{'r'} $P;\Skip = P$}
\\&& \lnot ls(out) \land ls(in) \land B \land ls'=ls\ominus(in|out)
\\&\lor& ls(out) \land \Skip
}


\HDRd{Propagate New Labels}\label{hd:prop-new-labels}

Reduction Law:
\RLEQNS{
   P \land ls'=ls\ominus(L_1|L_2) ; Q
   &=&
P \land ls'=ls\ominus(L_1|L_2) ; ls(L_2) \land Q,
\\ &&\textbf{ provided } L_2 \textbf{ is ground}
}

\textbf{Motivation/Justification:}
We want $P \land ls'=ls\ominus(in|out) ; Q$
to propagate the fact that $ls$ has been updated to $Q$.

Some known laws:
\RLEQNS{
   P \land x'=e ; Q &=& P \land x'=e ; Q[e/x]
      ,\textbf{ given } e \textbf{ is ground }
}
We find the above law only works if $e = e[O_m/O]$ which can only happen
if $e$ is ground, i.e., contains no dynamic (pre-)observations.
What we really want is:
\RLEQNS{
   P \land ls'=ls\ominus(in|out) ; Q
   &=&
   P \land ls'=ls\ominus(in|out) ; ls(out) \land Q
}
We have a key property of $\ominus$ we can exploit:
\RLEQNS{
   S' = S \ominus (T|V) &\implies& S'(V)
}
so the remaining general law we need is
$P \land S'(V) ; Q = P \land S'(V) ; S(V) \land Q$,
provided $V$ is ground.
This gives us the desired reduction law above.

\HDRc{Test Constructs}\label{hc:test-constructs}

\begin{code}
pP = PVar "P" ; pQ = PVar "Q"  -- general programs
a = PVar "a"
b = PVar "b"

subII :: (Show s, Ord s) => Pred s
subII = PSub mkSkip [("g",g'1),("out",lg)]

actionA = atom a
actionB = atom b

athenb = actionA `vseq` actionB
\end{code}

\HDRd{Loops---alternative approach}

We note the following result:
\RLEQNS{
   c*P &=& \lim_{n \rightarrow \infty}\bigvee_0^n S^n \seq D
\\ && \textbf{where}
\\ S &=& c \land P
\\ D &=& \lnot c \land \Skip
}
Of interest are the following calculations:
\RLEQNS{
   &&  S^n \seq D
\\ && S \seq S
\\ && S \seq D
}
\begin{code}
--defvseq :: (Ord s, Show s) => [Pred s] -> Pred s
defvseq = defnVSeq (vDict :: Dict ())
--athenbBody :: (Ord s, Show s) => Pred s
athenbBody = case defvseq [actionA,actionB] of
              Just (_,Comp _ [body],_)  ->  body
              _                         ->  PVar "??"
\end{code}
\begin{verbatim}
D(lg) \/ X(in|lg|a|in|lg) \/ D(out) \/ X(lg|out|b|lg|out) ; D(out)
 = "..."
D(out,lg) \/ X(in,out|lg|a|in|lg) \/ D(out) \/ X(lg|out|b|lg|out)
\end{verbatim}

\begin{verbatim}
   D(lg) \/ X(in|lg|a|in|lg) \/ D(out) \/ X(lg|out|b|lg|out)
 ; D(lg) \/ X(in|lg|a|in|lg) \/ D(out) \/ X(lg|out|b|lg|out)
 = "..."
    D(lg) \/ X(in|lg|a|in|lg) \/ D(out,lg)
 \/ X(in,out|lg|a|in|lg) \/ X(in,lg|out|b ; a|in|out,lg)
 \/ D(out,lg) \/ X(in,out|lg|a|in|lg) \/ D(out) \/ X(lg|out|b|lg|out)
 \/ X(lg|out|b|lg|out) \/ X(in|out,lg|a ; b|in,lg|out)
 = "by hand, rearrange"
    D(out) \/ D(lg) \/ D(out,lg)
 \/ X(in|lg|a|in|lg) \/ X(in,out|lg|a|in|lg)
 \/ X(lg|out|b|lg|out)
 \/ X(in|out,lg|a ; b|in,lg|out)
 \/ X(in,lg|out|b ; a|in|out,lg)
 = "absorption --- see below, also X-norm"
    D(out) \/ D(lg)
 \/ X(in|lg|a|in|lg)
 \/ X(lg|out|b|lg|out)
 \/ X(in|out,lg|a ; b|in|out)
 \/ X(in,lg|out|b ; a|in|out,lg) -- shouldn't arise
\end{verbatim}
\RLEQNS{
   X(E|D|a|R|A) \lor X(E\cup F|D|a|R|A)&=& X(E|D|a|R|A)
\\ D(E) \lor D(E \cup F) &=& D(E)
}

The  $X(in,\ell_g|out|b \seq a|in|out,\ell_g)$ case should not arise
because there is no path from $ls(in)$ and $ls(\B{\ell_g})$
that leads to $ls(in,\ell_g)$.


\newpage
\HDRb{Required Laws}

Need reductions of the form:
\begin{eqnarray*}
   \lnot ls(L_1) \land A(I,O,\dots)
   &=&
   L_1 \cap I = \emptyset \land A(I,O\cup L_1,\dots)
\\ A(I,O,a,R,A,L') \seq A(I,O,a,R,A,L') &=& \false?
\\ A(I,O,a,I,O,O) \seq A(I,O,a,I,O,O) &=& \false
\end{eqnarray*}

We note the strongest inference we can make regarding $L'$
\begin{eqnarray*}
   A(I,O,a,R,A,L') &\implies& ls'(I\setminus R \cup A \cup L')
\end{eqnarray*}

Remembering:
\begin{eqnarray*}
  && A(I_1,O_1,as,R_1,A_1,L_1) \seq A(I_2,O_2,bs,R_2,A_2,L_2)
\EQ{Defn. of $A$, lots of steps\dots}
\\&& (L_1 \cup I_2)\setminus A_1 \cap R_1 = \emptyset
     \land O_2 \cap A_1 = \emptyset
\\&& {}\land A( I_1 \cup I_2\setminus A_1
              , O_1 \cup O_2\setminus R_1
              , (as\!\seq\! bs)
              , R_1 \cup R_2
              , A_1\setminus R_2 \cup A_2
              , L_2 )
\end{eqnarray*}


\newpage

\HDRb{Proofs}




\begin{eqnarray*}
  && A(I_1,O_1,as,R_1,A_1,L_1) \seq A(I_2,O_2,bs,R_2,A_2,L_2)
\EQ{Defn $A$, twice}
\\&& ls(I_1) \land ls(\B{O_1}) \land \ado{as}
     \land \lupd{R_1}{A_1} \land ls'(L_1)
\\&& {} \seq
     ls(I_2) \land ls(\B{O_2}) \land \ado{bs}
     \land \lupd{R_2}{A_2} \land ls'(L_2)
\EQ{Defn $\seq$.}
\\&& \exists s_m,ls_m \bullet
\\&& \qquad ls(I_1) \land ls(\B{O_1}) \land \ado{as}[s_m/s']
     \land ls_m = ls\ominus(R_1|A_1) \land ls_m(L_1)
\\&& \quad {} \land
     ls_m(I_2) \land ls_m(\B{O_2}) \land \ado{bs}[s_m/s]
     \land ls' = ls_m\ominus(R_2|A_2) \land ls'(L_2)
\EQ{$A \subseteq S \land B \subseteq S = (A \cup B) \subseteq S$, re-arrange}
\\&& \exists s_m,ls_m \bullet
\\&& \qquad ls(I_1) \land ls(\B{O_1}) \land ls_m = ls\ominus(R_1|A_1)
     \land ls_m(L_1 \cup I_2)
\\&& \quad {}\land ls_m(\B{O_2}) \land ls' = ls_m\ominus(R_2|A_2) \land ls'(L_2)
     \land \ado{as}[s_m/s'] \land \ado{bs}[s_m/s]
\EQ{One-point, $ls_m = ls\ominus(R_1|A_1)$}
\\&& \exists s_m \bullet ls(I_1) \land ls(\B{O_1})
     \land (ls\ominus(R_1|A_1))(L_1 \cup I_2)
\\&& \qquad {}\land (ls\ominus(R_1|A_1))(\B{O_2})
      \land ls' = (ls\ominus(R_1|A_1))\ominus(R_2|A_2) \land ls'(L_2)
\\&& \qquad {} \land \ado{as}[s_m/s'] \land \ado{bs}[s_m/s]
\EQ{Push quantifier in}
\\&& ls(I_1)  \land ls(\B{O_1})
     \land (ls\ominus(R_1|A_1))(L_1 \cup I_2)
\\&& {}\land (ls\ominus(R_1|A_1))(\B{O_2})
      \land ls' = (ls\ominus(R_1|A_1))\ominus(R_2|A_2) \land ls'(L_2)
\\&& {}\land \exists s_m \bullet \ado{as}[s_m/s'] \land \ado{bs}[s_m/s]
\EQ{Defn. of $\seq$ for atomic $as$,$bs$.}
\\&& ls(I_1)  \land ls(\B{O_1})
     \land (ls\ominus(R_1|A_1))(L_1 \cup I_2)
\\&& {}\land (ls\ominus(R_1|A_1))(\B{O_2})
      \land ls' = (ls\ominus(R_1|A_1))\ominus(R_2|A_2) \land ls'(L_2)
\\&& {}\land (\ado{as \seq bs})
\end{eqnarray*}
We now take stock, and seek to simplify some stuff.

\begin{eqnarray*}
  && (ls\ominus(R|A))(L)
\\&=& L \subseteq (ls \setminus R) \cup A
\\&=&  L \setminus ((ls \setminus R) \cup A) = \emptyset
\\&=&  L \setminus (A \cup (ls \setminus R)) = \emptyset
\\&=&  (L \setminus A) \setminus (ls \setminus R) = \emptyset
\EQ{$A\setminus(B\setminus C) = A\setminus B \cup A\cap C$}
\\&&  (L \setminus A) \setminus ls
      \cup
     (L \setminus A) \cap R = \emptyset
\\&=&  (L \setminus A) \setminus ls = \emptyset
      \land
     (L \setminus A) \cap R = \emptyset
\\&=&  (L \setminus A) \subseteq ls
      \land
     (L \setminus A) \cap R = \emptyset
\end{eqnarray*}

\begin{eqnarray*}
  && (ls\ominus(R_1|A_1))(\B{O_2})
\\&=& O_2 \cap ((ls \setminus R_1) \cup A_1) = \emptyset
\\&=& O_2 \cap (ls \setminus R_1)  = \emptyset
      \land
      O_2 \cap A_1 = \emptyset
\\&=& ls \cap (O_2 \setminus R_1)  = \emptyset
      \land
      O_2 \cap A_1 = \emptyset
\\&=& ls(\B{O_2 \setminus R_1})
      \land
      O_2 \cap A_1 = \emptyset
\end{eqnarray*}

\begin{eqnarray*}
  && (ls\ominus(R_1|A_1))\ominus(R_2|A_2)
\EQ{defn. $\ominus$, twice}
\\&& (((ls \setminus R_1) \cup A_1) \setminus R_2) \cup A_1
\EQ{$(A \cup B) \setminus C = (A\setminus C) \cup (B \setminus C)$}
\\&& (((ls \setminus R_1)\setminus R_2) \cup (A_1\setminus R_2) )\cup A_1
\EQ{$(A \setminus B) \setminus C = A \setminus (B \cup C)$}
\\&& (ls \setminus (R_1 \cup R_2)) \cup (A_1\setminus R_2) \cup A_1
\EQ{Defn $\ominus$, fold}
\\&& (ls \ominus  (R_1 \cup R_2|(A_1\setminus R_2) \cup A_1)
\end{eqnarray*}

Now, back into the fray\dots
\begin{eqnarray*}
  && ls(I_1)  \land ls(\B{O_1})
\\&& {}\land (ls\ominus(R_1|A_1))(L_1 \cup I_2)
\\&& {}\land (ls\ominus(R_1|A_1))(\B{O_2})
\\&& {}\land ls' = (ls\ominus(R_1|A_1))\ominus(R_2|A_2) \land ls'(L_2)
\\&& {}\land (\ado{as \seq bs})
\EQ{three calculations above}
\\&& ls(I_1)  \land ls(\B{O_1})
\\&& {}\land ls((L_1 \cup I_2)\setminus A_1)
       \land (L_1 \cup I_2)\setminus A_1 \cap R_1 = \emptyset
\\&& {}\land ls(\B{O_2\setminus R_1})
       \land O_2 \cap A_1 = \emptyset
\\&& {}\land ls' = ls\ominus(R_1 \cup R_2| A_1\setminus R_2 \cup A_2)
       \land ls'(L_2)
\\&& {}\land (\ado{as \seq bs})
\EQ{re-group}
\\&& (L_1 \cup I_2)\setminus A_1 \cap R_1 = \emptyset
     \land O_2 \cap A_1 = \emptyset
\\&& {}\land ls(I_1)
       \land ls((L_1 \cup I_2)\setminus A_1)
\\&& {}\land ls(\B{O_1})
       \land ls(\B{O_2\setminus R_1})
\\&& {}\land (\ado{as \seq bs})
\\&& {}\land ls' = ls\ominus(R_1 \cup R_2| A_1\setminus R_2 \cup A_2)
       \land ls'(L_2)
\EQ{merge  and simplify $ls$ assertions}
\\&& (L_1 \cup I_2)\setminus A_1 \cap R_1 = \emptyset
     \land O_2 \cap A_1 = \emptyset
\\&& {}\land ls(I_1 \cup I_2\setminus A_1)
\\&& {}\land ls(\B{O_1 \cup O_2\setminus R_1})
\\&& {}\land (\ado{as \seq bs})
\\&& {}\land ls' = ls\ominus(R_1 \cup R_2| A_1\setminus R_2 \cup A_2)
       \land ls'(L_2)
\EQ{Defn. of $A$, fold}
\\&& (L_1 \cup I_2)\setminus A_1 \cap R_1 = \emptyset
     \land O_2 \cap A_1 = \emptyset
\\&& {}\land A( I_1 \cup I_2\setminus A_1
              , O_1 \cup O_2\setminus R_1
              , (as\!\seq\! bs)
              , R_1 \cup R_2
              , A_1\setminus R_2 \cup A_2
              , L_2 )
\end{eqnarray*}

Hmmmm\dots
We may need to assume explicit false-avoiding and minimalist conditions,
e.g. for
\[
   A(I,O,as,R,A,L)
\]
the false avoiding conditions are
$I \cap O = \emptyset$
and $L \cap (R \setminus A) = \emptyset$,
while the minimalist condition is $R \cap A = \emptyset$.

The basic atomic action $a$ has semantics
\[
  D(out) \lor A(in,\emptyset,a,in,out,out)
\]
But since $in$ and $out$ are always local,
thanks to the way label generators are used,
we can assert the slightly stronger:
\[
  D(out) \lor A(in,out,a,in,out,out)
\]

\newpage
\HDRb{Results}

\HDRc{$a$}

\begin{eqnarray*}
  a
   & =  & D(out)
\\ &\lor& A(in,out,a,in,out,out)
\end{eqnarray*}

\HDRc{$a \cseq b$}

\begin{eqnarray*}
  a \cseq b
   & =  & D(out)
\\ &\lor& A(in,out,a,in,\ell_g,\setof{out,\ell_g})
\\ &\lor& A(\ell_g,out,b,\ell_g,out,out)
\\ &\lor& A(in,out,a;b,\setof{in,\ell_g},out,out)
\end{eqnarray*}

\HDRc{$a + b$}

\begin{eqnarray*}
  a + b
   & =  & D(out)
\\ &\lor& A(in,\setof{out,\ell_{g1},\ell_{g2}},ii,\setof{in,\ell_{g2}},\ell_{g1},\setof{out,\ell_{g1}})
\\ &\lor& A(in,\setof{out,\ell_{g1},\ell_{g2}},ii,\setof{in,\ell_{g1}},\ell_{g2},\setof{out,\ell_{g2}})
\\ &\lor& A(in,\setof{out,\ell_{g1},\ell_{g2}},ii ; a,\setof{in,\ell_{g1},\ell_{g2}},out,out)
\\ &\lor& A(in,\setof{out,\ell_{g1},\ell_{g2}},ii ; b,\setof{in,\ell_{g1},\ell_{g2}},out,out)
\\ &\lor& A(\ell_{g1},out,a,\ell_{g1},out,out)
\\ &\lor& A(\ell_{g2},out,b,\ell_{g2},out,out)
\end{eqnarray*}

\HDRb{Calculations with Views}

\HDRc{$Atm(a)$}

\RLEQNS{
   Atm(a) &=& D(out) \lor X(in|out|a|in|out)
}

\HDRc{$Atm(a) \cseq Atm(b)$}

\begin{eqnarray*}
   \lefteqn{Atm(a)[\g{:1},\ell_g/g,out] \lor Atm(b)[\g{:2},\ell_g/g,in]}
\\ &=& D(\ell_g)
       \lor X(in|\ell_g|a|in|\ell_g)
       \lor D(out)
       \lor X(\ell_g|out|b|\ell_g|out)
\end{eqnarray*}
