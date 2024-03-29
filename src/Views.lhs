\HDRa{Views}\label{ha:Views}
\begin{code}
module Views where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
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
-- import Debug.Trace
-- dbg str x = trace (str++show x) x
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
vGenDict :: Dict
vGenDict
 = makeDict
    [ (new1n,(ExprEntry subAny showGNew1 noDefn (justMakes gNew1) noEq))
    , (new2n,(ExprEntry subAny showGNew2 noDefn (justMakes gNew2) noEq))
    , (split1n,(ExprEntry subAny showGSplit1 noDefn (justMakes gSplit1) noEq))
    , (split2n,(ExprEntry subAny showGSplit2 noDefn (justMakes gSplit2) noEq))
    ]
\end{code}

\HDRc{The Expression Dictionary}\label{hc:WWW-expr-dict}

\begin{code}
dictVE :: Dict
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
   dictAtomic = mergeDicts 
                $ map snd [ pvarEntry "a" ss'
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
vXEntry :: (String, Entry)
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

vAEntry :: (String, Entry)
vAEntry
 = ( nA
   , PredEntry vStatic ppA vObs defnA simpA )
\end{code}

\HDRc{Wheels within Wheels}\label{hc:WwW}

We will remove the stuttering step from here,
because it looks like it only needs to be applied to atomic actions,
and it then propagates up.
\RLEQNS{
   \W(C) &\defs& \true * C
\\       &=& \bigvee_{i\in 0\dots} \Skip\seq D^i
     & \textbf{provided } C = \Skip \lor D \textbf{ for some } D
\\ ii &\defs& s'=s
}
We hypothesis that $\W(C) = \W(\Skip \lor C)$
for all our command constructs.
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

vWEntry :: (String, Entry)
vWEntry
 = ( nW
   , PredEntry [] ppW vObs defnW simpW )
\end{code}

\NOTE{
Redo this to handle $\W(P) = \true * (\Skip \lor P)$
}
\begin{code}
wUnroll :: String -> RWFun
wUnroll arg d _ wpr@(Comp nw [pr])
 | nw == nW
   = case numfrom arg of
      0 -> Just ( "W-unroll"
                , mkSeq (mkOr [mkSkip, pr]) wpr , True )
      n -> Just ( "W-unroll."++arg
                ,  wunroll n
                , True )

 where
   numfrom "" = 0
   numfrom (c:_) | isDigit c = digitToInt c
                 | otherwise = 42

   wunroll n = mkOr (mkSkip : dupPr pr n)
   dupPr dups 0 = []
   dupPr dups n = dups : dupPr (mkSeq dups pr) (n-1)

wUnroll _ _ _ _ = Nothing
\end{code}

\newpage
\HDRb{WwW Semantic Definitions}

The definitions, using the new shorthands:
\RLEQNS{
   \W(C) &\defs& \true * C
\\       &=& \bigvee_{i\in 0\dots} \Skip\seq D^i
\\       & & \textbf{provided } C = \Skip \lor D \textbf{ for some } D
\\ ii &\defs& s'=s
\\
\\ \miracle &\defs&  \W(\false)
\\
\\ \Atm a &\defs&\W(\Skip \lor A(in|a|out)) \land [in|out]
\\ \cskip
   &\defs&
   \W(\Skip \lor A(in|ii|out)) \land [in|out]
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
\\ && \qquad {}\lor A(in|ii|\ell_g)
\\ && \qquad {}\lor C[g_{:},\ell_g,in/g,in,out]~)
\\&& {} \land [in|\ell_g|out]
}

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

vIElemEntry :: (String, Entry)
vIElemEntry
 = ( nIElem
   , PredEntry anyVars ppIElem vStatic (pNoChg nIElem) (pNoChg nIElem) )

vIDisjEntry :: (String, Entry)
vIDisjEntry
 = ( nIDisj
   , PredEntry anyVars ppIDisj vStatic (pNoChg nIDisj) (pNoChg nIDisj) )

vIJoinEntry :: (String, Entry)
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

Now we have to code up \textbf{lsat}:
\RLEQNS{
}
\begin{code}
lsat :: Dict -> Expr -> Pred -> Bool
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
locc :: Dict -> Expr -> Pred -> I Bool

-- occ ls (I ell) = I (ell `elem` ls)
locc d lset (Comp nm [Atm ell])
 | nm == nIElem
   = case esimp d $ subset ell lset of
      (_,B b)  ->  I b
      _        ->  I False -- no occupancy!

-- occ ls (U invs) = U $ map (occ ls) invs
locc d lset (Comp nm prs)
 | nm == nIJoin  =  U $ map (locc d lset) prs

-- occ ls (X invs) = X $ map (occ ls) invs
 | nm == nIDisj  =  X $ map (locc d lset) prs

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
\\ occChk(b) &\defs& (ok,b)
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
\HDRc{Invariant Trimming}

We can use the invariant to trim removal sets,
given an enabling label or label-set.
\RLEQNS{
   I \textbf{ invTrims } X(E|a|E,L|A)
   &\defs&
   \lnot(\setof{E,L} \textbf{ lsat } I)
}
We need a function that establishes when the invariant is not satisfied
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


\HDRc{Coding Miracle}

\RLEQNS{
\miracle &\defs&  \W(\false)
}

\begin{code}
nMiracle = "miracle" -- internal abstract name
isMiracle (Comp n [_]) | n==nMiracle = True; isMiracle _ = False

mkMiracle = Comp nMiracle []

ppMiracle d ms p [] = ppa "<miracle>"
ppMiracle d ms p mprs = pps styleRed $ ppa ("invalid-"++nMiracle)


defnMiracle d []
 = ldefn nMiracle $ mkW F

invMiracle = idisj [ielem inp, ielem out]

vMiracleEntry :: (String, Entry)
vMiracleEntry
 = ( nMiracle
   , PredEntry ["s","s'"] ppMiracle [] defnMiracle (pNoChg nMiracle) )

\end{code}

\newpage
\HDRc{Coding Atomic Semantics}

\RLEQNS{
 \Atm a &\defs&\W(\Skip \lor A(in|a|out)) \land [in|out]
}

\begin{code}
nAtom = "Atom" -- internal abstract name
isAtom (Comp n [_]) | n==nAtom = True; isAtom _ = False

atom pr = Comp nAtom [pr]

ppAtom sCP d p [pr] = ppbracket "<" (sCP 0 1 pr) ">"
ppAtom _ _ _ _ = pps styleRed $ ppa ("invalid-"++nAtom)

defnAtom d [a]
 = ldefn nAtom $ mkW $ mkOr $ [mkSkip, mkA inp a out]

invAtom = idisj [ielem inp, ielem out]

sinp = sngl inp
sout = sngl out

vAtmEntry :: (String, Entry)
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

vAtmCalcEntry :: (String, Entry)
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
\begin{code}
nVSkip = "VSkip" -- internal abstract name
isVSkip (_,Comp n []) | n==nVSkip = True; isVSkip _ = False

vskip  = Comp nVSkip []

ppVSkip d ms p [] = ppa "<skip>"
ppVSkip d ms p mprs = pps styleRed $ ppa ("invalid-"++nVSkip)

defnVSkip d []
 = ldefn nVSkip $ mkW $ mkOr $ [mkSkip, mkA inp ii out]

invVSkip = idisj [ielem inp, ielem out]

vSkipEntry :: (String, Entry)
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

vSkipCalcEntry :: (String, Entry)
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
 = ldefn shVSeq $ mkW $ mkOr [PSub p sub1, PSub q sub2]
 where
   sub1 = [("g",g'1),("out",lg)]
   sub2 = [("g",g'2),("in",lg)]

lg = new1 g
g' = new2 g
g'1 = split1 g'
g'2 = split2 g'

invVSeq = idisj[ielem inp, ielem lg, ielem out]

vSeqEntry :: (String, Entry)
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
 = ldefn shVChc $ mkW
    $ mkOr [ mkA inp ii lg1
           , mkA inp ii lg2
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

vChcEntry :: (String, Entry)
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
 = ldefn shVPar $ mkW
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

invVPar = idisj [ ielem inp
                , ijoin [ idisj [ ielem lg1, ielem lg1' ]
                        , idisj [ ielem lg2, ielem lg2' ]
                        ]
                , ielem out
                ]

vParEntry :: (String, Entry)
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
 = ldefn shVIter $ mkW
    $ mkOr [ mkA inp ii out
           , mkA inp ii lg
           , PSub p sub
           ]
 where
   sub = [("g",g'),("in",lg),("out",inp)]

invVIter = idisj [ ielem inp
                 , ielem lg
                 , ielem out
                 ]

vIterEntry :: (String, Entry)
vIterEntry
 = ( nVIter
   , PredEntry [] ppVIter [] defnVIter (pNoChg nVIter) )
\end{code}



\newpage
\HDRc{The Predicate Dictionary}\label{hc:WWW-pred-dict}

\begin{code}
dictVP, dictVPCalc :: Dict
dictVP = makeDict [ vXEntry
                  , vAEntry
                  , vWEntry
                  , vIElemEntry
                  , vIDisjEntry
                  , vIJoinEntry
                  , vMiracleEntry
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
        -- -> Pred    -- Invariant
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

\false\ is a zero for sequential composition
\begin{eqnarray*}
   \false \seq B &=~\false~=& A \seq \false
\end{eqnarray*}
\begin{code}
vReduce d _ (Comp ns1 [ prA, prB ])
 | ns1 == nSeq && ( prA == F || prB == F)
     =  lred  ";-zero" $ F
\end{code}

\false\ is a unit for logical-or composition
\begin{eqnarray*}
   \false \lor A &=~A~=& A \lor \false
\end{eqnarray*}
\begin{code}
vReduce d _ (Comp ns1 [ prA, prB ])
 | ns1 == nOr && prA == F  =  lred  "or-l-unit" $ prB
 | ns1 == nOr && prB == F  =  lred  "or-r-unit" $ prA
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
vRedEntry :: Dict
vRedEntry = entry laws $ LawEntry [vReduce] [] []
\end{code}


\HDRb{Conditional Reductions for WWW}\label{hb:WWW-creduce}

\begin{code}
vCReduce :: CRWFun
\end{code}

Default case: no change.
\begin{code}
vCReduce _ mpr = Nothing
\end{code}

\HDRc{The Conditional Reduction Entry}\label{hc:WWW-reduce-ent}

\begin{code}
vCRedEntry :: Dict
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

\HDRc{The Unroll Entry}\label{hc:WWW-reduce-ent}

\begin{code}
vLoopEntry :: Dict
vLoopEntry = entry laws $ LawEntry [] [] [wUnroll,vUnroll]
\end{code}


\HDRb{Dictionary for Views}\label{hb:View-Dict}

\begin{code}
vDict :: Dict
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
vshow :: Pred -> String
vshow = pmdshow 80 vDict noStyles . buildMarks

vput :: Pred -> IO ()
vput = putStrLn . vshow

vcalc pr = calcREPL vDict [noInvariant] pr

ivcalc inv pr
 = calcREPL vDict [(labelSetInv, inv)] pr

vputcalc :: Pred -> IO ()
vputcalc pr = printREPL vDict [noInvariant]  pr

ivputc inv pr
 = printREPL vDict [(labelSetInv, inv)]  pr

vsavecalc fp pr
 = do calc <- vcalc pr
      saveCalc fp calc

vsimp :: Pred -> (String, Pred)
vsimp pr
  = case simplify vDict 42 $ buildMarks pr of
     Nothing               ->  ("", pr)
     Just (_,what,(pr',_)) ->  (what,pr')
vsimp2 :: (String, Pred) -> (String, Pred)
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

subII :: Pred
subII = PSub mkSkip [("g",g'1),("out",lg)]

-- an invariant that always fails
noGood _ _ _ = Just False

xcalc :: Pred -> IO ()
xcalc = printREPL vDict [(noGood, F)]
\end{code}

\begin{code}
--defvseq :: [Pred] -> Pred
defvseq = defnVSeq vDict
--athenbBody :: Pred
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

test :: Maybe BeforeAfter
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
 = idisj [ ielem inp
         , ielem lg
         , ielem lg'
         , ielem out ]
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


\newpage
\HDRc{Miracle as unit for nDC}

We have laws regarding $A;A$, $A;X$, etc.
I think we need laws also relating $A(\dots)$ and $X(\dots)$ to $C$
and $C[\dots/\dots]$.
 
\begin{verbatim}
invVChc = [in|lg1|lg2|out]
\end{verbatim}
\begin{code}
mkC = PVar "C"
corm = mkC `vchc` mkMiracle
cSub = PSub mkC [("g",g1'),("in",lg1)]
\end{code}
\begin{verbatim}
Q(corm) =    A(in|ii|lg1) \/ C[g1:,lg1/g,in] 
          \/ A(in|ii|lg2) \/ F[g2:,lg2/g,in]
\end{verbatim}
\begin{verbatim}
q_corm
 =    A(in|ii|lg1) 
   \/ C[g1:,lg1/g,in] 
   \/ A(in|ii|lg2)
\end{verbatim}
\begin{code}
q_corm  = mkOr [ mkA inp ii lg1, cSub, mkA inp ii lg2 ]
\end{code}

\begin{verbatim}
q_corm^2
 =   (C[g1:,lg1/g,in] ; A(in|ii|lg1))
   \/ (A(in|ii|lg1) ; C[g1:,lg1/g,in])
   \/ (C[g1:,lg1/g,in] ; C[g1:,lg1/g,in])
   \/ (A(in|ii|lg2) ; C[g1:,lg1/g,in])
   \/ (C[g1:,lg1/g,in] ; A(in|ii|lg2))
\end{verbatim}