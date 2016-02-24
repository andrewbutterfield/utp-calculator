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

%\begin{code}
%import Debug.Trace
%vdbg str x = trace (str++show x) x
%\end{code}

We do a quick run-down of the Commands\cite{conf/popl/Dinsdale-YoungBGPY13}.

\HDRb{Syntax}

\def\atm#1{atm(#1)}

\begin{eqnarray*}
   a &\in& \Atom
\\ C &::=&
 \atm a \mid \cskip \mid C \cseq C \mid C+C \mid C \parallel C \mid C^*
\\ g &:& Gen
\\ \ell &:& Lbl
\\ G &::=&  g \mid G_{:} \mid G_1 \mid G_2
\\ L &::=& \ell_G
\end{eqnarray*}

We assign the following precedences to Views syntactical constructs,
interleaving them among the standard predicates.
\begin{code}
precVCond = 5 + precSpacer  1
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

emp = set []

mkSet :: Ord s => [Expr s] -> Expr s
mkSet = set . sort . nub

showSet d elms = "{" ++ dlshow d "," elms ++ "}"

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
    [ (setn,(ExprEntry ["*"] showSet evalSet eqSet))
    , (unionn,(ExprEntry ["*"] ppUnion evalUnion noEq))
    , (intn,(ExprEntry ["*"] ppIntsct evalIntsct noEq))
    , (sdiffn,(ExprEntry ["*"] ppSDiff evalSDiff noEq))
    , (subsetn,(ExprEntry ["*"] showSubSet evalSubset noEq))
    , (sswapn, (ExprEntry ["*"] showSSwap evalSSwap noEq))
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
    [ (new1n,(ExprEntry ["*"] showGNew1 (justMakes gNew1) noEq))
    , (new2n,(ExprEntry ["*"] showGNew2 (justMakes gNew2) noEq))
    , (split1n,(ExprEntry ["*"] showGSplit1 (justMakes gSplit1) noEq))
    , (split2n,(ExprEntry ["*"] showGSplit2 (justMakes gSplit2) noEq))
    ]
\end{code}

\HDRc{The Expression Dictionary}\label{hc:WWW-expr-dict}

\begin{code}
dictVE :: (Ord s, Show s) => Dict s
dictVE = vSetDict `dictMrg` vGenDict
\end{code}



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
   dictAlpha = stdAlfDictGen ["s"] ["ls"] ["g","in","out"]
   dictAtomic = makeDict [ pvarEntry "a" ss'
                         , pvarEntry "b" ss'
                         , pvarEntry "c" ss' ]
   ss' = ["s", "s'"]
\end{code}

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
defnSkip d _ = ldefn shSkip $ mkAnd [equal ls' ls, equal s' s]

vSkipEntry -- in stdUTPDict
  = ( nSkip
     , (snd skipEntry){ alfa = ["ls","ls'","s","s'"]
                      , pdefn = defnSkip } )
\end{code}

\HDRd{Updating the Standard UTP Dictionary}~

\begin{code}
vStdUTPDict :: (Show s, Ord s) => Dict s
vStdUTPDict
  = makeDict [ vSkipEntry
             ] `dictMrg` stdUTPDict
\end{code}



\HDRc{WwW Calculations/Results}

We will start by explaining a calculation method
that should help structure our reasoning about loops.
We consider a generic iteration $c*P$,
and note the following identity,
obtained by repeated application of the loop unrolling law
coupled with expansion of the definition of conditionals:
\begin{equation}\label{eqn:unroll-n-times}
   c * P
   \quad=\quad
   \bigvee_{i=0}^{n-1} ( (c \land P)^i ; \lnot c \land \Skip)
   \;\lor\;
   (c \land P)^n ; c * P
\end{equation}
From this we define the following shorthands,
and suggest two important calculations:
\begin{eqnarray*}
   W &\defs& c * P
\\ D &\defs& \lnot c \land \Skip \EOLC{Done}
\\ S &\defs& c \land P \EOLC{Step}
\\ L &\defs& S ; D \EOLC{Last}
\\ T &\defs& D ; D \EOLC{Two-Step}
\end{eqnarray*}


\HDRb{Atomic Shorthands}

We find essentially just two idioms here,
\[
  D(L) \qquad A(I,O,a,R,A,L)
\]
where $L$, $I$, $O$, $R$ and $A$ are lists of labels:
\begin{eqnarray*}
   D(L) &\defs&  ls(L) \land s'=s \land ls'=ls
\\ &=& ls(L) \land s'=s \land ls'=ls \land ls'(L)
\end{eqnarray*}
\begin{code}
nD = "D"
isD (_,Comp n [_]) | n==nD = True; isD _ = False

bD ell = comp nD [atm ell]

shD = "D"
ppD d ms p mprs@[(_,Atm _)] = stdCshow d ms shD mprs
ppD d ms p mprs = pps styleRed $ ppa ("invalid-"++shD)

-- we don't want to expand the definition of this
defnD = pNoChg nD

staticOnly = ["g","in","out"]

vDEntry :: (Show s, Ord s) => (String, Entry s)
vDEntry
 = ( nD
   , PredEntry staticOnly ppD [] defnD (pNoChg nD) )
\end{code}

\newpage
\begin{eqnarray*}
   A(I,O,as,R,A,L)
   &\defs& ls(I) \land ls(\B O) \land \ado{as}
       \land ls'=ls\ominus(R|A) \land ls'(L)
\\ &=& I \cap O = \emptyset \land ls(I) \land ls(\B O)
\\ && {} \land \ado{as}
\\ && {} \land ls'=ls\ominus(R|A) \land ls'(A \cup L)
         \land (R\setminus A) \cap L = \emptyset
\\ &=& A(I,O,as,R,A,A\cup L)
\\ A(I,O,as,R,A,L')
   &=&
   A(I,O,as,R\setminus A,A,(I\setminus R) \cup A \cup L')
\end{eqnarray*}

\begin{code}
nA = "A"
isA (_,Comp n [_]) | n==nA = True; isA _ = False

bA lI lO as lR lA lL
 = comp nA [ atm lI, atm lO, as
           , atm (lR `sdiff` lA)
           , atm lA,atm ((lI `sdiff` lR) `u` lA `u` lL) ]

shA = "A"
ppA d ms p mprs@[(_,Atm _),(_,Atm _),_,(_,Atm _),(_,Atm _),(_,Atm _)]
 = stdCshow d ms shA mprs
ppA d ms p mprs = pps styleRed $ ppa ("invalid-"++shA)

-- we don't want to expand the definition of this
defnA = pNoChg nA
\end{code}
\begin{eqnarray*}
   A(I,O,as,R,A,L) &=&  A(I,O,as,R,A,A\cup L)
\\ &\land& I \cap O = \emptyset
\\ &\land& (R\setminus A) \cap L = \emptyset
\end{eqnarray*}
\begin{code}
simpA :: (Ord s, Show s) => Rewrite s
simpA d mprs@[ (_,Atm lI)  -- I
             , (_,Atm lO)  --  O
             , as          --  as
             , (_,Atm lR)  --  R
             , (_,Atm lA)  --  A
             , (_,Atm lL)  --  L
             ]
 | preFalse || postFalse  =  ( "A-disabled",  F )
 | otherwise              =  ( "", Comp nA mprs )
 where
  iIO = snd $ esimp d (lI `i` lO)
  preFalse = (sEqual d iIO emp) == (True,F)
  dRAiL = snd $ esimp d ((lR `sdiff` lA) `i` lL)
  postFalse = (sEqual d dRAiL emp) == (True,F)

simpA d mprs = ( "", Comp nA mprs )

vAEntry :: (Show s, Ord s) => (String, Entry s)
vAEntry
 = ( nA
   , PredEntry staticOnly ppA [] defnA simpA )
\end{code}
We have both an `implicit' form which is a minimalist
definition of behaviour, along with an `explicit' form
that expresses all the logical consequences.


We get the following laws (implicit form):
\begin{eqnarray*}
   D(L_1) ; D(L_2) &=& D(L_1 \cup L_2)
%
\\ D(L_1) ;  A(I,O,as,R,A,L_2)
   &=&
   A(L_1\cup I,O,as,R,A,L_2)
%
\\  A(I,O,as,R,A,L_1) ; D(L_2)
   &=&
   A(I,O,as,R,A,L_1\cup L_2)
%
\\ A(I_1,O_1,as,R_1,A_1,L_1) ; {}
\\ A(I_2,O_2,bs,R_2,A_2,L_2)
   &=&  (L_1 \cup I_2)\setminus A_1 \cap R_1 = \emptyset
        \land O_2 \cap A_1 = \emptyset \land {}
\\&& A(~   I_1 \cup I_2\setminus A_1
      ,~   O_1 \cup O_2\setminus R_1
\\&& ~~~,~ (as\!\seq\! bs)
\\&& ~~~,~ R_1 \cup R_2
      ,~   A_1\setminus R_2 \cup A_2
      ,~   L_2 ~)
\end{eqnarray*}

Full forms
\begin{eqnarray*}
   D(L)
   &\defs& ls(L) \land s'=s \land ls'=ls
\\
\\ A(I,O,as,R,A,L)
   &\defs&
   ls(I) \land ls(\B O) \land \ado{as} \land \lupd R A \land ls'(L)
\end{eqnarray*}



\HDRc{Healthiness Predicates}

We define our main healthiness condition:
\RLEQNS{
\W(P) &\defs& \lnot ls(out) * P
}
\begin{code}
nW = "W" -- internal abstract name
isW (_,Comp n [_]) | n==nW = True; isW _ = False

w atom = comp nW [atom]
wp atom = Comp nW [atom]

shW = "W" -- show name
ppW d ms p [mpr]
 = pplist [ ppa shW
          , ppbracket "(" (mshowp d ms 0 mpr) ")"]
ppW d ms p mprs = pps styleRed $ ppa ("invalid-"++shW)

defnW d [mpr] = ldefn shW $ mkIter notlsout mpr

lsout = atm $ App subsetn [out,ls]
notlsout = bNot lsout

vWEntry :: (Show s, Ord s) => (String, Entry s)
vWEntry
 = ( nW
   , PredEntry [] ppW [] defnW (pNoChg nW) )
\end{code}
We need to show it is idempotent (monotonicity is immediate):
\RLEQNS{
   \W(\W(P)) &=& \W(P)
}
We assume the following laws of iteration:
\RLEQNS{
   c*P &=& P \seq c*P  \cond c \Skip
\\ &=& c \land P \seq c*P \lor \lnot c \land \Skip
\\ c \land c * P &=& c \land P \seq c * P
\\ \lnot c \land c * P &=& \lnot c \land \Skip
\\ && \lnot c \land \Skip \land \lnot c'
\\ \multicolumn{4}{l}{\mbox{below we assume }c \neq \true}
\\ c * P &=& c * P \land \lnot c'
\\ &=& (c * P) \seq \lnot c
\\ &=& (c * P) \seq \lnot c \land \Skip
\\ c * P \seq c * Q &=& c * P
\\ c * ( c * P ) &=& c * P
\\ c * (\bigvee_i P_i) &=& (\bigvee_i c \land P_i) \lor \lnot c \land \Skip
}
We can now defined expansions of $\W(P)$,
using loop-unrolling,
as:
\RLEQNS{
   \W(P) &\defs& \lnot ls(out) * P
\\ &=& P ; \W(P) \cond{\lnot ls(out)} \Skip
\\ &=& ls(out) \land Skip \lor \lnot ls(out) \land P ; \W(P)
\\ &=& D(out)
       \lor \lnot ls(out) \land P ; \W(P)
\\ &=& D(out)
\\ && {} \lor \lnot ls(out) \land P ; D(out)
\\ && {} \lor \lnot ls(out) \land P ; \lnot ls(out) \land P ; \W(P)
}
We do this as a loop-unroll with iteration parameter:
\begin{code}
wUnroll :: Ord s => String -> DictRWFun s
wUnroll ns d mw@(_,Comp nm [mpr])
 | nm == nW = ( "W-unroll" ++ ntag ns, wunroll n )
 where

   ntag "" = ""
   ntag ns = '.':ns

   n | null ns = 0
     | isDigit $ head ns = digitToInt $ head ns
     | otherwise = 0

   wunroll 0  =  bCond (bSeq mpr mw) (bNot lsout) bSkip
   wunroll 1  =  bOr [ loopdone
                     , bSeq (loopstep 1) mw]
   wunroll 2  =  bOr [ loopdone
                     , bSeq (loopstep 1) loopdone
                     , bSeq (loopstep 2) mw]
   wunroll 3  =  bOr [ loopdone
                     , bSeq (loopstep 1) loopdone
                     , bSeq (loopstep 2) loopdone
                     , bSeq (loopstep 3) mw]
   wunroll _  =  bCond (bSeq mpr mw) (bNot lsout) bSkip

   loopdone = bD out
   loopstep 1 = bAnd [bNot lsout, mpr]
   loopstep n = bSeq (loopstep (n-1)) (loopstep 1)

wUnroll _ _ mpr = ( "", mpr )
\end{code}

\HDRb{WwW Semantic Definitions}

The definitions, using the new shorthand:
\begin{eqnarray*}
   \W(C) &\defs& ls(\B{out}) * C)
\\ ii &\defs& s'=s
\\
\\ \atm a &\defs&\W(A(in,\emptyset,a,in,out,out))
\\ \cskip
   &\defs&
   \W(A(in,\emptyset,ii,in,out,out))
\\
\\ C \cseq D
   &\defs&
   \W(C[g_{:1},\ell_g/g,out] \lor D[g_{:2},\ell_g/g,in])
\\
\\ C + D
   &\defs&
   \W(\quad {}\phlor A(in,\emptyset,ii,\setof{in,\ell_{g2}},\ell_{g1},\ell_{g1})
\\ && \qquad {} \lor
   A(in,\emptyset,ii,\setof{in,\ell_{g1}},\ell_{g2},\ell_{g2})
\\ && \qquad {} \lor
   C[g_{1:},\ell_{g1}/g,in] \lor D[g_{2:},\ell_{g2}/g,in]~)
\\
\\ C \parallel D
   &\defs&
   \W(\quad\phlor A(in,\emptyset,ii,in,\setof{\ell_{g1},\ell_{g2}},\setof{\ell_{g1},\ell_{g2}})
\\ && \qquad {}\lor
   C[g_{1::},\ell_{g1},\ell_{g1:}/g,in,out]
   \lor D[g_{2::},\ell_{g2},\ell_{g2:}/g,in,out]
\\ && \qquad {}\lor
   A(\setof{\ell_{g1:},\ell_{g2:}},\emptyset
      ,ii
      ,\setof{\ell_{g1:},\ell_{g2:}},out,out)~)
\\
\\ C^*
   &\defs&
   \W(\quad\phlor A(in,\emptyset,ii,\setof{in,\ell_g},out,out)
\\ && \qquad {}\lor A(in,\emptyset,ii,\setof{in,out},\ell_g,\ell_g)
\\ && \qquad {}\lor C[g_{:},\ell_g,in/g,in,out]~)
\end{eqnarray*}






\HDRc{Coding Atomic Semantics}

Formally, using our shorthand notations, we can define atomic behaviour as:
\RLEQNS{
   \A(A)
    &\defs&
   \W(ls(in) \land A \land ls'=ls\ominus(in,out))
\\ &=& \lnot(ls(out))*(ls(in) \land A \land ls'=ls\ominus(in,out))
\\ &=& ls(out) \land \Skip
\\ &\lor& \lnot(ls(out)
     \land ( ls(in) \land A \land ls'=ls\ominus(in,out)
             \seq \W(\ldots) )
\\ &=& ls(out) \land \Skip
\\ &\lor& \lnot(ls(out)
     \land ( ls(in) \land A \land ls'=ls\ominus(in,out)
\\ && \qquad \seq ls(out)\land \lnot(ls(out)*(\ldots)))
\\ &=& ls(out) \land \Skip
\\ &\lor& \lnot(ls(out)
     \land ls(in) \land A \land ls'=ls\ominus(in,out)
\\ &=& \Skip
       \cond{ls(out)}
       ls(in) \land A \land ls'=ls\ominus(in,out)
                                           & \elabel{Atomic-Def}
}
\begin{code}
nPAtm = "PAtm" -- internal abstract name
isPAtm (_,Comp n [_]) | n==nPAtm = True; isPAtm _ = False

patm atom = comp nPAtm [atom]

shPAtm = "A" -- show name
ppPAtm d ms p [mpr]
 = pplist [ ppa shPAtm
          , ppbracket "(" (mshowp d ms 0 mpr) ")"]
ppPAtm d ms p mprs = pps styleRed $ ppa ("invalid-"++shPAtm)

defnAtomic d [a]
 = ldefn (shPAtm++".5")
    $ mkCond bSkip lsout $ bAnd [lsin,a,ls'eqlsinout]


lsin = atm $ App subsetn [inp,ls]
lsinout = App sswapn [ls,inp,out]
ls'eqlsinout = equal ls' lsinout

patmEntry :: (Show s, Ord s) => (String, Entry s)
patmEntry
 = ( nPAtm
   , PredEntry [] ppPAtm [] defnAtomic (pNoChg nPAtm) )
\end{code}


\HDRc{Coding Sequential Composition}

\RLEQNS{
   P \lseq Q
   &\defs&
   \W( P[\g{:1},\ell_g/g,out]
       \lor
       Q[\g{:2},\ell_g/g,in])
}
\begin{code}
nVSeq = "VSeq"
isVSeq (_,Comp n [_,_]) | n==nVSeq = True; isVSeq _ = False

vseq p q = comp nVSeq [p,q]

shVSeq = ";;"
ppVSeq d ms p [mpr1,mpr2]
 = paren p precVSeq
     $ ppopen  (pad shVSeq) [ mshowp d ms precVSeq mpr1
                            , mshowp d ms precVSeq mpr2 ]
ppVSeq d ms p mprs = pps styleRed $ ppa ("invalid-"++shVSeq)

defnVSeq d [p,q]
 = ldefn shVSeq $ wp $ bOr [psub p sub1, psub q sub2]
 where
   sub1 = [("g",g'1),("out",lg)]
   sub2 = [("g",g'2),("in",lg)]

lg = new1 g
g' = new2 g
g'1 = split1 g'
g'2 = split2 g'

vSeqEntry :: (Show s, Ord s) => (String, Entry s)
vSeqEntry
 = ( nVSeq
   , PredEntry [] ppVSeq [] defnVSeq (pNoChg nVSeq) )
\end{code}


\HDRc{The Predicate Dictionary}\label{hc:WWW-pred-dict}

\begin{code}
dictVP :: (Ord s, Show s) => Dict s
dictVP = makeDict [vDEntry,vAEntry,vWEntry,patmEntry,vSeqEntry]
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
mtchLabelSetSSwap (_,Equal v' (App nm [v, s1, s2]))
 | v == ls && v' == ls'  =  matchBind [atm s1, atm s2]
mtchLabelSetSSwap _      =  noMatch
\end{code}

\HDRc{\texttt{vReduce}}\label{hc:vReduce}

\begin{code}
vReduce :: (Ord s, Show s) => DictRWFun s
         -- Dict s -> MPred s -> (String, MPred s)
\end{code}
We start with laws concerning $D$, $A$ and $\seq$.

\newpage
\HDRd{Reduce $D(L_1)\seq D(L_2)$}

\begin{eqnarray*}
  && D(L_1) \seq D(L_2)
\EQ{Defn. $D$}
\\&& ls(L_1) \land s'=s \land ls'=ls \seq ls(L_2) \land s'=s \land ls'=ls
\EQ{Defn. $\seq$}
\\&& \exists s_m,ls_m \bullet
    ls(L_1) \land s_m=s \land ls_m=ls
    \land ls_m(L_2) \land s'=s_m \land ls'=ls_m
\EQ{One-point, $s_m,ls_m = s,ls$}
\\&& ls(L_1) \land ls(L_2) \land s'=s \land ls'=ls
\EQ{$A \subseteq S \land B \subseteq S = (A \cup B) \subseteq S$}
\\&& ls(L_1 \cup L_2) \land s'=s \land ls'=ls
\EQ{Defn. $D$, fold}
\\&& D(L_1 \cup L_2)
\end{eqnarray*}
\begin{code}
vReduce d (_,Comp ns [ (_,Comp nd1 [(_,Atm ell1)])    -- D(L1) ;
                     , (_,Comp nd2 [(_,Atm ell2)]) ]) -- D(L2)
 | ns == nSeq && nd1 == nD && nd2 == nD
   =  ( "D;D", bD $ snd $ esimp d (ell1 `u` ell2) )
\end{code}

\newpage
\HDRd{Reduce $D(L_1) ;  A(I,O,as,R,A,L_2)$}

\begin{eqnarray*}
  && D(L_1) \seq A(I,O,as,R,A,L_2)
\EQ{Defn. of $D$ and $A$.}
\\&& ls(L_1) \land s'=s \land ls'=ls
     \seq
     ls(I) \land ls(\B O) \land \ado{as} \land \lupd R A \land ls'(L_2)
\EQ{Defn. of $\seq$.}
\\&& \exists s_m,ls_m \bullet ls(L_1) \land s_m=s \land ls_m=ls
\\&& \qquad {} \land
     ls_m(I) \land ls_m(\B O) \land \ado{as}[s_m/s]
     \land ls'=ls_m \ominus (R|A) \land ls'(L_2)
\EQ{One-point, $s_m,ls_m = s,ls$}
\\&& ls(L_1) \land
     ls(I) \land ls(\B O) \land \ado{as}
     \land ls'=ls \ominus (R|A) \land ls'(L_2)
\EQ{$A \subseteq S \land B \subseteq S = (A \cup B) \subseteq S$}
\\&& ls(L_1 \cup I) \land ls(\B O) \land \ado{as}
     \land ls'=ls \ominus (R|A) \land ls'(L_2)
\EQ{add explicit condition}
\\&& (L_1 \cup I) \cap O = \emptyset \land
     ls(L_1 \cup I) \land ls(\B O) \land \ado{as}
     \land ls'=ls \ominus (R|A) \land ls'(L_2)
\EQ{Defn. $A$, fold}
\\&& (L_1 \cup I) \cap O = \emptyset \land A(L_1 \cup I,O,as,R,A,L_2)
\end{eqnarray*}
\begin{code}
vReduce d (_,Comp ns [ (_,Comp nd [(_,Atm ell1)]) -- D(L1) ;
                     , (_,Comp na [ (_,Atm lI)    -- A(I
                                  , (_,Atm lO)    --  ,O
                                  , as            --  ,as
                                  , (_,Atm lR)    --  ,R
                                  , (_,Atm lA)    --  ,A
                                  , (_,Atm lL2)   --  ,L2)
                                  ])
                     ])
 | ns == nSeq && nd == nD && na == nA
   =  ( "D;A", bAnd [ equal (ell `i` lO) emp
                    , bA ell lO as lR lA lL2 ])
 where ell = snd $ esimp d (ell1 `u` lI)
\end{code}

\newpage
\HDRd{Reduce $A(I,O,as,R,A,L_1) \seq D(L_2)$}

\begin{eqnarray*}
  && A(I,O,as,R,A,L_1) \seq D(L_2)
\EQ{Defn. of $A$ and $D$.}
\\&& ls(I) \land ls(\B O) \land \ado{as} \land \lupd R A \land ls'(L_1)
     \seq
     ls(L_2) \land s'=s \land ls'=ls
\EQ{Defn. $\seq$}
\\&& \exists s_m,ls_m \bullet
\\&& \quad
     ls(I) \land ls(\B O) \land \ado{as}[s_m/s']
     \land ls_m=ls \ominus (R|A) \land ls_m(L_1)
\\&& {} \land
     ls_m(L_2) \land s'=s_m \land ls'=ls_m
\EQ{One-point, $s_m,ls_m = s',ls'$}
\\&& ls(I) \land ls(\B O) \land \ado{as}
\land ls'=ls \ominus (R|A) \land ls'(L_1)
     \land ls'(L_2)
\EQ{$A \subseteq S \land B \subseteq S = (A \cup B) \subseteq S$}
\\&& ls(I) \land ls(\B O) \land \ado{as} \land ls'=ls \ominus (R|A)
     \land ls'(L_1 \cup L_2)
\EQ{add explicit conditions}
\\&& ls(I) \land ls(\B O) \land \ado{as} \land ls'=ls \ominus (R|A)
     \land ls'(L_1 \cup L_2)
     \land (R \setminus A) \cap (L_1 \cup L_2) = \emptyset
\EQ{Defn. $A$, fold}
\\&& A(I,O,as,R,A,L_1 \cup L_2)
     \land (R \setminus A) \cap (L_1 \cup L_2) = \emptyset
\end{eqnarray*}
\begin{code}
vReduce d (_,Comp ns [ (_,Comp na [ (_,Atm lI)    -- A(I
                                  , (_,Atm lO)    --  ,O
                                  , as            --  ,as
                                  , (_,Atm lR)    --  ,R
                                  , (_,Atm lA)    --  ,A
                                  , (_,Atm lL1)   --  ,L1) ;
                                  ])
                     , (_,Comp nd [(_,Atm ell2)]) -- D(L2)
                     ])
 | ns == nSeq && nd == nD && na == nA
   =  ( "A;D", bAnd [ bA lI lO as lR lA ell
                    , equal ((lR `sdiff` lA) `i` ell) emp
                    ])
 where ell = snd $ esimp d (lL1 `u` ell2)
\end{code}

\newpage
\HDRd{Reduce $A(I_1,O_1,as,R_1,A_1,L_1) \seq A(I_2,O_2,bs,R_2,A_2,L_2)$}


\begin{eqnarray*}
  && A(I_1,O_1,as,R_1,A_1,L_1) \seq A(I_2,O_2,bs,R_2,A_2,L_2)
\EQ{many, many steps}
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
\begin{code}
vReduce d (_,Comp ns [ (_,Comp na1 [ (_,Atm lI1)  -- A(I1
                                   , (_,Atm lO1)  --  ,O1
                                   , as           --  ,as
                                   , (_,Atm lR1)  --  ,R1
                                   , (_,Atm lA1)  --  ,A1
                                   , (_,Atm lL1)  --  ,L1) ;
                                   ])
                     , (_,Comp na2 [ (_,Atm lI2)  -- A(I2
                                   , (_,Atm lO2)  --  ,O2
                                   , bs           --  ,bs
                                   , (_,Atm lR2)  --  ,R2
                                   , (_,Atm lA2)  --  ,A2
                                   , (_,Atm lL2)  --  ,L2) ;
                                   ])
                     ])
 | ns == nSeq && na1 == nA && na2 == nA
   =  ( "A;A", bAnd [ bA lI lO asbs lR lA lL
                    , equal (((lL1 `u` lI2) `sdiff` lA1) `i` lR1)
                            emp
                    , equal (lA1 `i` lO2) emp
                    ])
 where
   lI = snd $ esimp d (lI1 `u` (lI2 `sdiff` lA1))
   lO = snd $ esimp d (lO1 `u` lO2)
   asbs = bSeq as bs
   lR = snd $ esimp d (lR1 `u` lR2)
   lA = snd $ esimp d ((lA1 `sdiff` lR2) `u` lA2)
   lL = lL2
\end{code}


\begin{eqnarray*}
   \lnot ls(L_1) \land A(I,O,\dots)
   &=&
   L_1 \cap I = \emptyset \land A(I,O\cup L_1,\dots)
\\ A(I,O,a,R,A,L')^2
   &=& I \cap R = \emptyset
    \land (I \setminus R \cup A \cup L') \cap O = \emptyset
    \land A(\dots)^2
\\ A(I,O,a,I,O,O)^2 &=& \false
\end{eqnarray*}
The latter two results will ``come out on the wash'',
so to speak, so don't need explicit reductions.
\begin{code}
vReduce d (_,Comp ns [ (_,Comp nn [(_,Atm lsL1)]) -- ~ls(L1) ;
                     , (_,Comp na [ (_,Atm lI)    -- A(I
                                  , (_,Atm lO)    --  ,O
                                  , as            --  ,as
                                  , (_,Atm lR)    --  ,R
                                  , (_,Atm lA)    --  ,A
                                  , (_,Atm lL2)   --  ,L2)
                                  ])
                     ])
 | ns == nAnd && nn == nNot && na == nA && isLS
   =  ( "~-ls(L);A"
      , if sEqual d (lI `i` lL1) emp == (True,F)
        then bF
        else bA lI (lO `u` lL1)  as lR lA lL2 )
 where
   (isLS,lL1) = matchls lsL1
   ell = snd $ esimp d (lsL1 `u` lI)
\end{code}


%Consider the following law:
%\RLEQNS{
%   P \land ls'=ls\ominus(S_1,S_2) \seq Q
%   &=&
%   P \land ls\ominus(S_1,S_2)=ls'
%   \seq
%   \lnot ls(S_1) \land ls(S_2) \land Q
%\\ && \elabel{sswap-$;$-prop.}
%}
%By flipping the $ls'=ls\ominus(S_1,S_2)$ equality
%we prevent continual re-application of this reduction step.
%\begin{code}
%vReduce d mpr@(_,Comp nm1 [mpr1@(_,Comp nm2 mprs1),mpr2])
% | nm1 == nSeq && nm2 == nAnd && isJust match
%     = ( "sswap-;-prop"
%       , bSeq (bAnd  ( before ++
%                        ( equal (sswap ls s1 s2) ls' : after )))
%              (bAnd [ bNot $ atm $ subset s1 ls
%                    , atm $ subset s2 ls
%                    , mpr2
%                    ]))
% where
%   match = matchRecog mtchLabelSetSSwap mprs1
%   Just (before,(_,[(_,Atm s1),(_,Atm s2)]),after) = match
%\end{code}

We find that $\W()$ defnitions
can be expressed a a disjunction
of sequential compositions of $D$ and $A$ with substitutions
for $g$, $in$ and $out$:
\[
  \W(C)
  =
  \left(
    \bigvee_{i=0}^n
      \left(
        {\large\seq}_{j=0}^{m_i}
           (D(L_{ij})|A(I_{ij},O_{ij},a_{ij},R_{ij},A_{ij},L'_{ij}))
           [G_{ij},\ell_{aij},\ell_{bij}/g,in,out]
      \right)
  \right)
\]
where $L_{00} = \setof{out}$ and $m_0=0$.
The above laws allow all of the above to collapse down to
\[
  \W(C)
  =
  D(out)
  \lor
  \left(
    \bigvee_{i=1}^{m \leq n}  A(I_{ij},O_{ij},a_{ij},R_{ij},A_{ij},L'_{ij})
                     [G_{ij},\ell_{ai},\ell_{bi}/g,in,out]
  \right)
\]
Basically $A$ absorbs $D$ on both left and right of sequential composition,
so the only $D$ that survives is the one capturing immediate termination.

This leads to naturally require the following distributivity laws
w.r.t to sequential composition:
\begin{eqnarray*}
   A \land (B \lor C) &=& (A \land B) \lor (A \land C)
\\ A \seq (B \lor C) &=& (A \seq B) \lor (A \seq C)
\\ (A \lor B) \seq C &=& (A \seq C) \lor (B \seq C)
\end{eqnarray*}

\begin{eqnarray*}
   A \land (B \lor C) &=& (A \land B) \lor (A \land C)
\end{eqnarray*}
\begin{code}
vReduce d (_,Comp na [ mpr, (_,Comp no mprs) ])
 | na == nAnd && no == nOr  =  ( "and-or-distr", bOr $ map f mprs )
 where f mpr' = bAnd [mpr , mpr']
\end{code}

\begin{eqnarray*}
   A \seq (B \lor C) &=& (A \seq B) \lor (A \seq C)
\end{eqnarray*}
\begin{code}
vReduce d (_,Comp ns [ mpr, (_,Comp no mprs) ])
 | ns == nSeq && no == nOr  =  ( ";-or-distr", bOr $ map f mprs )
 where f mpr' = bSeq mpr mpr'
\end{code}

\begin{eqnarray*}
  (A \lor B) \seq C &=& (A \seq C) \lor (B \seq C)
\end{eqnarray*}
\begin{code}
vReduce d (_,Comp ns [ (_,Comp no mprs), mpr ])
 | ns == nSeq && no == nOr  =  ( "or-;-distr", bOr $ map f mprs )
 where f mpr' = bSeq mpr' mpr
\end{code}

We prefer sequential chains to associate to the left:
\begin{eqnarray*}
   A \seq (B \seq C) &=& (A \seq B) \seq C
\end{eqnarray*}
\begin{code}
vReduce d (_,Comp ns1 [ mprA, (_,Comp ns2 [mprB, mprC]) ])
 | ns1 == nSeq && ns2 == nSeq
     =  ( ";-left-assoc", bSeq (bSeq mprA mprB) mprC )
\end{code}



\newpage
Default case: no change.
\begin{code}
vReduce _ mpr = ( "", mpr )
\end{code}

\HDRc{The Reduction Entry}\label{hc:WWW-reduce-ent}

\begin{code}
vRedEntry :: (Ord s, Show s) => Dict s
vRedEntry = entry laws $ LawEntry [vReduce] [] []
\end{code}


\HDRb{Conditional Reductions for WWW}\label{hb:WWW-creduce}

\begin{code}
vCReduce :: CDictRWFun s
\end{code}

Default case: no change.
\begin{code}
vCReduce _ mpr = ( "", [(T,mpr)] )
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
vUnroll :: Ord s => String -> DictRWFun s
vUnroll ns d miter@(_,Comp nm  [mc, mpr])
 | nm == nIter = ( "loop-unroll" ++ ntag ns, vunroll n )
 where

   ntag "" = ""
   ntag ns = '.':ns

   n | null ns = 0
     | isDigit $ head ns = digitToInt $ head ns
     | otherwise = 0

   vunroll 0  =  bCond (bSeq mpr miter) mc bSkip
   vunroll 1  =  bOr [ loopdone
                     , bSeq (loopstep 1) miter]
   vunroll 2  =  bOr [ loopdone
                     , bSeq (loopstep 1) loopdone
                     , bSeq (loopstep 2) miter]
   vunroll 3  =  bOr [ loopdone
                     , bSeq (loopstep 1) loopdone
                     , bSeq (loopstep 2) loopdone
                     , bSeq (loopstep 3) miter]
   vunroll _  =  bCond (bSeq mpr miter) mc bSkip

   loopdone = bAnd [bNot mc, bSkip]
   loopstep 1 = bAnd [mc, mpr]
   loopstep n = bSeq (loopstep (n-1)) (loopstep 1)

vUnroll _ _ mpr = ( "", mpr )
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
vshow :: (Show s, Ord s) => MPred s -> String
vshow = pmdshow 80 vDict noStyles

vput :: (Show s, Ord s) => MPred s -> IO ()
vput = putStrLn . vshow

vcalc mpr = calcREPL vDict mpr
vputcalc :: (Ord s, Show s) => MPred s -> IO ()
vputcalc mpr = printREPL vDict mpr

vsimp :: (Show s, Ord s) => MPred s -> (String, MPred s)
vsimp mpr
  = (what,mpr')
  where (_,what,mpr') = simplify vDict 42 mpr
vsimp2 :: (Show s, Ord s) => (String, MPred s) -> (String, MPred s)
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
pP = pvar "P" ; pQ = pvar "Q"  -- general programs
atomA = pvar "a"
atomB = pvar "b"

subII :: (Show s, Ord s) => MPred s
subII = psub bSkip [("g",g'1),("out",lg)]

--actionA = bA inp out atomA inp out out
--actionB = bA inp out atomB inp out out
actionA = bA inp emp atomA inp out out
actionB = bA inp emp atomB inp out out

athenb = actionA `vseq` actionB
\end{code}

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

\HDRc{$a \cseq b$}

\begin{eqnarray*}
  a \cseq b
   & =  & D(out)
\\ &\lor& A(in,out,a,in,\ell_g,\setof{out,\ell_g})
\\ &\lor& A(\ell_g,out,b,\ell_g,out,out)
\\ &\lor& A(in,out,a;b,\setof{in,\ell_g},out,out)
\end{eqnarray*}
