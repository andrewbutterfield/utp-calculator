\HDRa{Wheels Within Wheels}\label{ha:WWW}
\begin{code}
module WWW where
import Utilities
-- import qualified Data.Map as M
import Data.List
-- import Data.Char
import Data.Maybe
-- import Debug.Trace
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

%%
%% local macros
%%
\def\W{\mathbf{W}}
\HDRb{Introduction to WWW}\label{hb:WWW-intro}

This is UTCP where we explore the ``WWW'' variant
based on the healthiness condition:
\RLEQNS{
\W(P) &\defs& \lnot ls(out) * P
}

\HDRb{Variables of WWW}\label{hb:WWW-vars}

We shall define some generic \texttt{PVar}s:
\begin{code}
pA = pvar "A" ; pB = pvar "B"  -- atomic actions
pP = pvar "P" ; pQ = pvar "Q"  -- general programs
\end{code}


\HDRc{Alphabet of WWW}\label{hb:WWW-alpha}

\HDRd{Dynamic Observables}

Program (variable) state
($s,s' : State = Var \pfun Val$),
and the set of active labels
($ls,ls': \Set Label$).
\begin{code}
s  = Var "s"  ; s'  = Var "s'"
ls = Var "ls" ; ls' = Var "ls'"
\end{code}

\HDRd{Static Parameters}

Label Generator
($g : Gen$),
and the variables that record the start label
($in:Label$)
and the finish label
($out:Label$).
\begin{code}
g   = Var "g"
inp = Var "in" -- "in" is a Haskell keyword
out = Var "out"
\end{code}

\HDRc{The Alphabet Dictionary}\label{hc:WWW-alfa-dict}

We define our dictionary alphabet entries,
and also declare that the predicate variables $A$, $B$ and $C$
will refer to atomic state-changes, and so only have alphabet $\setof{s,s'}$.
\begin{code}
w3AlfDict
 = dictMrg dictAlpha dictAtomic
 where
   dictAlpha = stdAlfDictGen ["s"] ["ls"] ["g","in","out"]
   dictAtomic = makeDict [ pvarEntry "A" ss'
                         , pvarEntry "B" ss'
                         , pvarEntry "C" ss' ]
   ss' = ["s", "s'"]
\end{code}


\HDRb{Expressions of WWW}\label{hb:WWW-expr}


\HDRc{Set Expressions}

We use sets in two key ways:
checking for membership/subset inclusion;
and updating by removing elements.
\begin{code}
setn = "set"
set = App setn

mkSet :: Ord s => [Expr s] -> Expr s
mkSet = set . sort . nub

showSet d elms = "{" ++ dlshow d "," elms ++ "}"

evalSet _ _ = none
\end{code}


\HDRd{Set Membership}\label{hd:membership}~

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
\end{code}

We support a shorthand (that views a set as its own collection
of corresponding $n$-ary characteristic functions)
that denotes $x \in S$ by $S(x)$ and $ X \subseteq S$ by $S(X)$,
and omits $\{$ and $\}$ from around enumerations when context makes
it clear a set is expected

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
w3SetDict :: (Eq s, Ord s, Show s) => Dict s
w3SetDict
 = makeDict
    [ (setn,(ExprEntry True showSet evalSet))
    , (subsetn,(ExprEntry True showSubSet evalSubset))
    , (sswapn, (ExprEntry True showSSwap evalSSwap))
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
w3GenDict :: (Eq s, Ord s, Show s) => Dict s
w3GenDict
 = makeDict
    [ (new1n,(ExprEntry True showGNew1 $ justMakes gNew1))
    , (new2n,(ExprEntry True showGNew2 $ justMakes gNew2))
    , (split1n,(ExprEntry True showGSplit1 $ justMakes gSplit1))
    , (split2n,(ExprEntry True showGSplit2 $ justMakes gSplit2))
    ]
\end{code}

\HDRc{The Expression Dictionary}\label{hc:WWW-expr-dict}

\begin{code}
dictW3E :: (Ord s, Show s) => Dict s
dictW3E = w3SetDict `dictMrg` w3GenDict
\end{code}

\HDRb{Predicates for WWW}\label{hb:WWW-stmt}

\RLEQNS{
   A,B \in Action &:& State \rel State & \say{Atomic state transformer}
\\ p,q \in W3
   &::=& Idle & \say{Do nothing}
\\ &|& \A(A) & \say{Atomic process}
\\ &|& p \lseq q & \say{Sequential composition}
\\ &|& p \lcond c q & \say{Conditional}
\\ &|& p \parallel q & \say{Parallel composition}
\\ &|& c \wdo p & \say{Iteration}
}
We assign the following precedences to W3 syntactical constructs,
interleaving them among the standard predicates.
\begin{code}
precWCond = 5 + precSpacer  1
precWPar  = 5 + precSpacer  2
precWSeq  = 5 + precSpacer  3
precWIter = 5 + precSpacer  6
\end{code}

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

wEntry :: (Show s, Ord s) => (String, Entry s)
wEntry
 = ( nW
   , PredEntry False ppW [] defnW (pNoChg nW) )
\end{code}
We need to show it is idempotent (monotonicty is immediate):
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
Idempotency is now immediate.
Of interest are healthified predicates in sequence
and in disjunctions:
\RLEQNS{
   \W(X) \seq \W(Y) &=& \W(X)
\\ \W(P \lor Q) &=& (P \lor Q) \seq \W(P \lor Q) \cond{\lnot ls(out)} \Skip
\\ &=& ls(out) \land \Skip
\\ &\lor& \lnot ls(out) \land P \seq \W(P \lor Q)
\\ &\lor& \lnot ls(out) \land Q \seq \W(P \lor Q)
\\ \multicolumn{4}{l}{\mbox{below we assume } P=\W(P) \land Q=\W(Q)}
\\ &=& ls(out) \land \Skip
\\ &\lor& \lnot ls(out) \land \W(P) \seq \W(P \lor Q)
\\ &\lor& \lnot ls(out) \land \W(Q) \seq \W(P \lor Q)
\\ &=& ls(out) \land \Skip
\\ &\lor& \lnot ls(out) \land \W(P)
\\ &\lor& \lnot ls(out) \land \W(Q)
\\ &=& (\W(P) \lor \W(Q)) \cond{\lnot ls(out)} \Skip
}
A surprise---the following two healthiness conditions are equivalent,
and the third looks equivalent also (not yet verified)
\RLEQNS{
   \W &:&  P = c * P
\\ \mathbf{Z} &:&  P =  P \cond c \Skip
\\ \mbox{?} &:& c \land P = c \land P \land \lnot c'
}
We are assuming here that $P$ is arbitrary, but that $c$ is fixed,
and not  equivalent to $\true$.
However, as healithifiers they are quite different:
\RLEQNS{
  \lambda P @ c * P &\neq& \lambda P @ P \cond c \Skip
\\ \W(P) &\neq& \mathbf{Z}(P)
}
However, lovely as all those laws are,
they don't help much because we shall use substitutions
to replace $out$ by unique labels derived from generators.


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
   , PredEntry False ppPAtm [] defnAtomic (pNoChg nPAtm) )
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
nWSeq = "WSeq"
isWSeq (_,Comp n [_,_]) | n==nWSeq = True; isWSeq _ = False

wseq p q = comp nWSeq [p,q]

shWSeq = ";;"
ppWSeq d ms p [mpr1,mpr2]
 = paren p precWSeq
     $ ppopen  (pad shWSeq) [ mshowp d ms precWSeq mpr1
                            , mshowp d ms precWSeq mpr2 ]
ppWSeq d ms p mprs = pps styleRed $ ppa ("invalid-"++shWSeq)

defnWSeq d [p,q]
 = ldefn shWSeq $ wp $ bOr [psub p sub1, psub q sub2]
 where
   sub1 = [("g",g'1),("out",lg)]
   sub2 = [("g",g'2),("in",lg)]

lg = new1 g
g' = new2 g
g'1 = split1 g'
g'2 = split2 g'

wSeqEntry :: (Show s, Ord s) => (String, Entry s)
wSeqEntry
 = ( nWSeq
   , PredEntry False ppWSeq [] defnWSeq (pNoChg nWSeq) )
\end{code}


\HDRc{The Predicate Dictionary}\label{hc:WWW-pred-dict}

\begin{code}
dictW3P :: (Ord s, Show s) => Dict s
dictW3P = makeDict [wEntry,patmEntry,wSeqEntry]
\end{code}



\HDRb{Reductions for WWW}\label{hb:WWW-reduce}

\HDRc{Recognisers for WWW}\label{hc:w3-recog}

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

\HDRc{\texttt{w3Reduce}}\label{hc:w3Reduce}

\begin{code}
w3Reduce :: (Ord s, Show s) => DictRWFun s
         -- Dict s -> MPred s -> (String, MPred s)
\end{code}

The first case we consider is the following law:
\RLEQNS{
   P \land ls'=ls\ominus(S_1,S_2) \seq Q
   &=&
   P \land ls\ominus(S_1,S_2)=ls'
   \seq
   \lnot ls(S_1) \land ls(S_2) \land Q
\\ && \elabel{sswap-$;$-prop.}
}
By flipping the $ls'=ls\ominus(S_1,S_2)$ equality
we prevent continual re-application of this reduction step.
\begin{code}
w3Reduce d mpr@(_,Comp nm1 [mpr1@(_,Comp nm2 mprs1),mpr2])
 | nm1 == nSeq && nm2 == nAnd && isJust match
     = ( "sswap-;-prop"
       , bSeq (bAnd  ( before ++
                        ( equal (sswap ls s1 s2) ls' : after )))
              (bAnd [ bNot $ atm $ subset s1 ls
                    , atm $ subset s2 ls
                    , mpr2
                    ]))
 where
   match = matchRecog mtchLabelSetSSwap mprs1
   Just (before,(_,[(_,Atm s1),(_,Atm s2)]),after) = match
\end{code}

Default case: no change.
\begin{code}
w3Reduce _ mpr = ( "", mpr )
\end{code}

\HDRc{The Reduction Entry}\label{hc:WWW-reduce-ent}

\begin{code}
w3RedEntry :: (Ord s, Show s) => Dict s
w3RedEntry = entry laws $ LawEntry [w3Reduce] [] []
\end{code}


\HDRb{Conditional Reductions for WWW}\label{hb:WWW-creduce}

\begin{code}
w3CReduce :: CDictRWFun s
\end{code}

Default case: no change.
\begin{code}
w3CReduce _ mpr = ( "", [(T,mpr)] )
\end{code}

\HDRc{The Conditional Reduction Entry}\label{hc:WWW-reduce-ent}

\begin{code}
w3CRedEntry :: (Ord s, Show s) => Dict s
w3CRedEntry = entry laws $ LawEntry [] [w3CReduce] []
\end{code}



\HDRb{Loop Unrolling for WWW}\label{hb:WWW-unroll}

Here we remove the requirement that the loop predicate
be a condition.
Iteration  satisfies the loop-unrolling law:
\[
  C * P  \quad=\quad (P ; C * P ) \cond C \Skip
\]
\begin{code}
w3Unroll :: Ord s => DictRWFun s
w3Unroll d mw@(_,Comp nm  [mc, mpr])
 | nm == nIter = ( "WWW unroll"
                 , bCond (bSeq mpr mw) mc bSkip )
w3Unroll _ mpr = ( "", mpr )
\end{code}

\HDRc{The Unroll Entry}\label{hc:WWW-reduce-ent}

\begin{code}
w3LoopEntry :: (Ord s, Show s) => Dict s
w3LoopEntry = entry laws $ LawEntry [] [] [w3Unroll]
\end{code}


\HDRb{Dictionary for WWW}\label{hb:WWW-laws}

\begin{code}
w3Dict :: (Ord s, Show s) => Dict s
w3Dict
 =  dictVersion "WWW 0.1"
    `dictMrg` w3AlfDict
    `dictMrg` dictW3E
    `dictMrg` dictW3P
    `dictMrg` w3RedEntry
    `dictMrg` w3CRedEntry
    `dictMrg` w3LoopEntry
    `dictMrg` lawsUTCPDict
    `dictMrg` stdUTPDict
    `dictMrg` stdDict
\end{code}


\HDRb{WWW Calculator}\label{hb:WWW-CALC}

\begin{code}
w3show :: (Show s, Ord s) => MPred s -> String
w3show = pmdshow 80 w3Dict noStyles

w3put :: (Show s, Ord s) => MPred s -> IO ()
w3put = putStrLn . w3show


w3calc mpr = calcREPL w3Dict mpr
w3putcalc :: (Ord s, Show s) => MPred s -> IO ()
w3putcalc mpr = printREPL w3Dict mpr

w3simp :: (Show s, Ord s) => MPred s -> (String, MPred s)
w3simp mpr
  = (what,mpr')
  where (_,what,mpr') = simplify w3Dict 42 mpr
w3simp2 :: (Show s, Ord s) => (String, MPred s) -> (String, MPred s)
w3simp2 = w3simp . snd
\end{code}
