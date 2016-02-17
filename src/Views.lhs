\HDRa{Views}\label{ha:Views}
\begin{code}
module Views where
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


We do a quick run-down of the Commands\cite{conf/popl/Dinsdale-YoungBGPY13}.

\HDRb{Syntax}

\begin{eqnarray*}
   a &\in& \Atom
\\ C &::=& a \mid \cskip \mid C \cseq C \mid C+C \mid C \parallel C \mid C^*
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
vGenDict :: (Eq s, Ord s, Show s) => Dict s
vGenDict
 = makeDict
    [ (new1n,(ExprEntry True showGNew1 $ justMakes gNew1))
    , (new2n,(ExprEntry True showGNew2 $ justMakes gNew2))
    , (split1n,(ExprEntry True showGSplit1 $ justMakes gSplit1))
    , (split2n,(ExprEntry True showGSplit2 $ justMakes gSplit2))
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

\HDRd{Updating the Standard UTP Dictionary}

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
and suggest two important calcualtions:
\begin{eqnarray*}
   W &\defs& c * P
\\ D &\defs& \lnot c \land \Skip \EOLC{Done}
\\ S &\defs& c \land P \EOLC{Step}
\\ L &\defs& S ; D \EOLC{Last}
\\ T &\defs& D ; D \EOLC{Two-Step}
\end{eqnarray*}

We note some laws that apply to composition of $D$ with various
things, given certain substitutions, and noting that for us,
$D$ always has a specific instantiation:
\begin{eqnarray*}
   D &=& \LS{out} \land \Skip
\\ D ; D &= & D
\\ P \land \LSd{\ell} ; D[\ell/out] &=&  P \land \LSd{\ell}
\\ P \land \LSd{\B\ell} ; D[\ell/out] &=&  false
\\ D[\ell_1/out] ; D[\ell_2/out] &=& false,\textbf{ if }\ell_1/\neq\ell_2
\end{eqnarray*}

We now illustrate with the definition of $a$,
using subscripts indicating that we are instantiating the above shorthands
w.r.t. the semantics of $a$:

\begin{eqnarray*}
   a &\defs& \W( \LS{in} \land \ado a \land \LUPD{in}{out} )
\\ &=& W_a
\\ D &\defs& \D \EOLC{Independent of $a$.}
\\ S_a &\defs& \LS{\B{out}}
               \land \LS{in} \land \ado a \land \LUPD{in}{out}
\\ L_a &\defs& S_a ; D
\\ &=& \LS{\B{out}}
               \land \LS{in} \land \ado a \land \LUPD{in}{out}
\\ && {} ; \LS{out} \land \Skip
\EQ{shorthand law, and $\Skip$ is $;$-identity}
\\ && \LS{\B{out}}
               \land \LS{in} \land \ado a \land \LUPD{in}{out}
\\ T_a &\defs& S_a ; S_a
\\ &=& \LS{\B{out}}
               \land \LS{in} \land \ado a \land \LUPD{in}{out}
\\ && {} ; \LS{\B{out}}
               \land \LS{in} \land \ado a \land \LUPD{in}{out}
\EQ{shorthand law}
\\ && \LS{\B{out}}
               \land \LS{in} \land \ado a \land \LUPD{in}{out}
\\ && {} ; \LS{out} \land \LS{\B{out}}
               \land \LS{in} \land \ado a \land \LUPD{in}{out}
\\ &=& false
\end{eqnarray*}
We see that all terms $S_a^i$ for $i \geq 2$ just vanish, so
\begin{eqnarray*}
   a &=& D \lor L_a
\\ &=& \D \;\lor\; \LS{\B{out}}
               \land \LS{in} \land \ado a \land \LUPD{in}{out}
\end{eqnarray*}


We overload sequential composition as follows:
\begin{eqnarray*}
   \ado{a;b} &=& \ado a ; \ado b
\end{eqnarray*}

Now we look at $a \cseq b$:
\begin{eqnarray*}
   a \cseq b
   &=& \W(a[g_{:1},\ell_g/g,out] \lor b[g_{:2},\ell_g/g,in])
\\ &=& W_;
\\ D &\defs& \D \EOLC{Independent of $a\cseq b$.}
\\ S_; &=& a[g_{:1},\ell_g/g,out] \lor b[g_{:2},\ell_g/g,in]
\EQ{calc. of $a$ above}
\\ && (D \lor L_a)[g_{:1},\ell_g/g,out]
      \lor
      (D \lor L_b)[g_{:2},\ell_g/g,in]
\\&=& \LS{\ell_g} \land \Skip
      \lor \LS{\B{\ell_g}}
           \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g} \lor {}
\\&& \LS{out} \land \Skip
      \lor \LS{\B{out}}
           \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
\\ L_; &=& S_; ; D
\\ &=& (~\LS{\ell_g} \land \Skip
      \lor \LS{\B{\ell_g}}
           \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g} \lor {}
\\&& \LS{out} \land \Skip
      \lor \LS{\B{out}}
           \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}~)
\\&& {} ; \LS{out} \land \Skip
\\ &=& (\LS{\ell_g} \land \Skip ; \LS{out} \land \Skip) \lor{}
\\ &&  (\LS{\B{\ell_g}}
       \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g}
       ; \LS{out} \land \Skip) \lor {}
\\ &&  (\LS{out} \land \Skip ; \LS{out} \land \Skip )\lor {}
\\ &&  (\LS{\B{out}}
           \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
           ; \LS{out} \land \Skip )
\\ &=& \LS{out} \land \Skip \lor
       \LS{\B{out}}
       \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
\\ S_; ; L_; &=&
     \LS{\ell_g} \land \Skip \lor{}
\\&& \LS{\B{\ell_g}}
           \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g} \lor {}
\\&& \LS{out} \land \Skip \lor {}
\\&&\LS{\B{out}}
           \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
\\&& ;
\\&& \LS{out} \land \Skip \lor {}
\\&& \LS{\B{out}}
       \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
\end{eqnarray*}
We pause here, to do a little methodological innovation.
We introduce the notion of a ``label-type''
which is a  list of labels (in $\ltype\dots$),
which might be dashed,
and might be prefixed with negation.
We interpret these as follows:

\begin{tabular}{|c|c|}
  \hline
  % after \\: \hline or \cline{col1-col2} \cline{col3-col4} ...
  $\ell$ & we assert $ls(\ell)$ \\
  $\B\ell$ & we assert $\lnot ls(\ell)$ \\
  $\ell'$ & we assert $ls'(\ell)$ \\
  $\B\ell'$ & we assert $\lnot ls'(\ell)$ \\
  \hline
\end{tabular}

These lists are interpreted as conjunction.
This helps us to quickly spot predicates that reduce to
contradictions when sequentially composed.
Here is $S_; ; L_;$ with label-types added
\RLEQNS{
   S_; ; L_; &=&
     \LS{\ell_g} \land \Skip \lor{}
      & \ltype{\ell_g,\ell'_g}
\\&& \LS{\B{\ell_g}}
           \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g} \lor {}
      & \ltype{\B{\ell_g},in,\B{in'}, \ell'_g}
\\&& \LS{out} \land \Skip \lor {}
     & \ltype{out,out'}
\\&&\LS{\B{out}}
           \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
           & \ltype{\B{out},\ell_g,\B{\ell'_g},out'}
\\&& ;
\\&& \LS{out} \land \Skip \lor {}  & \ltype{out,out'}
\\&& \LS{\B{out}}
       \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
       & \ltype{\B{out},\ell_g,\B{\ell'_g},out'}
}
We see that the last two disjuncts of $S_;$ contradict the last disjunct
of $L_;$, so we get
\begin{eqnarray*}
  &&
     \LS{\ell_g} \land \Skip ; \LS{out} \land \Skip \lor{}
\\&& \LS{\B{\ell_g}}
           \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g}
            ; \LS{out} \land \Skip\lor {}
\\&& \LS{out} \land \Skip ;\LS{out} \land \Skip\lor {}
\\&&\LS{\B{out}}
           \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
           ; \LS{out} \land \Skip \lor {}
\\&&
     \LS{\ell_g} \land \Skip
     ; \LS{\B{out}}
       \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out} \lor{}
\\&& \LS{\B{\ell_g}}
           \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g}
            ; \LS{\B{out}}
       \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
\EQ{with care\dots}
\\&&\LS{\ell_g} \land\LS{out} \land \Skip
\\&& \LS{\B{\ell_g}}
           \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g}
            \land \LSd{out} \lor {}
\\&& \LS{out} \land \Skip  \lor {}
\\&&\LS{\B{out}}
           \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
           \lor {}
\\&& \LS{\B{out}}
       \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out} \lor{}
\\&& \LS{\B{\ell_g}} \land \LS{in} \land \LS{\B{out}}
    \land \ado{a;b}\land \LUPD{in}{out}
\EQ{\ldots tidy-up}
\\&& \LS{out} \land \Skip \lor {}
\\&& \LS{\B{\ell_g}}
           \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g}
            \land \LSd{out} \lor {}
\\&& \LS{\B{out}}
       \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out} \lor{}
\\&& \LS{\B{\ell_g}} \land \LS{in} \land \LS{\B{out}}
    \land \ado{a;b}\land \LUPD{in}{out}
\end{eqnarray*} Hmmm\dots

We look at $S_;^2 ; L_;$ now.
\RLEQNS{
   S^2_; ; L_; &=&
     \LS{\ell_g} \land \Skip \lor{}
      & \ltype{\ell_g,\ell'_g}
\\&& \LS{\B{\ell_g}}
           \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g} \lor {}
      & \ltype{\B{\ell_g},in,\B{in'}, \ell'_g}
\\&& \LS{out} \land \Skip \lor {}
     & \ltype{out,out'}
\\&&\LS{\B{out}}
           \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out}
           & \ltype{\B{out},\ell_g,\B{\ell'_g},out'}
\\&& ;
\\&& \LS{out} \land \Skip \lor {}
\\&& \LS{\B{\ell_g}}
           \land \LS{in} \land \ado a \land \LUPD{in}{\ell_g}
            \land \LSd{out} \lor {}
\\&& \LS{\B{out}}
       \land \LS{\ell_g} \land \ado b \land \LUPD{\ell_g}{out} \lor{}
\\&& \LS{\B{\ell_g}} \land \LS{in} \land \LS{\B{out}}
    \land \ado{a;b}\land \LUPD{in}{out}
}

\HDRb{Atomic Shorthands}

We find essentially just two idioms here,
where $L$, $I$, $O$, $R$ and $A$ are lists of labels,
with $I \cap O = \emptyset$ and $R \cap A = \emptyset$:
\begin{eqnarray*}
   D(L) &\defs&  \LS{L} \land \Skip
\\ &=& ls(L) \land s'=s \land ls'=ls
\\ &=& ls(L) \land s'=s \land ls'=ls \land ls'(L)
\\ &=& \LS{L} \land \Skip \land \LSd{L}
\\ &:&  \ltype{L,L'}
\\ A(I,O,as,R,A,L)
   &\defs& \LS{I} \land \LS{\B O}
           \land \ado{as}
           \land \LUPD{R}{A} \land \LSd{L}
\\ &=& ls(I) \land ls(\B O) \land \ado{as}
       \land ls'=ls\ominus(R|A) \land ls'(L)
\\ &:& \ltype{I,\B O,\B{R'\setminus A'},L',A'}
\\ &=& I \cap O = \emptyset \land ls(I) \land ls(\B O)
\\ && {} \land \ado{as}
\\ && {} \land ls'=ls\ominus(R|A) \land ls'(L)
         \land (R\setminus A) \cap L = \emptyset
\end{eqnarray*}
The first and second lines above in each definition/expansion
are the so-called ``implicit'' forms,
in that we have a minimal complete description,
but without any explicit identification of situations that force
the predicate to evaluate to false.
The last version of $A$ above is the so-called ``explicit-form'',
which states the relationships on parameters $I$, $O$, $R$, $A$ and $L$
that most hold in order for the predicate not to be false everywhere.



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

\HDRc{Proofs}

Full forms
\begin{eqnarray*}
   D(L)
   &\defs& \LS{L} \land \Skip
\\ &  =  & ls(L) \land s'=s \land ls'=ls
\\
\\ A(I,O,as,R,A,L)
   &\defs&
   \LS{I} \land \LS{\B O} \land \ado{as} \land \LUPD{R}{A} \land \LSd{L}
\\ &  =  & ls(I) \land ls(\B O) \land \ado{as} \land \lupd R A \land ls'(L)
\end{eqnarray*}

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
\EQ{Defn. $A$, fold}
\\&& A(L_1 \cup I,O,as,R,A,L_2)
\end{eqnarray*}

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
\EQ{Defn. $A$, fold}
\\&& A(I,O,as,R,A,L_1 \cup L_2)
\end{eqnarray*}

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

vEntry :: (Show s, Ord s) => (String, Entry s)
vEntry
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

\HDRb{WwW Semantic Definitions}

The definitions, using the new shorthand:
\begin{eqnarray*}
   \W(C) &\defs& ls(\B{out}) * C)
\\ ii &\defs& s'=s
\\
\\ a &\defs&\W(A(in,\emptyset,a,in,out,out))
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
   , PredEntry False ppVSeq [] defnVSeq (pNoChg nVSeq) )
\end{code}


\HDRc{The Predicate Dictionary}\label{hc:WWW-pred-dict}

\begin{code}
dictVP :: (Ord s, Show s) => Dict s
dictVP = makeDict [vEntry,patmEntry,vSeqEntry]
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
vReduce d mpr@(_,Comp nm1 [mpr1@(_,Comp nm2 mprs1),mpr2])
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



\HDRb{Loop Unrolling for WWW}\label{hb:WWW-unroll}

Here we remove the requirement that the loop predicate
be a condition.
Iteration  satisfies the loop-unrolling law:
\[
  C * P  \quad=\quad (P ; C * P ) \cond C \Skip
\]
\begin{code}
vUnroll :: Ord s => DictRWFun s
vUnroll d mw@(_,Comp nm  [mc, mpr])
 | nm == nIter = ( "WWW unroll"
                 , bCond (bSeq mpr mw) mc bSkip )
vUnroll _ mpr = ( "", mpr )
\end{code}

\HDRc{The Unroll Entry}\label{hc:WWW-reduce-ent}

\begin{code}
vLoopEntry :: (Ord s, Show s) => Dict s
vLoopEntry = entry laws $ LawEntry [] [] [vUnroll]
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
athenb = atomA `vseq` atomB

subII :: (Show s, Ord s) => MPred s
subII = psub bSkip [("g",g'1),("out",lg)]
\end{code}























