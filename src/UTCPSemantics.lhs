\HDRa{UTCP Semantics}\label{ha:UTCP-semantics}
\begin{code}
module UTCPSemantics where
import Utilities
import Data.List
import PrettyPrint
import CalcTypes
import CalcAlphabets
import CalcPredicates
import CalcSimplify
import CalcRecogniser
import CalcSteps
import StdPrecedences
import StdPredicates
import StdUTPPredicates
\end{code}

Version
\begin{code}
versionUTCP = "UTCP-0.7"
\end{code}

\HDRb{UTCP Syntax}

\RLEQNS{
   A,B \in Action &:& State \rel State & \say{Atomic state transformer}
\\ p,q \in UTCP
   &::=& Idle & \say{Do nothing}
\\ &|& \A(A) & \say{Atomic process}
\\ &|& p \lseq q & \say{Sequential composition}
\\ &|& p \lcond c q & \say{Conditional}
\\ &|& p \parallel q & \say{Parallel composition}
\\ &|& c \wdo p & \say{Iteration}
}


We assign the following precedences to UTCP syntactical constructs,
interleaving them among the standard predicates.
\begin{code}
precPCond = 5 + precSpacer  1
precPPar  = 5 + precSpacer  2
precPSeq  = 5 + precSpacer  3
precPIter = 5 + precSpacer  6
\end{code}


\HDRb{Dynamic and Static Observations}

The theory we built uses predicate variables
to record observations of program behaviour
in two distinct ways:
\begin{enumerate}
  \item
    Making observations of dynamic state change,
    using un-decorated variables to record before-values,
    and dashed variables to denote the corresponding after-value,
    as is the norm in most UTP theories.
    We shall refer to these as \emph{dynamic observables}.
  \item
    Some observations record context information that
    is propagated throughout a program.
    This information does not change during the lifetime of a program execution,
    and so only needs to be recorded using un-decorated variables.
    We shall call these \emph{static parameters}.
\end{enumerate}

\HDRc{Theory Alphabet}
The alphabet we shall use for our UTP theory of concurrent shared variables
is
\[ s,s',ls,ls',g,in,out \]

\HDRd{Dynamic Observables}

\begin{description}
  \item[State] $s,s' : State = Var \pfun Val$
    --- program (variable) state
\begin{code}
s = Var "s"
s' = Var "s'"
\end{code}
  \item[Label-Set] $ls,ls': \Set Label$
    --- set of active labels
\begin{code}
ls = Var "ls"
ls' = Var "ls'"
\end{code}
\end{description}

\HDRd{Static Parameters}
\begin{description}
  \item[Label Generator] $g : Gen$
  --- Base for generating new unique labels
\begin{code}
g = Var "g"
\end{code}
  \item[Input Place] $in : Label$
  --- Holds the value of the label that starts execution
\begin{code}
inp = Var "in" -- "in" is a Haskell keyword
\end{code}
  \item[Output Place] $out : Label $
  --- Holds the value of the label that signals termination
\begin{code}
out = Var "out"
\end{code}
\end{description}
These are described in more detail below.

We define our dictionary alphabet entries,
and also declare that the predicate variables $A$, $B$ and $C$
will refer to atomic state-changes, and so only have alphabet $\setof{s,s'}$.
\begin{code}
alfUTCPDict
 = dictMrg dictAlpha dictAtomic
 where
   dictAlpha = stdAlfDictGen ["s"] ["ls"] ["g","in","out"]
   dictAtomic = makeDict [ pvarEntry "A" ss'
                         , pvarEntry "B" ss'
                         , pvarEntry "C" ss' ]
   ss' = ["s", "s'"]
\end{code}




\HDRb{Our View of a Concurrent Program}

We view the semantics of a concurrent program as being a collection
of all its atomic actions, each with an associated guard that enables
it, those guards being based on the presence or absence of labels
from what we will call the global ``label set'' ($ls$).
An enabled atomic action will run when its input label ($in$) is in $ls$,
at which point in time
it will make changes to the global shared variable state ($s$),
remove its $in$ label from $ls$,
and add its output label ($out$) to that set
(\figref{fig:atom-act:view}).
A key point here to note is that every construct has both a input (start) label,
and a output (finish) label,
and its semantics is defined solely in terms of those.
The output label in particular,
belongs to the construct itself
and is not the label (or labels) of ``whatever comes after''.

\begin{figure}[h]
  \centering
\includegraphics{images/atomic-action.eps}
  \caption{Atomic Action view of the world}
  \label{fig:atom-act:view}
\end{figure}

\HDRc{Alphabet (Part 1)}

We shall assume types for variable state ($State$) and labels ($Label$),
and introduce the following observation variables:
\RLEQNS{
   in, out &:& Label
\\ ls, ls' &:& \power Label
\\ s, s' &:& State
\\ AlfState &=& Label^2 \times (\power Label)^2 \times State
}
The observations $in$ and $out$ have no dashed counterparts,
as they are static parameters that do not change over time.

\HDRc{Atomic Action Semantics}

Let us consider an atomic state change operation,
viewed as a before-after relation on $State$:
\RLEQNS{
   A(s,s') &:& State \rel State
}
We lift this into an atomic concurrent action over the full alphabet
using $\A$,
by defining
the appropriate behaviour w.r.t to $in$, $out$, $ls$ and $ls'$:
\RLEQNS{
   \A(A)
   &\defs&
         in \in ls
   \land A
   \land ls' = (ls \setminus \setof{in}) \cup \setof{out}
}
The situation with language composites is more complex, as we shall see.


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


\newpage
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
as summarised in \figref{fig:short:membership}.

\begin{figure}[h]
  \centering
\begin{tabular}{|c|c|}
\hline
  Longhand & Shorthand
\\\hline
  $x \in S$ & $S(x)$
\\\hline
  $x \in \setof{y_1,\ldots,y_n} $ & $\setof{y_1,\ldots,y_n}(x)$
\\\hline
  $\setof{x_1,\ldots,x_n} \subseteq S$  & $S( x_1,\ldots,x_n)$
\\\hline
  $T \subseteq S$ & $S(T)$
\\\hline
  $\setof x$ &    $x$ (if context permits)
\\\hline
\end{tabular}
  \caption{Set Membership Shorthands}
  \label{fig:short:membership}
\end{figure}

The aim is to minimise displayed expression widths.
This induces some funny looking laws:
\RLEQNS{
   x(x) &=& \true  & \mbox{think: } x \in \setof x \mbox{ is true}
\\ x(y) &=& \false & \mbox{think: } y \in \setof x \mbox{ is false, if }y\neq x
}
\begin{code}
showSubSet d [App "set" elms,App "set" [set]]
 = edshow d set ++ "(" ++ dlshow d "," elms ++ ")"
showSubSet d [App "set" elms,set]
 = edshow d set ++ "(" ++ dlshow d "," elms ++ ")"
showSubSet d [e,set]
 = edshow d set ++ "(" ++ edshow d e ++ ")"
\end{code}


\newpage
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


Label Swap:

The Set Dictionary:
\begin{code}
setUTCPDict :: (Eq s, Ord s, Show s) => Dict s
setUTCPDict
 = makeDict
    [ (setn,(ExprEntry True showSet evalSet))
    , (subsetn,(ExprEntry True showSubSet evalSubset))
    , (sswapn, (ExprEntry True showSSwap evalSSwap))
    ]
\end{code}

\newpage
\HDRc{Coding Atomic Semantics}

Formally, using our shorthand notations, we can define atomic behaviour as:
\RLEQNS{
    \A(A) &\defs& ls(in) \land A \land ls'=ls\ominus(in,out)
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

defnAtomic d [a] = ldefn shPAtm $ mkAnd [lsin,a,ls'eqlsinout]

lsin = atm $ App subsetn [inp,ls]
lsinout = App sswapn [ls,inp,out]
ls'eqlsinout = equal ls' lsinout

patmEntry :: (Show s, Ord s) => (String, Entry s)
patmEntry
 = ( nPAtm
   , PredEntry False ppPAtm [] defnAtomic (pNoChg nPAtm) )
\end{code}

A special case of this is the $Idle$ construct:
\RLEQNS{
   Idle &\defs& \A(s'=s)
\\      &=& s(in) \land s'=s \land ls'=ls\ominus(in,out)
}
\begin{code}
nPIdle = "PIdle"
isPIdle (_,Comp n []) | n==nPIdle = True; isPIdle _ = False

pidle = comp nPIdle []

shPIdle = "Idle" -- show name
ppPIdle d ms p [] = ppa shPIdle
ppPIdle d ms p mprs = pps styleRed $ ppa ("invalid-"++shPIdle)

defnIdle d [] = ldefn shPIdle $ Equal s' s

pidleEntry :: (Show s, Ord s) => (String, Entry s)
pidleEntry
 = ( nPIdle
   , PredEntry False ppPIdle [] defnIdle (pNoChg nPIdle) )
\end{code}

Given that $\alpha A = \setof{s,s'}$, we have:
\RLEQNS{
   \A(A)[\vec e/\vec x]
    &\defs&
          ls(in)[\vec e/\vec x]
    \land A [\vec e/\vec x]\!|_{s,s'}
    \land (ls'=ls\ominus(in,out))[\vec e/\vec x]
    & \elabel{sub-atomic}
}
Here the notation $[\vec e/\vec x]\!|_V$ denotes the substitution restricted
to the variables in $V$.
\begin{code}
substnAtomic d a subs
  = mkAnd (psub a rsubs
          : map (noMark . snd . psubst startm d subs)
                                           [lsin, ls'eqlsinout])
  where rsubs = filter ((`elem` ["s","s'"]) . fst) subs
\end{code}
However, this can be subsumed by \eref{pvar-substn},
if we have information about the alphabet of $A$.

\HDRc{Composite Semantics}

Our composites are:

For composite language constructs to work,
we require that the context of components is somehow ``informed''
of how it is being situated.
We consider this the semantic repsonsibilty of the composite itself,
and not something the components need to consider.

Let us consider sequential composition ($P \lseq Q$).
In effect, the $\lseq$ operator has to glue its components
so that the $out$ label of the first corresponds to the $in$ label
of the second.
So, in effect, we need an outcome as follows (\figref{fig:seq-idea:view}):
\RLEQNS{
   P \lseq Q  &\defs& P[\ell/out] \lor Q[\ell/in], & \mbox{given ``fresh'' }\ell
}

\begin{figure}[h]
  \centering
\includegraphics{images/seq-comp-idea.eps}
  \caption{Sequential Composition view of the world}
  \label{fig:seq-idea:view}
\end{figure}

We have a disjunction because it may be possible for both to be active
at the same time (consider $(P \lseq Q) \parallel (P \lseq Q))$.
The key issue we have to address, is how to obtain the label $\ell$.
It has to be unique to that instance of $\lseq$, but also has to be globally
visible, so the use of quantification to hide it will not do.
We also have to ensure that this contruction works
not just for atomic $P$ and $Q$, but also for arbitrary composites.
The solution is to provide a way to generate and propagate labels
that satisfy our requirements.

\HDRc{Label Generation}

Imagine that we have a mechanism for generating labels as follows:
\RLEQNS{
  g &\in& G & \text{a label generator}
\\ \ell &\in& L & \text{labels}
\\ new &:& G \fun L \times G & \text{generating a new label}
\\ split &:& G \fun G \times G & \text{split one generator into two}
\\ labs &:& G \fun \power L & \text{set of labels produced by a generator}
}
We now have a more general notion of a concurrent program's view of the world,
which now has a generator static parameter $g$ in addition to $in$ and $out$
(See \figref{fig:par-prog:view}).
\begin{figure}[tb]
  \centering
\includegraphics{images/parallel-program.eps}
  \caption{Concurrent Program view of the world}
  \label{fig:par-prog:view}
\end{figure}


\begin{itemize}
  \item
     Function $new$ takes a generator and returns a new label $\ell$,
     and a new generator which itself will never produce $\ell$.
  \item
    Function $split$ takes a generator and splits it into two new generators
    that will produce disjoint sets of labels.
  \item
     Function $labs$ returns the infinite set of
     all the labels its generator argument will ever produce.
     \RLEQNS{
        labs(g) &=& \setof\ell \cup labs(g') \cup labs(g_1) \cup labs(g_2)
     \\ && \WHERE
     \\ && (\ell,g') = new(g)
     \\ && (g_1,g_2) = split(g)
     }
\end{itemize}
These functions obey the following laws:
\RLEQNS{
   new(g) = (\ell,g') &\implies& \ell \notin labs(g')
\\ split(g) = (g_1,g_2) &\implies& labs(g_1) \cap labs(g_2) = \emptyset
}
We often want to focus on either the first or second component
that results from $new$ or $split$:
\RLEQNS{
 f_i  &\defs& \pi_i \circ f
}

Coding the dictionary entries for generator $new_i$ and $split_i$.
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

To make calculation easier, we shall introduce the following shorthands,
along with a suggestive diagrammatic notation:
\RLEQNS{
\\ \ell_g &\defs& new_1(g)
\\ \g:    &\defs& new_2(g)
\\        &     &          & \includegraphics{images/new-label.eps}
\\ \g1    &\defs& split_1(g)
\\ \g2    &\defs& split_2(g)
\\        &     &          & \includegraphics{images/split-gen.eps}
}



\begin{code}
showGNew1   d [g] = 'l':edshow d g
showGNew2   d [g] = edshow d g ++ ":"
showGSplit1 d [g] = edshow d g ++ "1"
showGSplit2 d [g] = edshow d g ++ "2"
\end{code}
So the expression $\ell_{g1:2:}$ (\figref{fig:label-gen-xampl}) denotes
\RLEQNS{
   && \ell_{g1:2:}
\\&=& new_1(\g{1:2:})
\\&=& new_1(new_2(\g{1:2}))
\\&=& new_1(new_2(split_2(\g{1:})))
\\&=& new_1(new_2(split_2(new_2(\g{1})))
\\&=& new_1(new_2(split_2(new_2(split_1(g))))
\\&=& new_1((split_1 ; new_2 ; split_2 ; new_2 )(g))
}
\begin{figure}[h]
  \centering
\includegraphics{images/label-gen-example.eps}
  \caption{Label generation example: $\ell_{g1:2:}$}
  \label{fig:label-gen-xampl}
\end{figure}




Function $labs$ in the shorthand:
\RLEQNS{
   labs(g) &=& \setof{\ell_g} \cup labs(\g{:}) \cup labs(\g{1}) \cup labs(\g{2})
\\ \ell_g &\notin& labs(\g{:})
\\ \emptyset  &=& labs(\g{1}) \cap labs(\g{2})
}
$new$ and $split$ are functional,
so we have the following law:
\RLEQNS{
  \ell_{gexprA} = \ell_{gexprB}
  &\equiv&
  gexprA = gexrpB
}
We can now define a generator dictionary:
\begin{code}
genUTCPDict :: (Eq s, Ord s, Show s) => Dict s
genUTCPDict
 = makeDict
    [ (new1n,(ExprEntry True showGNew1 $ justMakes gNew1))
    , (new2n,(ExprEntry True showGNew2 $ justMakes gNew2))
    , (split1n,(ExprEntry True showGSplit1 $ justMakes gSplit1))
    , (split2n,(ExprEntry True showGSplit2 $ justMakes gSplit2))
    ]
\end{code}


\newpage
\HDRc{Sequential Composition Semantics}


For sequential composition we use the generator $g$ as follows:
\begin{enumerate}
  \item
    First, we use $new$ to get our label $\ell$,
    which we can now refer to as $\ell_g$.
    The new generator returned is described as $\g:$.
  \item
    We then split the new generator $\g:$ in two ($\g{:1}$ and $\g{:2}$)
    and give one each to the subcomponents
\end{enumerate}
In effect we introduce $g$ as a new static parameter,
and use substitutions to propagate it to sub-components,
as we did with $in$ and $out$ (\figref{fig:seq-actual:view}).

\begin{figure}[htb]
  \centering
\includegraphics{images/seq-comp-actual.eps}
  \caption{Sequential Composition actual construction}
  \label{fig:seq-actual:view}
\end{figure}



\RLEQNS{
    P \lseq Q &\defs& P[\g{:1},\ell_g/g,out] \lor Q[\g{:2},\ell_g/g,in]
}
\newpage
\begin{code}
nPSeq = "PSeq"
isPSeq (_,Comp n [_]) | n==nPSeq = True; isPSeq _ = False

pseq = comp nPSeq

shPSeq = ";;"
ppPSeq d ms p [mpr1,mpr2]
 = paren p precPSeq
     $ ppopen  (pad shPSeq) [ mshowp d ms precPSeq mpr1
                            , mshowp d ms precPSeq mpr2 ]
ppPSeq d ms p mprs = pps styleRed $ ppa ("invalid-"++shPSeq)

defnSeq d [p,q]
 = ldefn shPSeq $ mkOr [psub p sub1, psub q sub2]
 where
   sub1 = [("g",g'1),("out",lg)]
   sub2 = [("g",g'2),("in",lg)]

lg = new1 g
g' = new2 g
g'1 = split1 g'
g'2 = split2 g'

pseqEntry :: (Show s, Ord s) => (String, Entry s)
pseqEntry
 = ( nPSeq
   , PredEntry False ppPSeq [] defnSeq (pNoChg nPSeq) )
\end{code}


\newpage
\HDRc{Parallel Composition Semantics}

Initially, parallel composition appears easy:
simply split the generator and pass to each part,
but leave $in$ and $out$ alone:
\[
  P[\g1/g] \lor Q[\g2/g]
\]
However this does not work --- consider if $P$ is atomic and runs first:
the $in$ is removed from, and $out$ added to $ls$, effectively disabling $Q$.
Instead we need to seperate out the $in$ and $out$ labels of $P$ and $Q$,
and introduce two new atomic ``actions'': one to split $in$  into two new
start labels; and another to merge finish labels into $out$.
These split and merge actions do not alter state $s$.
We need to split the generator ($\g1,\g2$)
and generate two labels
(start: $\ell_{g1},\ell_{g2}$,
 finish: $\ell_{g1:},\ell_{g2:}$)
from each before passing them ($\g{1::},\g{2::}$) into $P$ and $Q$.

\begin{center}
\includegraphics{images/parallel-label-gen.eps}
\end{center}
\begin{code}
g1   = split1 g
lg1  = new1 g1  ; g1'  = new2 g1
lg1' = new1 g1' ; g1'' = new2 g1'

g2   = split2 g
lg2  = new1 g2  ; g2'  = new2 g2
lg2' = new1 g2' ; g2'' = new2 g2'
\end{code}

\RLEQNS{
   Split(\ell_a,\ell_b)
   &\defs&
         ls(in)
   \land s'=s
   \land ls'=ls\ominus(in,\setof{\ell_a,\ell_b})
\\ Merge(\ell_a,\ell_b)
   &\defs&
         ls(\ell_{g1:},\ell_{g2:})
   \land s'=s
   \land ls'=ls\ominus(\setof{\ell_a,\ell_b},out)
}

So, the parallel compostion is a disjunction between
$Split(\ell_{g1},\ell_{g2})$,
the two components with appropriate re-labelling,
and $Merge(\ell_{g1:},\ell_{g2:})$
(\figref{fig:par-actual:view}).
\begin{figure}[h]
  \centering
\includegraphics{images/par-comp-actual.eps}
  \caption{
     Parallel Composition actual construction (omitting generators).
     The $s$ box is dashed to emphasise its global nature,
     \emph{i.e.}, that it lies outside/under the program box
  }
  \label{fig:par-actual:view}
\end{figure}

\RLEQNS{
    P \parallel Q
    &\defs&
    ~~~~ ls(in) \land s'=s \land ls'=ls\ominus(in,\setof{\ell_{g1},\ell_{g2}})
\\&& {} \lor P[\g{1::},\ell_{g1},\ell_{g1:}/g,in,out]
\\&& {} \lor Q[\g{2::},\ell_{g2},\ell_{g2:}/g,in,out]
\\&& {} \lor ls(\ell_{g1:},\ell_{g2:}) \land s'=s \land ls'=ls\ominus(\setof{\ell_{g1:},\ell_{g2:}},out)
}
\begin{code}
nPPar = "PPar"
isPPar (_,Comp n [_]) | n==nPPar = True; isPPar _ = False

ppar = comp nPPar

shPPar = "||"
ppPPar d ms p [mpr1,mpr2]
 = paren p precPPar
     $ ppopen  (pad shPPar) [ mshowp d ms precPPar mpr1
                            , mshowp d ms precPPar mpr2 ]
ppPPar d ms p mprs = pps styleRed $ ppa ("invalid-"++shPPar)

defnPPar d [p,q]
 = ldefn shPPar $ mkOr [split, psub p sub1, psub q sub2, merge]
 where
   split = bAnd [ lsin
               , equal s' s
               , equal ls' (sswap ls inp $ mkSet [lg1,lg2]) ]
   sub1 = [("g",g1''),("in",lg1),("out",lg1')]
   sub2 = [("g",g2''),("in",lg2),("out",lg2')]
   merge = bAnd [ atm $ subset (mkSet [lg1',lg2']) ls
               , equal s' s
               , equal ls' (sswap ls (mkSet[lg1',lg2']) out) ]

pparEntry :: (Show s, Ord s) => (String, Entry s)
pparEntry
 = ( nPPar
   , PredEntry False ppPPar [] defnPPar (pNoChg nPPar) )
\end{code}

\newpage
\HDRc{Conditional Semantics}

For the conditional, as only one arm will run, we can share $out$,
but we need a split on $in$ that uses the condition $c$.
\RLEQNS{
   Cond(\ell_a,c,\ell_b)
   &\defs&
         ls(in)
   \land s'=s
   \land ls'=ls\ominus(in,\ell_a \cond c \ell_b)
}
So we split the generator ($\g1,\g2$) and produce one start label from each
($\ell_{g1},\ell_{g2}$), and then pass the two remaining generators
($\g{1:},\g{2:}$)
into $P$ and $Q$ as appropriate.
We then have a conditional-split ``action'' that
converts $in$ into $\ell_{g1}$ or $\ell_{g2}$ as determined by the condition
(\figref{fig:cond-actual:view}).
\begin{figure}[h]
  \centering
\includegraphics{images/conditional-actual.eps}
  \caption{Conditional actual construction (omitting generators)}
  \label{fig:cond-actual:view}
\end{figure}

\RLEQNS{
    P \lcond c Q
    &\defs&
    ~~~~ ls(in) \land s'=s \land ls'=ls\ominus(in,\ell_{g1} \cond c \ell_{g2})
\\&& {} \lor P[\g{1:},\ell_{g1}/g,in]
\\&& {} \lor Q[\g{2:},\ell_{g2}/g,in]
}
\begin{code}
nPCond = "PCond"
isPCond (_,Comp n [_]) | n==nPCond = True; isPCond _ = False

shPCondL = "<|" ; shPCondR = "|>" ;shPCond = shPCondL++shPCondR
ppPCond d ms p [mprt,mprc,mpre]
 = paren p precPCond
      $ pplist [ mshowp d ms precPCond mprt
               , ppa $ pad shPCondL
               , mshowp d ms 0 mprc
               , ppa $ pad shPCondR
               , mshowp d ms precPCond mpre ]
ppCCond d ms p mprs = pps styleRed $ ppa ("invalid-"++shPCond)


pcond = comp nPCond

defnPCond d [c,p,q]
 = ldefn shPCond $ mkOr [ cnd lg1 c,cnd lg2 $ bNot c
                        , psub p sub1, psub q sub2 ]
 where
   cnd ell c  = bAnd [ lsin
                    , equal s' s
                    , c
                    , equal ls' $ sswap ls inp ell ]
   sub1 = [("g",g1'),("in",lg1)]
   sub2 = [("g",g2'),("in",lg2)]

pcondEntry :: (Show s, Ord s) => (String, Entry s)
pcondEntry
 = ( nPCond
   , PredEntry False ppPCond [] defnPCond (pNoChg nPCond) )
\end{code}

\newpage
\HDRc{Iteration Semantics}

Iteration is quite simple,
as we view it as a conditional loop unrolling
(\figref{fig:iter-actual:view}).

\begin{figure}[h]
  \centering
\includegraphics{images/iteration-actual.eps}
  \caption{Iteration actual construction (omitting generators)}
  \label{fig:iter-actual:view}
\end{figure}


\RLEQNS{
   c \wdo P
   &\defs&
    ~~~~ ls(in) \land s'=s \land ls'=ls\ominus(in,\ell_{g} \cond c out)
\\&& {} \lor P[\g{:},\ell_{g},in/g,in,out]
}
\begin{code}
nPIter = "PIter"
isPIter (_,Comp n [_]) | n==nPIter = True; isPIter _ = False

piter = comp "PIter"

shPIter = "??"
ppPIter d ms p [mpr1,mpr2]
 = paren p precPIter
     $ ppopen  (pad shPIter) [ mshowp d ms precPIter mpr1
                             , mshowp d ms precPIter mpr2 ]
ppPIter d ms p mprs = pps styleRed $ ppa ("invalid-"++shPIter)

defnIter d [c,p]
 = ldefn shPIter $ mkOr [loop (bNot c) out, loop c lg, psub p sb]
 where
   loop c ell = bAnd [ lsin
                     , equal s' s
                     , c
                     , equal ls' $ sswap ls inp ell ]
   sb = [("g",g'),("in",lg),("out",inp)]

piterEntry :: (Show s, Ord s) => (String, Entry s)
piterEntry
 = ( nPIter
   , PredEntry False ppPIter [] defnAtomic (pNoChg nPIter) )
\end{code}



\HDRb{Running a concurrent program}

So far the semantics we have written simply views a concurrent program
as a big disjunction of atomic actions that use labels in a particular way.
This is a very static view of the program meaning.
To get a dynamic semantics we need to embed the above static
view, with appropriate initialisation,
into a loop that repeatedly runs the static disjunction
until a suitable (label-based) termination condition is reached.
We shall denote by $run(P)$ the result of adding dynamism
to a static view $P$ in this way.
\begin{code}
nPRun = "PRun"
isPRun (_,Comp n [_]) | n==nPRun = True; isPRun _ = False

run p = comp nPRun [p]

shPRun = "run"
ppPRun d ms p [mpr]
 = pplist [ ppa shPRun
          , ppbracket "(" (mshowp d ms 0 mpr) ")"]
ppPRun d ms p mprs = pps styleRed $ ppa ("invalid-"++shPRun)
\end{code}

We produce $run(P)$ by putting $P$ into a loop
which keeps running so long as $out$
is not in $ls$.

At the very top level, we initialise $ls$ to be $\setof{in}$.
Note that we cannot push this in as a substitution on $P$,
otherwise all that happens is that the first enabled action keeps running.

We capture this as the following definition of $run$,
which we also expand once:
\RLEQNS{
\lefteqn{run(P)}
\\ &\defs&
   (\lnot ls(out) * P)[in/ls]
\EQ{unroll loop body once, because $\lnot ls(out)[in/ls]$ is true}
\\&& P[in/ls] ; (\lnot ls(out) * P)
}
\begin{code}
defnRun 2 d [p]
 = idefn 2 shPRun $ mkSeq (psub p [("ls",inp)]) (runLoop p)
defnRun _ d [p]
 = idefn 1 shPRun $ mkPSub (runLoop p) [("ls",inp)]

idefn i str = ldefn (str++'(':show i++")")

runLoop p  = bIter (bNot $ atm $ subset (mkSet [out]) ls) p

prunEntry :: (Show s, Ord s) => Int -> (String, Entry s)
prunEntry n
 = ( nPRun
   , PredEntry False ppPRun [] (defnRun n) (pNoChg nPRun) )
\end{code}


An extension to $run$, called $do$ explicitly mentions the fact
that $ls$ is initialised appropriately.
\RLEQNS{
    do(P) &\defs& ls=\setof{in} \land run(P)
}
\begin{code}
nPDo = "PDo"
isPDo (_,Comp n [_]) | n==nPDo = True; isPDo _ = False

doprog p = comp nPDo [p] 

shPDo = "do"
ppPDo d ms p [mpr]
 = pplist [ ppa shPDo
          , ppbracket "(" (mshowp d ms 0 mpr) ")"]
ppPDo d ms p mprs = pps styleRed $ ppa ("invalid-"++shPDo)


defnDo d [p]
 = ldefn shPDo $ mkAnd [ equal ls inp, run p ]

pdoEntry :: (Show s, Ord s) => (String, Entry s)
pdoEntry
 = ( nPDo
   , PredEntry False ppPDo [] defnDo (pNoChg nPDo) )
\end{code}


\newpage
\HDRb{Semantics Summary}

We assume atomic change-state actions $A$ with alphabet $\setof{s,s'}$.
\RLEQNS{
    \A(A) &\defs& ls(in) \land A \land ls'=ls\ominus(in,out),
    \qquad \alpha A = \setof{s,s'}
\\
\\  P \lseq Q &\defs& P[\g{:1},\ell_g/g,out] \lor Q[\g{:2},\ell_g/g,in]
\\
\\  P \parallel Q
    &\defs&
    ~~~~ ls(in) \land s'=s \land ls'=ls\ominus(in,\setof{\ell_{g1},\ell_{g2}})
\\&& {} \lor ls(\ell_{g1:},\ell_{g2:}) \land s'=s \land ls'=ls\ominus(\setof{\ell_{g1:},\ell_{g2:}},out)
\\&& {} \lor P[\g{1::},\ell_{g1},\ell_{g1:}/g,in,out]
\\&& {} \lor Q[\g{2::},\ell_{g2},\ell_{g2:}/g,in,out]
\\  P \lcond c Q
    &\defs&
    ~~~~ ls(in) \land s'=s \land ls'=ls\ominus(in,\ell_{g1} \cond c \ell_{g2})
\\&& {} \lor P[\g{1:},\ell_{g1}/g,in]
\\&& {} \lor Q[\g{2:},\ell_{g2}/g,in]
\\
\\  c \wdo P
   &\defs&
    ~~~~ ls(in) \land s'=s \land ls'=ls\ominus(in,\ell_{g} \cond c out)
\\&& {} \lor P[\g{:},\ell_{g},in/g,in,out]
\\
\\run(P)
   &\defs&
   (\lnot ls(\ell_{g:}) * P[\g{::},\ell_{g},\ell_{g:}/g,in,out])[\ell_g/ls]
\\ &=&
   P[\g{::},\ell_{g},\ell_{g:}/g,in,out][\ell_g/ls]
   ;
   (\lnot ls(\ell_{g:}) * P[\g{::},\ell_{g},\ell_{g:}/g,in,out])
\\ &=&
   P[\g{::},\ell_{g},\ell_{g:},\ell_g/g,in,out,ls]
   ;
   (\lnot ls(\ell_{g:}) * P[\g{::},\ell_{g},\ell_{g:}/g,in,out])
\\
\\ do(P) &\defs& in=\ell_g \land out=\ell_{g:} \land ls=\ell_g \land run(P)
}
\begin{code}
semUTCPDict :: (Ord s, Show s) => Dict s
semUTCPDict
 = makeDict
    [ patmEntry
    , pidleEntry
    , pseqEntry
    , pparEntry
    , pcondEntry
    , piterEntry
    , prunEntry 2
    , pdoEntry
    ]
\end{code}
