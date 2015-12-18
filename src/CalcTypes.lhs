\HDRa{Calculator Types}\label{ha:calc-types}
\begin{code}
module CalcTypes where
import qualified Data.Map as M
import PrettyPrint
\end{code}

\HDRb{Syntax}

First, we build some infrastructure to support a flexible expression and predicate
syntax, with an emphasis on allowing tailored notations
(e.g. writing $ps(in)$ and $ps(in,out)$
rather than $in \in ps$ or $\setof{in,out} \subseteq ps$),
effective pretty-printing of large complex nested terms,
and highlighting sub-terms of interest.

\HDRc{Expression Datatype}\label{hc:ExprData}

We start by defining an expression space that includes
booleans, integers,
variables, function applications, and substitutions.
\RLEQNS{
   s &\in& State  & \mbox{States}
\\ v &\in& Var & \mbox{Variables}
\\ e \in Expr &::=& s | \Bool | \Int | v & \mbox{Basic}
\\  &|& v(e_1,\ldots,e_n) & \mbox{Application}
\\ &|& e[e_1,\ldots,e_n/v_1,\ldots,v_n] & \mbox{Substitution}
}
This type $E$ is parametric in a generic state type:
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
\end{code}
We treat expressions as atomic from the perspective of
pretty-printing and highlighting.


\newpage
\HDRc{Predicate Datatype}\label{hc:PredData}

Now we need a  predicate syntax,
which has basic predicates
(true, false, predicate-variables, equality and lifted expressions)
along with a generic predicate composite, and substitution.
\BASIC

To implement suitable highlighting,
we need the calculator to be able to mark (sub-)predicates in some
way, with markings that can overlap.
We don't want to check for or pattern-match against
a special marker predicate, but prefer to add markers everywhere,
using a mutually recursive datatype:
\begin{code}
type MPred m s = ( [m], Pred m s )

data Pred m s
 = T
 | F
 | PVar String
 | Equal (Expr s) (Expr s)
 | Atm (Expr s)
 | Comp String [MPred m s]
 | PSub (MPred m s) (Substn s)
 | PUndef
 deriving (Ord, Show)
\end{code}

Predicate equality is defined on the underlying predicate,
so that it ignores marking completely.
\begin{code}
instance Eq s => Eq (Pred m s) where
 T == T                              =  True
 F == F                              =  True
 (PVar s1) == (PVar s2)              =  s1 == s2
 (Equal e11 e12) == (Equal e21 e22)  =  e11 == e21 && e12 == e22
 (Atm e1) == (Atm e2)                =  e1 == e2
 (Comp f1 prs1) == (Comp f2 prs2)
    =  f1 == f2 && map snd prs1 == map snd prs2
 (PSub (_, pr1) subs1) == (PSub (_, pr2) subs2)
    =  pr1 == pr2 && subs1 == subs2
 _ == _                              =  False
\end{code}

\HDRb{Marking Class}\label{hb:MarkClass}

We use a class for marks that specifies a special `starting' mark value,
as well as a way to generate a new label from an existing one,
and to reverse back.
\begin{code}
class Mark m where
  startm :: m
  nextm :: m -> m -- laws for nextm:
                  --    (i)  nextm m /= m
                  --   (ii)  nextm m /= startm
                  --  (iii)  nextm is bijective
  prevm :: m -> m -- laws for prevm
                  --    (i) prevm . nextm = id
\end{code}

We need a function from markings to styles:
\begin{code}
type MarkStyle m = m -> Maybe Style

noStyles :: MarkStyle m
noStyles = const Nothing
\end{code}


\newpage
\HDRb{Calculation Steps}\label{hb:calc-steps}

We now present the infrastructure for performing calculations.
There are a number of different kinds of calculation step,
described in a little more detail later.
The basic idea is that such a step rewrites a current goal
predicate in some way, and returns both the rewritten result,
as well as a justification string describing what was done.
\begin{code}
type RWResult m s = (String, MPred m s)
type RWFun m s = MPred m s -> RWResult m s
\end{code}

We also have steps that are contingent on some side-condition,
but we don't want to implement a fully automated solver for these conditions,
nor do we want to have to break-out into a sub-calculation.
These steps typically occur in pairs,
giving different results based on the truth of the condition.
So we design a ``step'' that returns the alternative rewrite outcomes,
along with a clear statement of the condition,
and allows the user to select which one should be used.
\begin{code}
type CRWResult m s
 = ( String
   , [( Pred m s    -- condition to be discharged
      , MPred m s)]  -- modified predicate
   )
type CRWFun m s = MPred m s -> CRWResult m s
\end{code}




\newpage
\HDRb{Dictionary}\label{hb:DataDict}

We need a dictionary that maps various names
to appropriate definitions.
\begin{code}
type Dict m s = M.Map String (Entry m s)
\end{code}

When processing a composite,
we will use the composite name to lookup a function
to do a rewrite.
This function will be passed the dictionary,
and the list of sub-components for it to do its work,
and will return a justification string and un-marked predicate:
\begin{code}
type Rewrite m s = Dict m s -> [MPred m s] -> (String, Pred m s)
\end{code}


A dictionary entry is a sum of  definition types defined below
\begin{code}
data Entry m s =
\end{code}

\HDRc{Alphabet Entry}\label{hc:alfa-entry}

\begin{code}
-- data Entry m s = ....
   AlfEntry {   -- about Alphabets
    avars :: [String]  -- variables
   }
\end{code}
An entry
\texttt{"A" |-> AlfEntry ["v1","v2",..,"vn"]}
\\defines an alphabet:
$A \defs \setof{v_1,v_2,\ldots,v_n}$.

\HDRc{Predicate Variable Entry}\label{hc:pvar-entry}

\begin{code}
-- data Entry m s = ....
 | PVarEntry {  -- about Predicate Variables
    alfa :: [String]  -- for now, just its alphabet
   }
\end{code}
An entry \texttt{"P" |-> PVarEntry ["v1","v2",..,"vn"]}
\\
declares the alphabet associated with that predicate variable:
$\alpha P \defs \setof{v_1,v_2,\ldots,v_n}$.

\HDRc{Expression Entry}\label{hc:expr-entry}

\begin{code}
-- data Entry m s = ....
 | ExprEntry { -- about Expressions
     ebvars  :: [String]                       -- bound variables
   , ebody   ::  Expr s                        -- definition body
   , ecansub :: Bool                           -- substitutable?
   , eprint  :: Dict m s -> [Expr s] -> String -- pretty printer
   , eval    :: Dict m s -> [Expr s]           -- evaluator
             -> ( String, Expr s )
   }
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"f" |->  ExprEntry ["v1","v2",...,"vn"] e ss pf ev
\end{verbatim}
as defining a function:
\RLEQNS{
   f(v_1,v_2,\ldots,v_n) &\defs& e
}
where $ss$ indicates its substitutability,
and with $pf_\delta(e_1,e_2,\ldots,e_n)$ being a specialised print function
that renders a function call as required,
and $ev_\delta(e_1,e_2,\ldots,e_n)$ is an evaluation function that
attempts to evaluate the call.
Both are parameterised with a dictionary argument ($\delta$),
which may, or may not, be the dictionary in which the entry occurs.
The string in the result is empty if it failed,
otherwise gives the name of the function to be used in the justification
of a proof step.
The evaluator is free to use or ignore the definition body expression $e$.

\HDRc{Predicate Entry}\label{hc:pred-entry}

\begin{code}
 | PredEntry {    -- about Predicates
     pbvars  :: [String]                       -- bound vars
   , pbody   :: Pred m s                       -- defn. body
   , pcansub :: Bool                           -- substitutable?
   , pprint  :: Dict m s -> MarkStyle m        -- pretty printer
             -> Int -> [MPred m s]
             -> PP
   , pdefn   :: Rewrite m s                    -- defn expansion
   , prsimp  :: Rewrite m s                    -- simplifier
   }
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"P" |->  PredEntry ["Q1","Q2",...,"Qn"] pr ss pp pd ps
\end{verbatim}
as defining a function:
\RLEQNS{
   P(Q_1,Q_2,\ldots,Q_n) &\defs& pr
}
and $ss$ is a boolean that is true if the predicate application
is substitutable%
\footnote{%
The LHS of a predicate definition is substitutable iff
$P(Q_1\sigma,\ldots,Q_n\sigma) = pr\sigma$ for any substitution $\sigma$.
}%
,
with $pp_\delta(Q_1,Q_2,\ldots,Q_n)$ being a specialised print function
that renders a predicate as required,
$pd$ is a function that expands the definition of $P$
(which may differ from $pr$),
and $ps_\delta(Q_1,Q_2,\ldots,Q_n)$ is a function that
attempts to simplify the predicate.
\textbf{WARNING: }
\textit{the \texttt{prsimp} function above
 must not call \texttt{simplify} (\secref{hc:simplify})!
To do so risks an infinite loop.
}

All are parameterised with a dictionary argument ($\delta$),
which may, or may not, be the dictionary in which the entry occurs.
The string in the result is empty if it failed,
otherwise gives the name of the predicate to be used in the justification
of a proof step.
The definition expansion is free to use or ignore the definition body expression $pr$.


\HDRcstar{Entry Complete}

\begin{code}
-- end Entry
\end{code}

\HDRb{Calculation Steps}\label{hb:calc-types}

\HDRc{Calculation Step Intro}\label{hc:step-intro}

Imagine an predicate $p$ containing sub-predicates $q_1$, $q_2$ and $q_3$,
to which we apply $step$ three times,
which results in the following changes:
\[
  step_i : q_i \mapsto q'_i, \qquad i \in 1\ldots 3
\]
The presentation of the calculation should look like the following,
where underlining denotes ``old'' and the colour red denotes ``new'':
\RLEQNS{
\\ && p
\EQ{defn of $p$ (w.l.o.g.)}
\\&& ( \ldots \OLD{q_1} \ldots q_2 \ldots q_3 \ldots)
\EQm{step_1}
\\&& ( \ldots \NEW{q'_1} \ldots \OLD{q_2} \ldots q_3 \ldots)
\EQm{step_2}
\\&& ( \ldots q'_1 \ldots \NEW{q'_2} \ldots \OLD{q_3} \ldots)
\EQm{step_3}
\\&& ( \ldots q'_1 \ldots q'_2 \ldots \NEW{q'_3} \ldots)
}
Notice how each $step_i$ affects the Old/New marking of both its predecessor
and successor predicates.
Rather than having two markings (Old/New) it turns out to be more efficient
to have a numeric marking, so $step_i$ introduces mark number $i$.
The interpetation of such marks as old, new or irrelevant can then be done
relative to the numbering of the step outcome being rendered for display.

We can breakdown the above calculation using mark numbers ($M_i$) as follows
\RLEQNS{
   p  && ( \ldots q_1 \ldots q_2 \ldots q_3 \ldots)
\EQm{step_1}
\\ pe_1 && ( \ldots \OLD{M_1(q_1)} \ldots q_2 \ldots q_3 \ldots) & \mbox{display 1=Old}
\\
\\ ne_1 && ( \ldots M_1(q'_1) \ldots q_2 \ldots q_3 \ldots)
\EQm{step_2}
\\ pe_2 && ( \ldots \NEW{M_1(q'_1)} \ldots \OLD{M_2(q_2)} \ldots q_3 \ldots) & \mbox{display 1=New, 2=Old}
\\
\\ ne_2 && ( \ldots M_1(q'_1) \ldots M_2(q'_2) \ldots q_3 \ldots)
\EQm{step_3}
\\ pe_3 && ( \ldots M_1(q'_1) \ldots \NEW{M_2(q'_2)} \ldots \OLD{M_3(q_3)} \ldots) & \mbox{display 2=New, 3=Old}
\\
\\ ne_3 && ( \ldots M_1(q'_1) \ldots M_2(q'_2) \ldots \NEW{M_3(q'_3)} \ldots) & \mbox{display 3=New}
}

So we see that $step_i$ takes $ne_{i-1}$ and produces:
\begin{itemize}
  \item $pe_i$, where $M_i$ has been wrapped around $q_i$
  \item $ne_i$, which is $pe_i$, where $q_i$ (already marked with $M_i$)
   is replaced by $q'_i$.
\end{itemize}
What is not obvious from the above example is what should happen
when two successive steps affect the same or a nested sub-predicate.
Here we find we need to be able to associate multiple marks with
any sub-component.

\HDRc{Calculation Step Types}\label{hc:step-types}

In order to mark and highlight predicates in calculation steps,
we need to return not just the modified result, marked at the point of change,
but also the original predicate, also marked at the same location
(with the same mark in each case --- the mark identifies the specific
calculation step).
We have a type that has this information,
along with a justification string:
\begin{code}
type BeforeAfter m s
 = ( MPred m s   -- before predicate, marked
   , String      -- justification, null if no change occurred
   , MPred m s ) -- after predicate, marked
\end{code}
In the conditional case, we have lists of outcomes
paired with conditions:
\begin{code}
type BeforeAfters m s
 = ( MPred m s   -- before predicate, marked
   , String      -- justification, null if no change occurred
   , [(Pred m s,MPred m s)] ) -- after predicates, marked
\end{code}

This seems to present a problem for the zipper,
as we have to identify corresponding locations,
where $q_i$ and $q'_i$ reside,
in two different versions of a single predicate.
However the structure of the two predicates is identical everywhere else
so a single zipper ``path'' can be applied to both.

\begin{code}
type MPZip2 m s = (BeforeAfter m s, [MPred' m s])
\end{code}

For conditional searches,
we return a list of \texttt{Pred},\texttt{MPred} pairs:
\begin{code}
type CMPZip2 m s = ( BeforeAfters m s, [MPred' m s] )
\end{code}

\newpage
\HDRb{Zipper Datatypes}\label{hb:zipper-types}

We note, using the notion of ``datatypes as algebras'',
%( http://chris-taylor.github.io/blog/2013/02/13/the-algebra-of-algebraic-data-types-part-iii/)
that the \texttt{Pred m s} and \texttt{MPred m s} types above
correspond to the following algebraic forms:
\RLEQNS{
   V && & \mbox{Variables}
\\ E && & \mbox{Expressions}
\\ M && & \mbox{Marks}
\\ P_M &=& \mathbf 1
         + \mathbf 1
         + \Char^*
         + E \times E
         + E
\\    && + \Char^* \times MP_M^*
         + MP_M \times (V \times E)^* & \mbox{Predicates}
\\ MP_M &=& M^* \times P_M & \mbox{Marked Predicates}
\\      &=& M^* \times \mathbf 1
          + M^* \times \mathbf 1
          + M^* \times \Char^*
          + M^* \times E \times E
          + M^* \times E
\\     && + M^* \times \Char^* \times MP_M^*
          + M^* \times MP_M \times (V \times E)^*
\\      &=& F(MP_M)
}
We want to define a ``zipper'' \cite{JFP::Huet1997} for \texttt{MPred m s},
following Conor McBride's Datatype Differentiation approach\cite{McB:derrti}.
So, we ``differentiate'' the expression for $MP_M$ above w.r.t. $MP_M$,
to obtain $MP'_M$:
\RLEQNS{
   MP'_M &=& \partial_{MP_M}(F)
\\       &=& M^* \times \Char^* \times (MP_M^*)^2
           + M^* \times (V \times E)^*
}
We use the following differentiation laws:
\RLEQNS{
   d(x^n)/dx &=& nx^{n-1}
\\ d(x^*)/dx
   &=& d(1+x+x^2+x^3+\cdots)/dx
\\ &=& (1+2x+3x^2+4x^3+\cdots)
\\ &=& (1+x+x^2+x^3+\cdots)^2 & \mbox{exercise: show this}
\\ &=& (x^*)^2
\\ d(kf)/dx &=& k(df/fx) & k\mbox{ a constant}
}
This leads to the following zipper datatypes:
\begin{code}
data MPred' m s
 = Comp'         -- parent is a Comp node
     [m]         -- parent marking
     String      -- parent name
     [MPred m s] -- components before current focus
     [MPred m s] -- components after current focus
 | PSub'         -- parent is a PSub node
     [m]         -- parent marking
     (Substn s)  -- substitution in parent
 deriving Show
\end{code}
We then define a zipper as being an predicate
together with a list of predicate derivatives:
\begin{code}
type MPZipper m s
  = ( MPred m s    -- the current (focus) predicate
    , [MPred' m s] -- the steps we took to get here,
                   -- and what we passed on the way.
    )
\end{code}

\HDRb{Recognisers}\label{hc:recog}

\begin{code}
type Recogniser m s = MPred m s -> Bool
\end{code}

\HDRb{Theory Steps}

%\begin{code}
%data ThSteps m s
% = TS{
%\end{code}
%    \begin{description}
%      \item[Reduce]
%        Apply a law of predicate calculus in a direction that ``makes progress''.
%\begin{code}
%   reduce :: Dict m s -> RWFun m s
%\end{code}
%      \item[Definition]
%        Expand a definition
%\begin{code}
% , defn :: RWFun m s
%\end{code}
%      \item[Conditional]
%        Apply a conditional law, also in a direction that makes progress.
%\begin{code}
% , creduce :: Dict m s -> CRWFun m s
%\end{code}
%    \end{description}
%\begin{code}
%}
%\end{code}
