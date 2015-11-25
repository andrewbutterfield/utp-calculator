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

We don't want to check for or pattern-match against
a special marker predicate, but prefer to add markers everywhere,
using a mutually recursive datatype:
\begin{code}
type MPred m s = ( m, Pred m s )

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

instance Eq s => Eq (Pred m s) where -- ignore values of type m
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

\newpage
\HDRb{Calculation Steps}\label{hb:calc-steps}

We now present the infrastructure for performing calculations.
There are a number of different kinds of calculation step,
described in a little more detail later.
The basic idea is that such a step transforms a current goal
predicate in some way, and returns both the transformed result,
as well as a justification string describing what was done.
\begin{code}
type CalcResult m s = (String, Pred m s)
type CalcStep m s = Pred m s -> CalcResult m s
\end{code}

We also have steps that are contingent on some side-condition,
but we don't want to implement a fully automated solver for these conditions,
nor do we want to have to break-out into a sub-calculation.
These steps typically occur in pairs,
giving different results based on the truth of the condition.
So we design a ``step'' that returns the alternative outcomes,
along with a clear statement of the condition,
and allows the user to select which one should be used.
\begin{code}
type CCalcResult m s
 = ( String
   , [( Pred m s    -- condition to be discharged
      , Pred m s)]  -- modified predicate
   )
type CCalcStep m s = Pred m s -> CCalcResult m s
\end{code}


\newpage
\HDRb{Dictionary}\label{hb:DataDict}

We need a dictionary that maps various names
to appropriate definitions.
\begin{code}
type Dict m s = M.Map String (Entry m s)
\end{code}

A dictionary entry is a sum of  definition types defined below
\begin{code}
data Entry m s =
\end{code}

\HDRc{Alphabet Entry}\label{hc:alfa-entry}

\begin{code}
-- data Entry m s = ....
   AlfEntry   -- about Alphabets
    [String]  -- variables
\end{code}
An entry
\texttt{"A" |-> AlfEntry ["v1","v2",..,"vn"]}
\\defines an alphabet:
$A \defs \setof{v_1,v_2,\ldots,v_n}$.

\HDRc{Predicate Variable Entry}\label{hc:pvar-entry}

\begin{code}
-- data Entry m s = ....
 | PVarEntry  -- about Predicate Variables
    [String]  -- for now, just its alphabet
\end{code}
An entry \texttt{"P" |-> PVarEntry ["v1","v2",..,"vn"]}
\\
declares the alphabet associated with that predicate variable:
$\alpha P \defs \setof{v_1,v_2,\ldots,v_n}$.

\HDRc{Predicate Entry}\label{hc:pred-entry}

\begin{code}
 | PredEntry    -- about Predicates
    [String]    -- list of formal/bound variables
    (Pred m s)  -- definition body
    (Dict m s -> Int -> [MPred m s] -> PP)      -- pretty printer
    (Dict m s -> [MPred m s] -> CalcResult m s) -- evaluator
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"P" |->  PredEntry ["Q1","Q2",...,"Qn"] pr pf pv
\end{verbatim}
as defining a function:
\RLEQNS{
   P(Q_1,Q_2,\ldots,Q_n) &\defs& pr
}
with $pf_\delta(Q_1,Q_2,\ldots,Q_n)$ being a specialised print function
that renders a predicate as required,
and $pv_\delta(Q_1,Q_2,\ldots,Q_n)$ is an valuation function that
attempts to simplify the predicate..
Both are parameterised with a dictionary argument ($\delta$),
which may, or may not, be the dictionary in which the entry occurs.
The string in the result is empty if it failed,
otherwise gives the name of the predicate to be used in the justification
of a proof step.
The evaluator is free to use or ignore the definition body expression $pr$.

\HDRc{Expression Entry}\label{hc:expr-entry}

\begin{code}
-- data Entry m s = ....
 | ExprEntry  -- about Expressions
    [String]  -- list of formal/bound variables
    (Expr s)  -- definition body
    (Dict m s -> [Expr s] -> String)      -- pretty printer
    (Dict m s -> [Expr s] -> ( String     -- eval name
                             , Expr s ))  -- evaluator
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"f" |->  ExprEntry ["v1","v2",...,"vn"] e pf ev
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


\HDRcstar{Entry Complete}

\begin{code}
-- end Entry
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
\\ MP_M &=& M \times P_M & \mbox{Marked Predicates}
\\      &=& M \times \mathbf 1
          + M \times \mathbf 1
          + M \times \Char^*
          + M \times E \times E
          + M \times E
\\     && + M \times \Char^* \times MP_M^*
          + M \times MP_M \times (V \times E)^*
\\      &=& F(MP_M)
}
We want to define a ``zipper'' \cite{JFP::Huet1997} for \texttt{MPred m s},
following Conor McBride's Datatype Differentiation approach\cite{McB:derrti}.
So, we ``differentiate'' the expression for $MP_M$ above w.r.t. $MP_M$,
to obtain $MP'_M$:
\RLEQNS{
   MP'_M &=& \partial_{MP_M}(F)
\\       &=& M \times \Char^* \times (MP_M^*)^2
           + M \times (V \times E)^*
}
This leads to the following zipper datatypes:
\begin{code}
data MPred' m s
 = Comp'         -- parent is a Comp node
     m           -- parent marking
     String      -- parent name
     [MPred m s] -- components before current focus
     [MPred m s] -- components after current focus
 | PSub'         -- parent is a PSub node
     m           -- parent marking
     (Substn s)  -- substitution in parent
 deriving Show
\end{code}
We then define a zipper as being an predicate
together with a list of expression derivatives:
\begin{code}
type MPZipper m s
  = ( MPred m s    -- the current (focus) predicate
    , [MPred' m s] -- the steps we took to get here,
                   -- and what we passed on the way.
    )
\end{code}
