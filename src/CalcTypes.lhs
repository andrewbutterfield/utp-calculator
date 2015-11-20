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

\HDRb{Dictionary}\label{hb:DataDict}

We need a dictionary that maps various names
to appropriate definitions.
\begin{code}
type Dict m s = M.Map String (Entry m s)
\end{code}

A dictionary entry is a sum of  definition types defined below
\begin{code}
data Entry m s
 = PredEntry (PredDef m s)
 | ExprEntry (ExprDef m s)
 | AlfEntry AlfDef
 | PVarEntry PVarDef
\end{code}

Predicate definitions
\begin{code}
data PredDef m s
 = PD [String]                -- list of formal/bound variables
      (Pred m s)              -- definition body
      (Dict m s -> Int -> [MPred m s] -> PP)    -- pretty printer
      (Dict m s -> [MPred m s] -> ( String      -- eval name
                                 , Pred m s )) -- evaluator
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"P" |->  PredEntry (PD  ["Q1","Q2",...,"Qn"] pr pf pv)
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

Expression definitions
\begin{code}
data ExprDef m s
 = ED [String]                -- list of formal/bound variables
      (Expr s)                 -- definition body
      (Dict m s -> [Expr s] -> String)     -- pretty printer
      (Dict m s -> [Expr s] -> ( String   -- eval name
                             , Expr s )) -- evaluator
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"f" |->  ExprEntry (ED ["v1","v2",...,"vn"] e pf ev)
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

We also want to define alphabets, as sets of names
\begin{code}
type AlfDef = [String]
\end{code}
An entry
\begin{verbatim}
"a" |-> AlfEntry ["v1","v2",..,"vn"]
\end{verbatim}
defines an alphabet:
\RLEQNS{
  a &\defs& \setof{v_1,v_2,\ldots,v_n}
}
We sometimes want to associate extra information with given
predicate variables:
\begin{code}
type PVarDef = [String] -- for now, just its alphabet
\end{code}
An entry
\begin{verbatim}
  "P" |-> PVarEntry ["v1","v2",..,"vn"]
\end{verbatim}
declares the alphabet associated with that predicate variable:
\RLEQNS{
   \alpha P &=&  \setof{v_1,v_2,\ldots,v_n}
}
