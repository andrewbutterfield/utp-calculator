\HDRa{Calculator Types}\label{ha:calc-types}
\begin{code}
module CalcTypes where
import qualified Data.Map as M
import PrettyPrint
\end{code}

Here we give the user-facing types,
namely those a user needs to know,
in order to setup calculator dictionaries,
invoke the calculator,
and explore the resulting calculations.


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
We shall do this by using integers as markers,
and marking predicates with a marker-set.
We don't want to check for or pattern-match against
a special marker predicate, but prefer to add markers everywhere,
using a mutually recursive datatype.

Under the hood, a top-level predicate is marked,
but all user-supplied code will focus and pattern-match
on predicates,
with a few support functions to hide the details of marking.
We represent ``matchable'' predicates using the \texttt{Pred} datatype:
\begin{code}
data Pred s
 = T
 | F
 | PVar String
 | Equal (Expr s) (Expr s)
 | Atm (Expr s)
 | Comp String [Pred s]
 | PSub (Pred s) (Substn s)
 deriving (Eq, Ord, Show)
\end{code}


\newpage
\HDRb{Calculation Steps}\label{hb:calc-steps}

We now present the infrastructure for performing calculations.
There are a number of different kinds of calculation step,
described in a little more detail later.
The basic idea is that such a step rewrites a current goal
predicate in some way, and returns both the rewritten result,
as well as a justification string describing what was done.
Also returned is a boolean flag that indicates
if it was the top-level predicate that was modified,
rather than one of its sub-components.
\begin{code}
type RWResult s
 = Maybe ( String  -- rewrite justification
         , Pred s  -- result predicate
         , Bool )  -- True if top-level modified
type RWFun s = Dict s -> Pred s -> RWResult s
\end{code}

For convenience we give boolean values indicating if something
changes (\texttt{diff}erent) or has stayed the \texttt{same}.
\begin{code}
diff, same :: Bool; diff = True; same = False
\end{code}


We also have steps that are contingent on some side-condition,
but we don't want to implement a fully automated solver for these conditions,
nor do we want to have to break-out into a sub-calculation.
These steps typically occur in pairs,
giving different results based on the truth of the condition.
So we design a ``step'' that returns the alternative rewrite outcomes,
along with a clear statement of the corresponding side-conditions.
This allows the user to select which one should be used.
\begin{code}
type CRWResult s
 = Maybe ( String      -- justification
         , [( Pred s   -- side-condition to be discharged
            , Pred s   -- modified predicate
            , Bool)])  -- True if top-level modified
type CRWFun s = Dict s -> Pred s -> CRWResult s
\end{code}
The justification string used in the calculator will be the one returned
here along with a rendering of the chosen side-condition.




\newpage
\HDRb{Dictionary}\label{hb:DataDict}

We need a dictionary that maps various names
to appropriate definitions.
\begin{code}
type Dict s = M.Map String (Entry s)
\end{code}

When processing a composite,
we will use the composite name to lookup a function
to do a rewrite.
This function will be passed the dictionary,
and the list of sub-components for it to do its work,
and will return a justification string and un-marked predicate:
\begin{code}
type Rewrite s = Dict s -> [Pred s] -> RWResult s
\end{code}


For pretty printing we will need to call a specific system-supplied
function with the following type:
\begin{code}
type SubCompPrint s
 = Int       -- precedence level for sub-component
   -> Int    -- sub-component number
   -> Pred s -- sub-component
   -> PP
\end{code}


A dictionary entry is a sum of  definition types defined below
\begin{code}
data Entry s =
\end{code}

\HDRc{Alphabet Entry}\label{hc:alfa-entry}

\begin{code}
-- data Entry s = ....
   AlfEntry {   -- about Alphabets
    avars   :: [String]  -- alphabet
   }
\end{code}
An entry
\texttt{"A" |-> AlfEntry ["v1","v2",..,"vn"]}
\\defines an alphabet:
$A \defs \setof{v_1,v_2,\ldots,v_n}$.

\newpage
\HDRc{Expression Entry}\label{hc:expr-entry}

\begin{code}
-- data Entry s = ....
 | ExprEntry { -- about Expressions
     ecansub :: [String]                   -- substitutable vars
   , eprint  :: Dict s -> [Expr s] -> String   -- pretty printer
   , eval    :: Dict s -> [Expr s]                  -- evaluator
             -> ( String -- empty if no change, else explanation
                , Expr s )
   , isEqual :: Dict s -> [Expr s] -> [Expr s] -> Maybe Bool
   }
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"f" |->  ExprEntry ss pf ev
\end{verbatim}
as defining a function:
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

\HDRc{Predicate Entry}\label{hc:pred-entry}

\begin{code}
 | PredEntry {    -- about Predicates and PredVars
     pcansub :: [String]                   -- substitutable vars
   , pprint  :: SubCompPrint s                 -- pretty-printer
             -> Dict s -> Int -> [Pred s]
             -> PP
   , alfa :: [String]                      -- predicate alphabet
   , pdefn   :: Rewrite s                      -- defn expansion
   , prsimp  :: Rewrite s                          -- simplifier
   }
\end{code}
We interpret a \texttt{Dict} entry like
\begin{verbatim}
"P" |->  PredEntry ss pp af pd ps
\end{verbatim}
as defining a composite,
where: $ss$ is a boolean that is true if the predicate application
is substitutable%
\footnote{%
The LHS of a predicate definition is substitutable iff
$P(Q_1\sigma,\ldots,Q_n\sigma) = pr\sigma$ for any substitution $\sigma$.
}%
;
$af$ gives the alphabet, if non-empty;
 $pp_\delta(Q_1,Q_2,\ldots,Q_n)$ is a specialised print function
that renders a predicate as required;
$pd$ is a function that expands the definition of $P$;
and $ps_\delta(Q_1,Q_2,\ldots,Q_n)$ is a function that
attempts to simplify the predicate.

All are parameterised with a dictionary argument ($\delta$),
which may, or may not, be the dictionary in which the entry occurs.
The string in the result is empty if it failed,
otherwise gives the name of the predicate to be used in the justification
of a proof step.

\textbf{WARNING: }
\textit{the \texttt{prsimp} function above
 must not call \texttt{simplify} (\secref{hc:simplify})!
To do so risks an infinite loop.
}

\newpage
\HDRc{Law Entry}\label{hc:law-entry}

\begin{code}
 | LawEntry {  -- about useful laws
     reduce  :: [RWFun s]            -- reduction laws
   , creduce :: [CRWFun s]           -- conditional reductions
   , unroll  :: [String -> RWFun s]  -- loop unrollers
   }
\end{code}
We interpret a \texttt{Dict} entry like:
\begin{verbatim}
"laws" |->  LawEntry [r1,....,rm] [cr1,...,crn] [u1,..,up]
\end{verbatim}
as describing the law/reduction steps to be tried
if the \verb"reduce",\verb"creduce" or \verb"unroll" commands
are invoked in the calculator.
The reduction steps are tried in order, from \m{r_1} to \m{r_m},
or \m{cr_1} to \m{cr_n} or \m{u_1} to \m{u_p}, as appropriate.



\HDRcstar{Entry Complete}

\begin{code}
-- end Entry
\end{code}

\HDRc{Displaying Dictionaries}\label{hc:show-dicts}

\begin{code}
instance Show (Entry s) where
 show (AlfEntry vars) = "Alf {"++seplist ',' vars++"}"
 show (ExprEntry csub _ _ _) = "Expr, subst? = "++show csub
 show (PredEntry csub _ alf _ _)
  = "Pred, subFor"++show csub++", alf="++ashow alf
  where
    ashow [] = ""
    ashow xs = " {"++seplist ',' xs++"}"
 show (LawEntry r c u)
    = "Laws, #red="++show (length r)
      ++ ", #cred="++show (length c)
      ++ ", #loop="++show (length u)

seplist _ [] = []
seplist _ [xs] = xs
seplist s (xs:xss) = xs ++ s:seplist s xss

dictshow d
 = putStrLn $ unlines $ map entryShow $ M.assocs d

entryShow ( n, e ) = n ++ " :- " ++ show e
\end{code}




\HDRb{Recognisers}\label{hc:recog}

A recogniser looks for a specific pattern within
a predicate, and either returns \texttt{Nothing} if no such pattern exists
or else returns \texttt{Just} a selection of zero or more sub-components
of interest.
\begin{code}
type Recogniser s = Pred s -> Maybe [Pred s]

noBind        =  Just []
condBind c prs = if c then Just prs else Nothing
\end{code}

When building up rules it can help to have
a ``under construction'' law name:
\begin{code}
rUC = "RuleUnderConstruction!!!"
\end{code}
