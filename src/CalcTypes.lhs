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
 | Comp String [MPred s]
 | PSub (MPred s) (Substn s)
 | PUndef
 deriving (Ord, Show)
\end{code}
Marked predicates are marks paired with a predicate,
denoted by the \texttt{MPred} datatype:
\begin{code}
type MPred s = ( Marks, Pred s )

type Mark = Int
type Marks = [Mark]
\end{code}
We provide functions to remove markings
and to make changes `under' markings:
\begin{code}
mkstrip :: [MPred s] -> [Pred s]
mkstrip = map snd

pfapply :: (Pred s -> Pred s) -> MPred s -> MPred s
pfapply pf (m, p) = (m, pf p)
\end{code}

Mark management (SHOULD LIVE ELSEWHERE)
\begin{code}
startm :: Mark
startm = 0
nextm, prevm :: Mark -> Mark
nextm = (+1)
prevm = subtract 1
\end{code}


Predicate equality is defined on the underlying predicate,
so that it ignores marking completely.
\begin{code}
instance Eq s => Eq (Pred s) where
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

Sometimes we need to view everything:
\begin{code}
viewPred :: Show s => MPred s -> String
viewPred
 = unlines . vPred 0
 where

   ind i strs = map (replicate i ' ' ++) strs

   vPred i (ms, T) = ind i ["T : "++show ms]
   vPred i (ms, F) = ind i ["F : "++show ms]
   vPred i (ms, PVar pv) = ind i ["PVar '"++pv++"' : "++show ms]
   vPred i (ms, Equal e1 e2)
     = ind i ["Equal : "++show ms]
       ++ vExpr (i+2) e1
       ++ vExpr (i+2) e2
   vPred i (ms, Atm e)
    = ind i ["Atm : "++show ms]
      ++ vExpr (i+2) e
   vPred i (ms, Comp name mprs)
    = ind i ["Comp '"++name++"' : "++show ms]
      ++ concat (map (vPred (i+2)) mprs)
   vPred i (ms, PSub mpr sub)
    = ind i ["Psub : "++show ms]
      ++ vPred (i+2) mpr
      ++ vSbst (i+2) sub

   vExpr i (St s)  = ind i ["St "++show s]
   vExpr i (B b)   = ind i ["B "++show b]
   vExpr i (Z z)   = ind i ["Z "++show z]
   vExpr i (Var v) = ind i ["Var "++"'"++v++"'"]
   vExpr i e       = ind i ["Expr..."]

   vSbst i subs = ind i ["Subst for "++show (map fst subs)]

putView :: Show s => MPred s -> IO ()
putView = putStrLn . viewPred
\end{code}

We need a function from markings to styles:
\begin{code}
type MarkStyle = Int -> Maybe Style

noStyles :: MarkStyle
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

When applying general laws (usually as reductions)
then we need a function that takes a dictionary and predicate



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
     pcansub :: [String]                      -- substitutable vars
   , pprint  :: Dict s -> MarkStyle           -- pretty printer
             -> Int -> [MPred s]
             -> PP
   , alfa :: [String]  -- predicate alphabet
   , pdefn   :: Rewrite s                    -- defn expansion
   , prsimp  :: Rewrite s                    -- simplifier
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



\newpage
\HDRb{Zipper Datatypes}\label{hb:zipper-types}

We note, using the notion of ``datatypes as algebras'',
%( http://chris-taylor.github.io/blog/2013/02/13/the-algebra-of-algebraic-data-types-part-iii/)
that the \texttt{Pred s} and \texttt{MPred s} types above
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
We want to define a ``zipper'' \cite{JFP::Huet1997} for \texttt{MPred s},
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
data MPred' s
 = Comp'         -- parent is a Comp node
     Marks       -- parent marking
     String      -- parent name
     [MPred s] -- components before current focus
     [MPred s] -- components after current focus
 | PSub'         -- parent is a PSub node
     Marks       -- parent marking
     (Substn s)  -- substitution in parent
 deriving Show
\end{code}
We then define a zipper as being an predicate
together with a list of predicate derivatives:
\begin{code}
type MPZipper s
  = ( MPred s    -- the current (focus) predicate
    , [MPred' s] -- the steps we took to get here,
                   -- and what we passed on the way.
    )
\end{code}

\newpage
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
  && ( \ldots \OLD{q_1} \ldots q_2 \ldots q_3 \ldots)
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
The interpretation of such marks as old, new or irrelevant can then be done
relative to the numbering of the step outcome being rendered for display.

We can breakdown the above calculation using mark numbers ($M_i$) as follows
\RLEQNS{
   ne_0  && ( \ldots q_1 \ldots q_2 \ldots q_3 \ldots)
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

Under the hood we need \texttt{RWResult} versions with marked predicates:
\begin{code}
type MRWResult s
 = Maybe ( String  -- rewrite justification
         , MPred s  -- result marked predicate
         , Bool )  -- True if top-level modified

type MCRWResult s
 = Maybe ( String      -- justification
         , [( Pred s   -- side-condition to be discharged
            , MPred s   -- modified marked predicate
            , Bool)])  -- True if top-level modified
\end{code}

In order to mark and highlight predicates in calculation steps,
we need to return not just the modified result, marked at the point of change,
but also the original predicate, also marked at the same location
(with the same mark in each case --- the mark identifies the specific
calculation step).
We have a type that has this information,
along with a justification string:
\begin{code}
type BeforeAfter s
 = ( MPred s   -- before predicate, marked
   , String      -- justification
   , MPred s ) -- after predicate, marked
\end{code}
In the conditional case, we have lists of outcomes
paired with conditions:
\begin{code}
type BeforeAfters s
 = ( MPred s   -- before predicate, marked
   , String      -- justification
   , [(Pred s,MPred s)] ) -- after predicates, marked
\end{code}

This seems to present a problem for the zipper,
as we have to identify corresponding locations,
where $q_i$ and $q'_i$ reside,
in two different versions of a single predicate.
However the structure of the two predicates is identical everywhere else
so a single zipper ``path'' can be applied to both.

\begin{code}
type MPZip2 s = (BeforeAfter s, [MPred' s])
\end{code}

For conditional searches,
we return a list of \texttt{Pred},\texttt{MPred} pairs:
\begin{code}
type CMPZip2 s = ( BeforeAfters s, [MPred' s] )
\end{code}

A calculation log records all pertinent data regarding a calculation
\begin{code}
type CalcLog s = ( MPred s      -- initial predicate (pe1)
                 , [(String, MPred s)] -- steps, most recent first
                 , Dict s )     -- final dictionary
\end{code}
The dictionary is included as it is required, for example,
to pretty-print the predicates.

It can help to be able to see all the gory details.
\begin{code}
viewcalc :: Show s => CalcLog s -> IO ()
viewcalc (currpr,steps,_)
 = vc 0 $ reverse (("QED",currpr):steps)
 where
   vc _ [] = return ()
   vc s ((what,mpr):rest)
     = do putStrLn ("Step "++show s)
          putView mpr
          putStrLn ("\n= '"++what++"'\n")
          vc (s+1) rest
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
