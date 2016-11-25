\HDRa{Calculator System Types}\label{ha:calc-sys-types}
\begin{code}
module CalcSysTypes where
import qualified Data.Map as M
import PrettyPrint
import CalcTypes
\end{code}

Here we have under-the-hood types used to implement
all the calculator features.
Users should not import this or need to know what happens here.

\HDRb{Marking}

We shall mark predicates with zero or more integers:
\begin{code}
type Mark = Int
type Marks = [Mark]
\end{code}

Marking is done by constructing a tree-structure
that matches the predicate structure:
\begin{code}
data MTree = MT Marks [MTree] deriving (Eq, Ord, Show)
\end{code}

Marked predicates are marks paired with a predicate,
denoted by the \texttt{MPred} datatype:
\begin{code}
type MPred = ( Pred, MTree )
\end{code}

We provide a marking constructor that marks a tree with no integers:
\begin{code}
buildMarks :: Pred -> MPred
buildMarks pr@(Comp _ prs)
 = ( pr, MT [] mts )
   where mts = map (snd . buildMarks) prs
buildMarks pr@(PSub spr _)
 = ( pr, MT [] [mt] )
   where mt = snd $ buildMarks spr
buildMarks pr = ( pr, MT [] [] )
\end{code}

There is a key invariant that \texttt{MPred} must satisfy:
\begin{code}
invMPred :: MPred -> Bool
invMPred (Comp _ prs, MT _ mts)
 = length mts == length prs && all invMPred (zip prs mts)
invMPred (PSub pr _, MT _ mts)
 = length mts == 1 && invMPred (pr, head mts)
invMPred (_, MT _ mts) = null mts
\end{code}

We really should prove \texttt{invMPred (buildMarks pr)} !


We provide a HOF to make changes `under' markings:
\begin{code}
pfapply :: (Pred -> Pred) -> MPred -> MPred
pfapply pf (pr, mt) = (pf pr, mt)
\end{code}

Sometimes we need to view everything:
\begin{code}
viewPred :: MPred -> String
viewPred
 = unlines . vPred 0
 where

   ind i strs = map (replicate i ' ' ++) strs

   vPred i (pr, mt) = [show pr,"@",show mt]

--    vPred i (T, ms, T) = ind i ["T : "++show ms]
--    vPred i (ms, F) = ind i ["F : "++show ms]
--    vPred i (ms, PVar pv) = ind i ["PVar '"++pv++"' : "++show ms]
--    vPred i (ms, Equal e1 e2)
--      = ind i ["Equal : "++show ms]
--        ++ vExpr (i+2) e1
--        ++ vExpr (i+2) e2
--    vPred i (ms, Atm e)
--     = ind i ["Atm : "++show ms]
--       ++ vExpr (i+2) e
--    vPred i (ms, Comp name mprs)
--     = ind i ["Comp '"++name++"' : "++show ms]
--       ++ concat (map (vPred (i+2)) mprs)
--    vPred i (ms, PSub mpr sub)
--     = ind i ["Psub : "++show ms]
--       ++ vPred (i+2) mpr
--       ++ vSbst (i+2) sub
--
--    vExpr i (St s)  = ind i ["St "++show s]
--    vExpr i (B b)   = ind i ["B "++show b]
--    vExpr i (Z z)   = ind i ["Z "++show z]
--    vExpr i (Var v) = ind i ["Var "++"'"++v++"'"]
--    vExpr i e       = ind i ["Expr..."]
--
--    vSbst i subs = ind i ["Subst for "++show (map fst subs)]

putView :: MPred -> IO ()
putView = putStrLn . viewPred
\end{code}

We need a function from markings to styles:
\begin{code}
type MarkStyle = Int -> Maybe Style

noStyles :: MarkStyle
noStyles = const Nothing
\end{code}




\newpage
\HDRb{Zipper Datatypes}\label{hb:zipper-types}

We note, using the notion of ``datatypes as algebras'',
%( http://chris-taylor.github.io/blog/2013/02/13/the-algebra-of-algebraic-data-types-part-iii/)
that the \texttt{Pred} and \texttt{MPred} types above
correspond to the following algebraic forms:
\RLEQNS{
   V && & \mbox{Variables}
\\ E && & \mbox{Expressions}
\\ M && & \mbox{Marks}
\\ P   &=& \mathbf 1
         + \mathbf 1
         + \Char^*
         + E \times E
         + E
\\    && + \Char^* \times P^*
         + P \times (V \times E)^* & \mbox{Predicates}
\\  &=& F(P)
\\ T &=& M \times T^* & \mbox{Mark Trees}
\\ &=& G(T)
}
We want to define a ``zipper'' \cite{JFP::Huet1997} for \texttt{MPred},
following Conor McBride's Datatype Differentiation approach\cite{McB:derrti}.
In effect we want a parallel zipper that keeps both the predicate
and mark-tree in sync.
So, we ``differentiate'' the expressions for $P$ and $T$
 above w.r.t. $P$ and $T$ respectively.,
to obtain $MP'_M$:
\RLEQNS{
   P' &=& \partial_{P}(F)
\\    &=& \Char^* \times (P^*)^2  +  (V \times E)^*
\\ T' &=& \partial_{T}(G)
\\    &=& M \times (T^*)^2
}
We used the following differentiation laws:
\RLEQNS{
   d(x^n)/dx &=& nx^{n-1}
\\ d(x^*)/dx &=& (x^*)^2
\\ d(kf)/dx  &=& k(df/fx) & k\mbox{ a constant}
}
This leads to the following zipper datatypes:
\begin{code}
data Pred'
 = Comp'        -- parent is a Comp node
     String       -- parent name
     [Pred]     -- components before current focus
     [Pred]     -- components after current focus
 | PSub'        -- parent is a PSub node
     Substn     -- substitution in parent
 deriving Show

data MTree'
 = MT'       -- parent is always a MT node
     Marks     -- parents marking
     [MTree]   -- components before current focus
     [MTree]   -- components before current focus

type MPred' = ( Pred', MTree' )
\end{code}
We then define a zipper as being an predicate
together with a list of predicate derivatives:
\begin{code}
type MPZipper
  = ( MPred    -- the current (focus) predicate
    , [MPred']  -- the steps we took to get here,
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
type MRWResult
 = Maybe ( String  -- rewrite justification
         , MPred  -- result marked predicate
         , Bool )  -- True if top-level modified

type MCRWResult
 = Maybe ( String      -- justification
         , [( Pred   -- side-condition to be discharged
            , MPred   -- modified marked predicate
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
type BeforeAfter
 = ( MPred   -- before predicate, marked
   , String      -- justification
   , MPred ) -- after predicate, marked
\end{code}
In the conditional case, we have lists of outcomes
paired with conditions:
\begin{code}
type BeforeAfters
 = ( MPred   -- before predicate, marked
   , String      -- justification
   , [(Pred,MPred)] ) -- after predicates, marked
\end{code}

This seems to present a problem for the zipper,
as we have to identify corresponding locations,
where $q_i$ and $q'_i$ reside,
in two different versions of a single predicate.
However the structure of the two predicates is identical everywhere else
so a single zipper ``path'' can be applied to both.

\begin{code}
type MPZip2  = (BeforeAfter, [MPred' ])
\end{code}

For conditional searches,
we return a list of \texttt{Pred},\texttt{MPred} pairs:
\begin{code}
type CMPZip2 = ( BeforeAfters, [MPred'] )
\end{code}

First, the REPL state:
\begin{code}
type Step
 = ( String        -- step justification
   , MPred )     -- prev predicate
type State
 = ( MPred       -- current goal predicate
   , [Step ]      -- calc steps so far
   , InvState  )  -- invariant
\end{code}

A calculation log records all pertinent data regarding a calculation
\begin{code}
type CalcLog  = ( State    -- final state
                 , Dict )  -- final dictionary
\end{code}
The dictionary is included as it is required, for example,
to pretty-print the predicates.

It can help to be able to see all the gory details.
\begin{code}
viewcalc :: CalcLog  -> IO ()
viewcalc ((currpr,steps,_),_)
 = vc 0 $ reverse (("QED",currpr):steps)
 where
   vc _ [] = return ()
   vc s ((what,mpr):rest)
     = do putStrLn ("Step "++show s)
          putView mpr
          putStrLn ("\n= '"++what++"'\n")
          vc (s+1) rest
\end{code}
