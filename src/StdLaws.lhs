\HDRa{Standard Laws}\label{ha:std-laws}
\begin{code}
module StdLaws where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import CalcPredicates
import CalcAlphabets
import CalcSimplify
import CalcRecogniser
import StdPredicates
\end{code}




\HDRb{Tailoring ``standard'' UTP}

We make use of (almost) standard notions of skip,
sequential composition
and iteration in UTP for the theories we are trying to construct.
The versions used here are slightly non-standard because we have
non-homogeneous relations,
where the static parameters have no dashed counterparts.
In essence we ignore the parameters as far as flow-of-control is concerned:
\RLEQNS{
   \Skip &\defs& Dyn' = Dyn
\\ P ; Q
   &\defs&
   \exists Dyn_m @
     P[Dyn_m/Dyn']
     \land
     Q[Dyn_m/Dyn]
\\ c * P &\defs& \mu L @ (P ; L) \cond c \Skip
\\ P \cond c Q &\defs& c \land P \lor \lnot c \land Q
}
Here, the definition of $\cond\_$ is entirely standard, of course.

\HDRc{Standard Skip}\label{hc:std-Skip}
\RLEQNS{
   \Skip &\defs& Dyn' = Dyn
}
\begin{code}
defnII d
 = let dyn  = sort $ getAlpha aDyn  d
       dyn' = sort $ getAlpha aDyn' d
   in noMark $ mkAnd $ map alfEq $ zip dyn' dyn
 where
   alfEq(x',x) = noMark $ Equal (Var x') (Var x)
\end{code}

\newpage
\HDRc{Loop UnRolling}\label{hc:loop-unroll}

Iteration  satisfies the loop-unrolling law:
\[
  c * P  \quad=\quad (P ; c * P ) \cond c \Skip
\]

\begin{code}
unroll :: (Mark m, Ord s) => RWFun m s
unroll mw@(_,Comp "Iter"  [mc@(_,c), mpr])
 | isCondition c
           = lred "loop-unroll" $ bCond mc (bSeq mpr mw) bSkip
unroll mpr = lred "" mpr

lred nm mpr = ( nm, mpr )
\end{code}


\HDRb{Standard Reductions}\label{hb:std-reduce}

In the calculator we do not implement the definitions
for $;$ and $c * P$,
as these would make the calculator far too complex.
Instead we implement a number of judiciously chosen laws
satisfied by certain (equally judiciously chosen) combinations
of these and other predicate constructs.
We define laws that are generally
viewed as reduction steps going from left-to-right.
\begin{code}
reduceStd :: (Mark m, Ord s, Show s) => DictRWFun m s
\end{code}

\HDRc{Skip and Sequential Composition}\label{hc:skip-and-seq}

These laws are immediate, and their proof is left as an exercise.
\RLEQNS{
   \Skip;P &=& P & \elabel{$;$-l-unit}
\\ P;\Skip &=& P & \elabel{$;$-r-unit}
}
\begin{code}
reduceStd d (_,Comp "Seq" [(_,Comp "Skip" []), mpr])
                                            = lred ";-lunit" mpr
reduceStd d (_,Comp "Seq" [mpr, (_,Comp "Skip" [])])
                                            = lred ";-runit" mpr
\end{code}

\HDRc{Conditions preceding Iteration}

The first law we might consider describes how a boolean variable changes as it
crosses a ``$;$-boundary'':
\RLEQNS{
   A \land c' ; B &=& A ; c \land B & \elabel{condition-$;$-swap}
}
where we assume $c$ is a condition.

We do not provide this in the calculator,
but it is key to a number of laws that we do implement.


Now we look at more specific cases:
\RLEQNS{
  && A \land x'=k ; B  \qquad \fv k = \emptyset
\EQ{defn general UTP $;$}
\\&& \exists x_m,\nu_m @ A[x_m,\nu_m/x',\nu'] \land x_m = k \land B[x_m,\nu_m/x,\nu]
\EQm{y=e \land P \implies P[e/y]}
\\&& \exists x_m,\nu_m @ A[x_m,\nu_m/x',\nu'] \land x_m = k \land B[x_m,\nu_m/x,\nu][k/x_m]
\EQ{subst. comp.}
\\&& \exists x_m,\nu_m @ A[x_m,\nu_m/x',\nu'] \land x_m = k \land B[k,\nu_m/x,\nu]
\\
\\&& A \land x'=k ; B[k/x]
\EQ{defn general UTP $;$}
\\&& \exists x_m,\nu_m @ A[x_m,\nu_m/x',\nu'] \land x_m = k \land B[k/x][x_m,\nu_m/x,\nu]
\EQm{x \notin \fv{B[k/x]}}
\\&& \exists x_m,\nu_m @ A[x_m,\nu_m/x',\nu'] \land x_m = k \land B[k/x][\nu_m/\nu]
\EQ{subst. comp.}
\\&& \exists x_m,\nu_m @ A[x_m,\nu_m/x',\nu'] \land x_m = k \land B[k,\nu_m/x,\nu]
}

So given $k$ a ground term,
we have
\[
(A \land x'=k ; B)
=
(A \land x'=k ; B[k/x])
\]

This extends to multiple such equalities,
for  $x'_i \in Dyn'$ and $k_i$ ground:
\RLEQNS{
   A \land \bigwedge_i x'_i = k_i ; B
   &=&
   A \land \bigwedge_i x'_i = k_i ; B[k_i/x_i]
   & \elabel{some-$x'=k$-$;$-prop}
}
\begin{code}
-- reduceStd d
--  (_,Comp "Seq" [ conj@(_,Comp "And" mprs), mpr ])
--  | not (null x'eqks) && not (null rest)
--  = lred "some-x'=k-;-prop"
--      $ bSeq conj $ bPSub mpr $ map eqToSub x'eqks
--  where
--    (x'eqks,rest) = partition (isAfterEqToConst d) mprs
\end{code}
\textbf{Note:} this law can be repeatedly applied again
to its result --- it may not be such a good thing to have around!

If we only have such equalities,
and they cover all dynamic variables ($\setof{x'_i} = Dyn'$),
then we get:
\RLEQNS{
   \bigwedge_i x'_i = k_i ; B
   &=&
   B[k_i/x_i]
   & \elabel{all-$x'=k$-$;$-init}
}
We implement this latter one:
\begin{code}
reduceStd d
 (_,Comp "Seq" [ (_,Comp "And" mprs), mpr ])
 | all (isAfterEqToConst d) mprs
   && sort (map getLVar mprs) == sort (getAlpha aDyn' d)
 = lred "all-x'=k-;-init" $ bPSub mpr $ map eqToSub mprs
 where
   getLVar (_,Equal (Var x') _) = x'
\end{code}

Assuming that $\fv{e'} \subseteq Dyn'$,
$x'\in Dyn'$,
 and $\fv k \cap Dyn =\emptyset$:
\RLEQNS{
   A \land e' ; B &=& A ; e \land B & \elabel{bool-$;$-switch}
\\ A \land x'=k ; B &=& A ; x=k \land B[k/x] & \elabel{const-$;$-prop}
}
\begin{code}
reduceStd d (_, Comp "Seq" [(_,Comp "And" mpAs), mpB])

 | isJust match1
     = lred "bool-;-switch"
        $ bSeq (bAnd (pre1++post1)) $ bAnd [bAtm $ unDash e', mpB]

 | isJust match2
     = let x = init x'
       in lred "const-;-prop"
           $ bSeq (bAnd (pre2++post2))
                $ bAnd [bEqual (Var x) k,bPSub mpB [(x,k)]]
 where

   match1 = matchRecog (isDashedObsExpr d) mpAs
   Just (pre1,(_,Atm e'),post1) = match1

   match2 = matchRecog (isAfterEqToConst d) mpAs
   Just (pre2,(_,Equal (Var x') k),post2) = match2
\end{code}

\HDRc{Disjunction and Sequential Composition}

We more specific laws first, more general later.

\RLEQNS{
   A ; ((B_1 \lor B_2) ; C)
   &=&
   (A ; (B_1 ; C)) \lor (A ; (B_2 ; C))
   & \ecite{$;$-$\lor$-3distr}
}
\begin{code}
reduceStd d 
  (_, Comp "Seq" [ mpA
                 , (_,Comp "Seq" [ (_,Comp "Or" mpBs)
                                 , mpC] ) ] )
 = lred ";-\\/-3distr" $ bOr $ map (bracketWith mpA mpC) mpBs
 where
   bracketWith p q r = bSeq p $ bSeq r q
\end{code}

\RLEQNS{
   (A_1 \lor A_2) ; B
   &=&
   (A_1 ; B) \lor (A_2 ; B)
   & \ecite{$\lor$-$;$-distr}
}
\begin{code}
reduceStd d (_,Comp "Seq" [(_,Comp "Or" mpAs), mpB])
 = lred "\\/-;-distr" $ bOr $ map (postFixWith mpB) mpAs
 where
  postFixWith p q = bSeq q p
\end{code}


\HDRc{Substitution}

We can always try to apply a substition:
\begin{code}
reduceStd d (_,PSub mpr sub)
 | substitutable d mpr && chgd = lred "substn" $ noMark pr'
 where
   (chgd,pr') = psubst startm d sub mpr
\end{code}


That's all folks!
\begin{code}
reduceStd d mpr = lred "" mpr
\end{code}


\newpage
\HDRb{The Standard Dictionary}\label{hb:std-dict}

\begin{code}
stdDict :: (Eq m, Ord s, Show s) => Dict m s
stdDict
 = M.fromList
    [ topEntry
    , botEntry
    , notEntry
    , andEntry
    , orEntry
    , ndcEntry
    , impEntry
    , rfdbyEntry
    , condEntry
    , skipEntry
    , seqEntry
    , iterEntry
    ]
\end{code}

\HDRc{Debugging aids}

\begin{code}
putPred :: (Eq m, Mark m, Ord s, Show s) => Pred m s -> IO ()
putPred = putStrLn . pdshow 80 stdDict
putMPred :: (Eq m, Mark m, Ord s, Show s) => MPred m s -> IO ()
putMPred = putPred . snd
\end{code}
