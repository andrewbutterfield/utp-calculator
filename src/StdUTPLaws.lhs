\HDRa{Standard UTP Laws}\label{ha:std-UTP-laws}
\begin{code}
module StdUTPLaws where
import Utilities
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
import StdUTPPredicates
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
   in  mkAnd $ map alfEq $ zip dyn' dyn
 where
   alfEq(x',x) = Equal (Var x') (Var x)
\end{code}

\newpage

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
lred nm pr = Just ( nm, pr, diff )

reduceStd :: RWFun
\end{code}

\HDRc{Skip and Sequential Composition}\label{hc:skip-and-seq}

These laws are immediate, and their proof is left as an exercise.
\RLEQNS{
   \Skip;P &=& P & \elabel{$;$-l-unit}
\\ P;\Skip &=& P & \elabel{$;$-r-unit}
}
\begin{code}
reduceStd d _ (Comp "Seq" [(Comp "Skip" []), pr])
                                            = lred ";-lunit" pr
reduceStd d _ (Comp "Seq" [pr, (Comp "Skip" [])])
                                            = lred ";-runit" pr
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
--      $ mkSeq conj $ bPSub mpr $ map eqToSub x'eqks
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
reduceStd d _
 (Comp "Seq" [ (Comp "And" prs), pr ])
 | (all (isAfterEqToConst d) prs)
   && sort (map getLVar prs) == sort (getAlpha aDyn' d)
 = lred "all-x'=k-;-init" $ PSub pr $ map eqToSub prs
 where
   getLVar (Equal (Var x') _) = x'
\end{code}

Assuming that $\fv{e'} \subseteq Dyn'$,
$x'\in Dyn'$,
 and $\fv k \cap Dyn =\emptyset$:
\RLEQNS{
   A \land e' ; B &=& A ; e \land B & \elabel{bool-$;$-switch}
\\ A \land x'=k ; B &=& A ; x=k \land B[k/x] & \elabel{const-$;$-prop}
}
\begin{code}
reduceStd d _ (Comp "Seq" [(Comp "And" pAs), pB])

 | isJust match1
     = lred "bool-;-switch"
        $ mkSeq (mkAnd (pre1++post1)) $ mkAnd [Atm $ unDash e', pB]

 | isJust match2
     = let x = init x'
       in lred "const-;-prop"
           $ mkSeq (mkAnd (pre2++post2))
                $ mkAnd [Equal (Var x) k, PSub pB [(x,k)]]
 where

   match1 = matchRecog (mtchDashedObsExpr d) pAs
   Just (pre1, (_,[Atm e']), post1) = match1

   match2 = matchRecog (mtchAfterEqToConst d) pAs
   Just (pre2, (Equal (Var x') k,_), post2) = match2
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
reduceStd d _
  (Comp "Seq" [ pA
              , (Comp "Seq" [ (Comp "Or" pBs)
                              , pC] ) ] )
 = lred ";-\\/-3distr" $ mkOr $ map (bracketWith pA pC) pBs
 where
   bracketWith p q r = mkSeq p $ mkSeq r q
\end{code}

\RLEQNS{
   (A_1 \lor A_2) ; B
   &=&
   (A_1 ; B) \lor (A_2 ; B)
   & \ecite{$\lor$-$;$-distr}
}
\begin{code}
reduceStd d _ (Comp "Seq" [(Comp "Or" pAs), pB])
 = lred "\\/-;-distr" $ mkOr $ map (postFixWith pB) pAs
 where
  postFixWith p q = mkSeq q p
\end{code}


That's all folks!
\begin{code}
reduceStd d _ mpr = lred "" mpr
\end{code}

Now, the standard reduction dictionary entry:
\begin{code}
stdReduceEntry :: Dict
stdReduceEntry = entry laws $ LawEntry [reduceStd] [] []
\end{code}

\HDRb{Standard Loop Unrolling}\label{hb:std-loop-unroll}

Iteration  satisfies the loop-unrolling law:
\[
  c * P  \quad=\quad (P ; c * P ) \cond c \Skip
\]
\begin{code}
unrollStd :: String -> RWFun
unrollStd ns d _ w@(Comp nm  [c, pr])
 | nm== nIter && isCondition c
           = Just( "std-loop-unroll"
                 , mkCond (mkSeq pr w) c mkSkip
                 , diff )
unrollStd _ _ _ _ = Nothing
\end{code}

Now, the standard unroll dictionary entry:
\begin{code}
stdUnrollEntry :: Dict
stdUnrollEntry = entry laws $ LawEntry [] [] [unrollStd]
\end{code}

\newpage
\HDRb{The Standard UTP Dictionary}\label{hb:std-UTP-dict}

\begin{code}
stdUTPDict :: Dict
stdUTPDict
 = makeDict
    [ topEntry
    , botEntry
    , ndcEntry
    , rfdbyEntry
    , condEntry
    , skipEntry
    , seqEntry
    , iterEntry
    ] `dictMrg` stdReduceEntry
      `dictMrg` stdUnrollEntry
\end{code}
