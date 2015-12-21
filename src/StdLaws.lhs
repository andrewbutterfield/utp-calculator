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
reduceStd :: Ord s => DictRWFun m s
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
for all $x'_i \in Dyn'$ and $k_i$ ground:
\RLEQNS{
   A \land \bigwedge_i x'_i = k_i ; B
   &=&
   A \land \bigwedge_i x'_i = k_i ; B[k_i/x_i]
   & \elabel{$x'=k$-$;$-prop}
}
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
 = lred "all-x'=k-;-init" $ noMark $ PSub mpr $ map eqToSub mprs
 where
   eqToSub (_,Equal (Var x') e) = (x',e)
   getLVar (_,Equal (Var x') _) = x'
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
-- reduceStd d (Seq pA (Seq (Or pBs) pC))
--  = lred ";-\\/-3distr" $ Or $ map (bracketWith pA pC) pBs
--  where
--    bracketWith p q r = Seq p $ Seq r q
\end{code}

\RLEQNS{
   (A_1 \lor A_2) ; B
   &=&
   (A_1 ; B) \lor (A_2 ; B)
   & \ecite{$\lor$-$;$-distr}
}
\begin{code}
-- reduceStd d (Seq (Or pAs) pB)
--  = lred "\\/-;-distr" $ Or $ map (postFixWith pB) pAs
--  where
--   postFixWith p q = Seq q p
\end{code}

We can always try to apply a substition:
\begin{code}
-- reduceStd d (PSub pr sub)
--  | canSub pr  =  lred "substn" $ psubst sub pr
\end{code}

\newpage
A useful reduction for tidying up at the end,
assuming that $ls' \notin A$ and $ls \notin B$, and both $k$ and $h$
are ground:
\RLEQNS{
   A \land ls'=k ; B \land ls'= h
   &\equiv&
   (A;B) \land ls'=h
   & \elabel{$ls'$-cleanup}
}
\begin{code}
-- reduceStd d pr@(Seq (And pAs) (And pBs))
--  = case isSafeLSDash d ls' pAs of
--     Nothing -> lred "" pr
--     Just (_,restA) ->
--      case isSafeLSDash d ls pBs of
--       Nothing -> lred "" pr
--       Just (eqB,restB)
--        -> lred "ls'-cleanup" $
--              And [ Seq (mkAnd restA)
--                        (mkAnd restB)
--                  , eqB ]
--  where
--    ls = "ls"
--    ls' = "ls'"
--
--    isSafeLSDash d theLS prs
--     = case matchRecog (isObsEqToConst "ls'" d) prs of
--        Nothing -> Nothing
--        Just (pre,eq@(Equal _ k),post) ->
--         if notGround d k
--          then Nothing
--          else if all (dftlyNotInP d theLS) rest
--           then Just (eq,rest)
--           else Nothing
--         where rest = pre++post
\end{code}

Assuming that $\fv{e'} \subseteq \setof{s',ls'}$, $x'\in\setof{s',ls'}$ and $\fv k \cap \setof{s,ls}=\emptyset$:
\RLEQNS{
   A \land e' ; B &=& A ; e \land B & \elabel{bool-$;$-switch}
\\ A \land x'=k ; B &=& A ; x=k \land B[k/x] & \elabel{const-$;$-prop}
}
\begin{code}
-- reduceStd d pr@(Seq (And pAs) pB)
--  = case matchRecog (isDashedObsExpr d) pAs of
--    Just (pre,Atm e',post)
--     -> lred "bool-;-switch"
--        $ Seq (And (pre++post)) $ And [Atm $ unDash e', pB]
--    Nothing ->
--     case matchRecog (isAfterEqToConst d) pAs of
--      Just (pre,Equal (Var x') k,post)
--       -> let x = init x'
--          in lred "const-;-prop"
--             $ Seq (And (pre++post))
--                    $ And [Equal (Var x) k,PSub pB [(x,k)]]
--      Nothing  ->  lred "" pr
\end{code}


That's all folks!
\begin{code}
reduceStd d mpr = lred "" mpr
\end{code}

\newpage
\HDRb{Definition Expansion}

Now we hard-code semantic definitions, starting with a dispatch function,
and then defining each replacement.
\begin{code}
-- defnUTCP :: Ord s => Pred s -> CalcResult s
--
-- defnUTCP Skip                =  ldefn "II" defnII
-- defnUTCP (PAtm a)            =  ldefn "A" $ defnAtomic a
-- defnUTCP PIdle               =  ldefn "Idle" $ defnIdle
-- defnUTCP (PSeq p q)          =  ldefn ";;" $ defnSeq p q
-- defnUTCP (PPar p q)          =  ldefn "||" $ defnPar p q
-- defnUTCP (PCond c p q)       =  ldefn "<$>" $ defnCond c p q
-- defnUTCP (PIter c p)         =  ldefn "<*>" $ defnIter c p
-- defnUTCP (PFun "run"   [p])  =  ldefn "run.3" $ defnRun 3 p
-- defnUTCP (PFun "run.1" [p])  =  ldefn "run.1" $ defnRun 1 p
-- defnUTCP (PFun "run.2" [p])  =  ldefn "run.2" $ defnRun 2 p
-- defnUTCP (PFun "run.3" [p])  =  ldefn "run.3" $ defnRun 3 p
-- defnUTCP (PFun "do" [p])     =  ldefn "do" $ defnDo p
--
-- -- specialised "definition" !!! Actually a law.
-- defnUTCP (PSub (PAtm a) subs)
--                          =  lred "sub-atomic" $ substnAtomic a subs
--
-- defnUTCP pr                  =  ldefn "" pr

ldefn :: String -> RWFun m s
ldefn "" mpr = ( "", mpr )
ldefn nm mpr = ( "defn. of " ++ nm, mpr )
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
