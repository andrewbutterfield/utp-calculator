\HDRa{UTCP Laws}\label{ha:UTCP-laws}
\begin{code}
module UTCPLaws where
import Debug.Trace
import CalcPredicates
import CalcSteps
import UTCPSemantics
\end{code}


\HDRb{Tailoring ``standard'' UTP}

The definition of the semantics of the UTCP language
constructs, and of $run$,
make use of the (almost) standard notions of skip,
sequential composition
and iteration in UTP.
The versions used here are slightly non-standard because we have
non-homogeneous relations,
where the static parameters have no dashed counterparts.
In essence we ignore the parameters as far as flow-of-control is concerned:
\RLEQNS{
   \Skip &\defs& s'=s \land ls'=ls
\\ P ; Q
   &\defs&
   \exists s_m,ls_m @
     P[s_m,ls_m/s',ls']
     \land
     Q[s_m,ls_m/s,ls]
\\ c * P &\defs& \mu L @ (P ; L) \cond c \Skip
\\ P \cond c Q &\defs& c \land P \lor \lnot c \land Q
}
Here, the definition of $\cond\_$ is entirely standard, of course.

\HDRc{UTCP Skip}
\RLEQNS{
   \Skip &\defs& s'=s \land ls'=ls
}
\begin{code}
defnII = And[ Equal s' s, Equal ls' ls ]
\end{code}

In the calculator we do not implement the definitions
for $;$ and $c * P$,
as these would make the calculator far too complex.
Instead we implement a number of judiciously chosen laws
satisfied by certain (equally judiciously chosen) combinations
of these and other predicate constructs.
We define laws that are generally
viewed as reduction steps going from left-to-right.
\begin{code}
reduceUTCP :: (Show s, Ord s) => Dict s -> CalcStep s
\end{code}

\HDRb{Skip and Sequential Composition}

These laws are immediate, and their proof is left as an exercise.
\RLEQNS{
   \Skip;P &=& P & \elabel{$;$-l-unit}
\\ P;\Skip &=& P & \elabel{$;$-r-unit}
}
\begin{code}
reduceUTCP d (Seq Skip pr) = lred ";-lunit" pr
reduceUTCP d (Seq pr Skip) = lred ";-runit" pr
\end{code}

In the special case of atomic actions ($\alpha A = \setof{s,s'}$), we have:
\RLEQNS{
   s'=s ; A &=& A & \elabel{atomic-;-l-unit}
\\ A ; s'=s &=& A & \elabel{atomic-;-r-unit}
}
\begin{code}
reduceUTCP d (Seq (Equal (Var s1) (Var s2)) pA@(PVar a))
 | isIdleSeqAtom d s1 s2 a  =  lred "atomic-;-lunit" pA
reduceUTCP d (Seq pA@(PVar a) (Equal (Var s1) (Var s2)))
 | isIdleSeqAtom d s1 s2 a  =  lred "atomic-;-runit" pA
\end{code}


\HDRb{Iteration and Sequential Composition}

\HDRc{Loop UnRolling}

Iteration  satisfies the loop-unrolling law:
\[
  c * P  \quad=\quad (P ; c * P ) \cond c \Skip
\]
Currently already implemented in \texttt{CalcSteps} (\ref{hb:unroll}).

\HDRc{Conditions preceding Iteration}

The first law we have describes how a boolean variable changes as it
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

An obvious corollary of the above is:
\RLEQNS{
   s' = e \land ls' = f ; A
   &=&
   A[e,f/s,ls]
   & \elabel{$s'$-$ls'$-$;$-prop}
}
\begin{code}
reduceUTCP d (Seq (And [ Equal (Var "s'") e,
                         Equal (Var "ls'") f])
                  pA )
 = lred "s'ls'-;-prop" $ PSub pA [("s",e),("ls",f)]
reduceUTCP d (Seq (And [ Equal (Var ls'@"ls'") f,
                         Equal (Var s'@"s'") e])
                  pA )
 = lred "s'ls'-;-prop" $ PSub pA [("s",e),("ls",f)]
\end{code}

\HDRb{Disjunction and Sequential Composition}

We more specific laws first, more general later.

\RLEQNS{
   A ; ((B_1 \lor B_2) ; C)
   &=&
   (A ; (B_1 ; C)) \lor (A ; (B_2 ; C))
   & \ecite{$;$-$\lor$-3distr}
}
\begin{code}
reduceUTCP d (Seq pA (Seq (Or pBs) pC))
 = lred ";-\\/-3distr" $ Or $ map (bracketWith pA pC) pBs
 where
   bracketWith p q r = Seq p $ Seq r q
\end{code}

\RLEQNS{
   (A_1 \lor A_2) ; B
   &=&
   (A_1 ; B) \lor (A_2 ; B)
   & \ecite{$\lor$-$;$-distr}
}
\begin{code}
reduceUTCP d (Seq (Or pAs) pB)
 = lred "\\/-;-distr" $ Or $ map (postFixWith pB) pAs
 where
  postFixWith p q = Seq q p
\end{code}

We can always try to apply a substition:
\begin{code}
reduceUTCP d (PSub pr sub)
 | canSub pr  =  lred "substn" $ psubst sub pr
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
reduceUTCP d pr@(Seq (And pAs) (And pBs))
 = case isSafeLSDash d ls' pAs of
    Nothing -> lred "" pr
    Just (_,restA) ->
     case isSafeLSDash d ls pBs of
      Nothing -> lred "" pr
      Just (eqB,restB)
       -> lred "ls'-cleanup" $
             And [ Seq (mkAnd restA)
                       (mkAnd restB)
                 , eqB ]
 where
   ls = "ls"
   ls' = "ls'"

   isSafeLSDash d theLS prs
    = case matchRecog (isObsEqToConst "ls'" d) prs of
       Nothing -> Nothing
       Just (pre,eq@(Equal _ k),post) ->
        if notGround d k
         then Nothing
         else if all (dftlyNotInP d theLS) rest
          then Just (eq,rest)
          else Nothing
        where rest = pre++post
\end{code}

Assuming that $\fv{e'} \subseteq \setof{s',ls'}$, $x'\in\setof{s',ls'}$ and $\fv k \cap \setof{s,ls}=\emptyset$:
\RLEQNS{
   A \land e' ; B &=& A ; e \land B & \elabel{bool-$;$-switch}
\\ A \land x'=k ; B &=& A ; x=k \land B[k/x] & \elabel{const-$;$-prop}
}
\begin{code}
reduceUTCP d pr@(Seq (And pAs) pB)
 = case matchRecog (isDashedObsExpr d) pAs of
   Just (pre,Atm e',post)
    -> lred "bool-;-switch"
       $ Seq (And (pre++post)) $ And [Atm $ unDash e', pB]
   Nothing ->
    case matchRecog (isAfterEqToConst d) pAs of
     Just (pre,Equal (Var x') k,post)
      -> let x = init x'
         in lred "const-;-prop"
            $ Seq (And (pre++post))
                   $ And [Equal (Var x) k,PSub pB [(x,k)]]
     Nothing  ->  lred "" pr
\end{code}


That's all folks!
\begin{code}
reduceUTCP d pr = lred "" pr
\end{code}

\newpage
\HDRb{Definition Expansion}

Now we hard-code semantic definitions, starting with a dispatch function,
and then defining each replacement.
\begin{code}
defnUTCP :: Ord s => Pred s -> CalcResult s

defnUTCP Skip                =  ldefn "II" defnII
defnUTCP (PAtm a)            =  ldefn "A" $ defnAtomic a
defnUTCP PIdle               =  ldefn "Idle" $ defnIdle
defnUTCP (PSeq p q)          =  ldefn ";;" $ defnSeq p q
defnUTCP (PPar p q)          =  ldefn "||" $ defnPar p q
defnUTCP (PCond c p q)       =  ldefn "<$>" $ defnCond c p q
defnUTCP (PIter c p)         =  ldefn "<*>" $ defnIter c p
defnUTCP (PFun "run"   [p])  =  ldefn "run.3" $ defnRun 3 p
defnUTCP (PFun "run.1" [p])  =  ldefn "run.1" $ defnRun 1 p
defnUTCP (PFun "run.2" [p])  =  ldefn "run.2" $ defnRun 2 p
defnUTCP (PFun "run.3" [p])  =  ldefn "run.3" $ defnRun 3 p
defnUTCP (PFun "do" [p])     =  ldefn "do" $ defnDo p

-- specialised "definition" !!! Actually a law.
defnUTCP (PSub (PAtm a) subs)
                         =  lred "sub-atomic" $ substnAtomic a subs

defnUTCP pr                  =  ldefn "" pr

ldefn :: String -> Pred s -> CalcResult s
ldefn "" pr = ( "", pr )
ldefn nm pr = ( "defn. of " ++ nm, pr )
\end{code}
