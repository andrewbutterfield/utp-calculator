\HDRa{UTCP Conditional Reducer}\label{ha:UTCP-cond:reduce}
\begin{code}
module UTCPCReduce where
import CalcTypes
import CalcAlphabets
import CalcPredicates
import CalcSimplify
import CalcSteps
import CalcRecogniser
import StdPredicates
import StdUTPPredicates
import UTCPSemantics
import UTCPLaws
\end{code}

To avoid having to support a wide range of expression-related theories,
we provide a conditional reducer, that computes
a number of alternative outcomes, each guarded by some predicate
that is hard to evaluate.
The user elects which one to use by checking the conditions manually.

A result wrapper:
\begin{code}
lcred nm cmprs = Just ( nm, cmprs )
\end{code}

\begin{code}
creduceUTCP :: CRWFun
\end{code}

\HDRc{pre- and before-substitutions}
A pre-substitution is one that replaces undashed variables with
undashed expressions, while a before-substitution is further restricted
to replacing undashed observables only.
\begin{code}
preSublet :: ( String, Expr ) -> Bool
preSublet (v,e) = notDash v && notDashed e

preSub :: Substn -> Bool
preSub = all preSublet

beforeSublet :: Dict -> ( String, Expr ) -> Bool
beforeSublet d (v,e) = isDyn d v && notDashed e

beforeSub :: Dict -> Substn -> Bool
beforeSub d = all (beforeSublet d)
\end{code}


\HDRc{Atomic Enablement}

\RLEQNS{
   ns(\ell_0)
   &\implies&
   \A(A)[\ell_0,\ell_1,ns/in,out,ls]
    = A \land ls'=ns\ominus(\ell_0,\ell_1)
\\ \lnot ns(\ell_0)
   &\implies&
   \A(A)[\ell_0,\ell_1,ns/in,out,ls]
    = \false
}
\begin{code}
creduceUTCP d (PSub (Comp "PAtm" [pA])
                      [("in",l0),("out",l1),("ls",ns)] )
 = lcred "Atm-substn" [doA,nowt]
 where
   nsl0 = Atm $ subset l0 ns
   doA  = ( psimp d nsl0
          , mkAnd [pA, Equal ls' $ sswap ns l0 l1 ]
          , diff )
   nowt = ( psimp d $ mkNot nsl0
          , F
          , diff )
\end{code}

\HDRc{Before-Var Iteration substitution}

We exploit the results of following calculation,
given conditions $b$ and $c$ such that $b \implies c$:
\RLEQNS{
  && A \land b' ; c * B
\EQ{\eref{condition-$;$-swap}}
\\&& A ; b \land c * B
\EQ{$b \implies c$, so we iterate at least once}
\\&& A ; b \land ( B; c * B )
\EQ{\eref{condition-$;$-swap}}
\\&& A \land b' ; ( B; c * B )
\EQ{$;$ assoc}
\\&& ( A \land b' ;  B) ; c * B
\EQ{\eref{condition-$;$-swap}}
\\&& ( A ; b \land  B) ; c * B
}
If $b \implies \lnot c$, then we get
\RLEQNS{
  && A \land b' ; c * B
\EQ{\eref{condition-$;$-swap}}
\\&& A ; b \land c * B
\EQ{$b \implies \lnot c$, so we exit the loop}
\\&& A ; b \land \Skip
\EQ{\eref{condition-$;$-swap}}
\\&& A \land b' ; \Skip
\EQ{$\Skip$ is identity}
\\&& A \land b'
}

From this we can deduce the following laws:

Provided that $\vec x \subseteq in\alpha P$
 (which in this case is $\setof{s,ls}$):
\RLEQNS{
   c[\vec e/\vec x]
   &\implies&
   (c * P)[\vec e/\vec x] = P[\vec e/\vec x] ; c * P
\\ \lnot c[\vec e/\vec x]
   &\implies&
   (c * P)[\vec e/\vec x] = \Skip[\vec e/\vec x]
}
\begin{code}
creduceUTCP d (PSub w@(Comp "Iter" [c,p]) sub)
 | isCondition c && beforeSub d sub
 = lcred "loop-substn" [ctrue,cfalse]
 where
   csub = PSub c sub
   ctrue  = ( psimp d csub
            , mkSeq (PSub p sub) w
            , diff )
   cfalse = ( psimp d $ mkNot csub
            , PSub mkSkip sub
            , diff )
\end{code}

\HDRc{Before-Var Condition substitution}

Provided that $\vec x$ are undashed:
\RLEQNS{
   c[\vec e/\vec x]
   &\implies&
   (P \cond c Q)[\vec e/\vec x] = P[\vec e/\vec x]
\\ \lnot c[\vec e/\vec x]
   &\implies&
   (P \cond c Q)[\vec e/\vec x] = Q[\vec e/\vec x]
}
\begin{code}
creduceUTCP d (PSub (Comp "Cond" [c,p,q]) sub)
 | isCondition c && preSub sub
 = lcred "cond-substn" [ctrue,cfalse]
 where
   csub = PSub c sub
   ctrue  = ( psimp d csub
            , PSub p sub
            , diff )
   cfalse = ( psimp d $ mkNot csub
            , PSub q sub
            , diff )
\end{code}

\HDRc{Boolean followed by iteration}

Provided $\fv{b'} \subseteq \setof{s',ls'}$, $x'$ is an observation, and $k$ is ground
\begin{code}
creduceUTCP d mpr@(Comp "Seq" [ a@(Comp "And" prs)
                                , w@(Comp "Iter" [c,pB]) ])
 | isCondition c

\end{code}
\RLEQNS{
   (b \implies c)       &\implies& A \land b' ; c * B = (A ; b \land B) ; c * B
\\ (b \implies \lnot c) &\implies& A \land b' ; c * B = A \land b'
}
\begin{code}
   = case matchRecog (mtchDashedObsExpr d) prs of
     Just (pre,((Atm e'),_),post)
      -> let
          e = Atm $ unDash e'
          continue = ( psimp d $ mkImp e c
                     , mkSeq (mkSeq (mkAnd (pre++post)) (mkAnd [e, pB])) w
                     , diff )
          stop     = ( psimp d $ mkImp e (mkNot c)
                     , a
                     , diff )
         in lcred "loop-step" [continue,stop]
\end{code}
\newpage
\RLEQNS{
   (x=k \implies c)
   &\implies&
   (A \land x' = k ; c * B)
   =
   (A \land x'=k ; B[k/x] ; c * B)
\\ (x=k \implies \lnot c)
   &\implies&
   (A \land x' = k ; c * B)
   =
   (A \land x'=k)
}
\begin{code}
     Nothing ->
      case matchRecog (mtchAfterEqToConst d) prs of
       Just (pre,(((Equal (Var x') k)),_),post)
        -> let
            x = init x'
            e = Equal (Var x) k
            stop     = ( psimp d $ mkImp e (mkNot c)
                       , a
                       , diff )
            continue = ( psimp d $ mkImp e c
                       , mkSeq a
                             (mkSeq (PSub pB [(x,k)])
                                   w)
                       , diff )
           in lcred "obs'-;-*-prop" [continue,stop]
       Nothing -> Nothing
\end{code}

Other cases, do nothing:
\begin{code}
creduceUTCP d mpr = Nothing
\end{code}


\begin{code}
lawsUTCPDict :: Dict
lawsUTCPDict
 = makeDict
    [ ( "laws"
      , LawEntry [reduceUTCP] [creduceUTCP] [])
    ]
\end{code}
