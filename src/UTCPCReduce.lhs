\HDRa{UTCP Conditional Reducer}\label{ha:UTCP-cond:reduce}
\begin{code}
module UTCPCReduce where
import qualified Data.Map as M
import CalcTypes
import CalcAlphabets
import CalcPredicates
import CalcSimplify
import CalcSteps
import CalcRecogniser
import StdPredicates
import UTCPSemantics
import UTCPLaws
\end{code}

To avoid having to support a wide range of expression-related theories,
we provide a conditional reducer, that computes
a number of alternative outcomes, each guarded by some predicate
that is hard to evaluate.
The user elects which one to use by checking the conditions manually.

\begin{code}
creduceUTCP :: (Show s, Ord s) => CDictRWFun s
\end{code}

\HDRc{pre- and before-substitutions}
A pre-substitution is one that replaces undashed variables with
undashed expressions, while a before-substitution is further restricted
to replacing undashed observables only.
\begin{code}
preSublet :: Ord s => ( String, Expr s ) -> Bool
preSublet (v,e) = notDash v && notDashed e

preSub :: Ord s => Substn s -> Bool
preSub = all preSublet

beforeSublet :: Ord s => Dict s -> ( String, Expr s ) -> Bool
beforeSublet d (v,e) = isDyn d v && notDashed e

beforeSub :: Ord s => Dict s -> Substn s -> Bool
beforeSub d = all (beforeSublet d)
\end{code}

\HDRc{Predicate Simplifier}
 Sometimes we want to simplify a predicate without fuss
(marking or comment):
\begin{code}
psimp :: (Ord s, Show s)
      => Dict s -> MPred s -> Pred s
psimp d = snd . thd . simplify d startm

thd (_,_,z) = z
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
creduceUTCP d (_,PSub (_,Comp "PAtm" [pA])
                      [("in",l0),("out",l1),("ls",ns)] )
 = lcred "atm-substn" [doA,nowt]
 where
   nsl0 = atm $ subset l0 ns
   doA  = ( psimp d nsl0
          , bAnd [pA, equal ls' $ sswap ns l0 l1 ] )
   nowt = ( psimp d $ bNot nsl0
          , false )
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
creduceUTCP d (_,PSub w@(_,Comp "Iter" [c,p]) sub)
 | isCondition c && beforeSub d sub
 = lcred "loop-substn" [ctrue,cfalse]
 where
   csub = psub c sub
   ctrue  = ( psimp d csub
            , bSeq (psub p sub) w )
   cfalse = ( psimp d $ bNot csub
            , psub bSkip sub )
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
creduceUTCP d (_,PSub (_,Comp "Cond" [c,p,q]) sub)
 | isCondition c && preSub sub
 = lcred "cond-substn" [ctrue,cfalse]
 where
   csub = psub c sub
   ctrue  = ( psimp d csub
            , psub p sub)
   cfalse = ( psimp d $ bNot csub
            , psub q sub )
\end{code}

\HDRc{Boolean followed by iteration}

Provided $\fv{b'} \subseteq \setof{s',ls'}$, $x'$ is an observation, and $k$ is ground
\begin{code}
creduceUTCP d mpr@(_,Comp "Seq" [ a@(_,Comp "And" prs)
                                , w@(_,Comp "Iter" [c,pB]) ])
 | isCondition c

\end{code}
\RLEQNS{
   (b \implies c)       &\implies& A \land b' ; c * B = (A ; b \land B) ; c * B
\\ (b \implies \lnot c) &\implies& A \land b' ; c * B = A \land b'
}
\begin{code}
   = case matchRecog (isDashedObsExpr d) prs of
     Just (pre,(_,Atm e'),post)
      -> let
          e = atm $ unDash e'
          continue = ( psimp d $ bImp e c
                     , bSeq (bSeq (bAnd (pre++post)) (bAnd [e, pB])) w)
          stop     = ( psimp d $ bImp e (bNot c)
                     , a )
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
      case matchRecog (isAfterEqToConst d) prs of
       Just (pre,(_,Equal (Var x') k),post)
        -> let
            x = init x'
            e = equal (Var x) k
            stop     = ( psimp d $ bImp e (bNot c)
                       , a )
            continue = ( psimp d $ bImp e c
                       , bSeq a
                             (bSeq (psub pB [(x,k)])
                                   w ))
           in lcred "obs'-;-*-prop" [continue,stop]
       Nothing -> lcred "" [(T,mpr)]
\end{code}

Other cases, do nothing:
\begin{code}
creduceUTCP d mpr = lcred "" [(T,mpr)]

lcred nm cmprs = ( nm, cmprs )
\end{code}


\begin{code}
lawsUTCPDict :: (Ord s, Show s) => Dict s
lawsUTCPDict
 = M.fromList
    [ ( "laws"
      , LawEntry [reduceUTCP] [creduceUTCP] [])
    ]
\end{code}
