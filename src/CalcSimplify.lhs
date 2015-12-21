\HDRa{Calculator Simplification}\label{ha:calc-simp}
\begin{code}
module CalcSimplify where
import CalcTypes
import CalcPredicates
\end{code}


\HDRb{Introduction}

Predicate simplification
does not use the recursive predicate search just described,
but instead is a recursive descent,
where sub-components at any level are simplified first,
and then that level is simplified using predicate variant-specific rules
(like (\texttt{sImp} mentioned above).

\HDRc{Preliminaries}

At the top-level,
when we attempt to apply some rule,
we return a \texttt{RWResult} --- a pairing of a string with a predicate.
If the string is empty, then no change occurred,
otherwise it supplies a (short ?!) justification/explanation
for what has happened.


For convenience,
the expression simplification functions return a pair with the string
replaced by a predicate that is true if a change occurred.
\begin{code}
diff, same :: Bool
diff = True
same = False
\end{code}


\HDRb{Expression Simplification}


The top-level expression simplifier.
\begin{code}
esimp :: (Eq s, Ord s, Show s) => Dict m s -> Expr s -> (Bool, Expr s)
esimp d (App fn es) = asimp d fn $ esimps d same [] es
esimp d esub@(Sub e subs)
 = let
    (ediff,e') = esimp d e
    (subsdiff,subs') = ssimp d subs
    (topdiff,esub') = esubst subs' e'
   in (ediff||subsdiff||topdiff, esub)
esimp d e = (same, e)
\end{code}

Simplifying lists of expressions:
\begin{code}
esimps :: (Eq s, Ord s, Show s)
       => Dict m s -> Bool -> [Expr s]-> [Expr s] -> (Bool, [Expr s])
esimps d chgd se [] = (chgd, reverse se)
esimps d chgd se (e:es)
 = let (chgd',e') = esimp d e
   in esimps d (chgd||chgd') (e:se) es
\end{code}

\HDRc{Function Simplification}~
\begin{code}
asimp :: (Eq s, Ord s, Show s)
      => Dict m s -> String -> (Bool,[Expr s]) -> (Bool, Expr s)
asimp d fn (chgd,es)
 = case elookup fn d of
     Nothing  ->  (chgd, App fn es)
     Just (ExprEntry _ _ evalf)
       -> case evalf d es of
            ( "", _ )  ->  (chgd, App fn es)
            ( _, e)    ->  (diff, e)
\end{code}

\HDRc{Substitution Simplification}~
\begin{code}
ssimp :: (Eq s, Ord s, Show s) => Dict m s -> Substn s -> (Bool,Substn s)
ssimp d subs
 = let
    (vs,es) = unzip subs
    (chgd,es') = esimps d False [] es
   in (chgd, zip vs es')
\end{code}

\HDRc{Expression Substitution}~
\begin{code}
esubst :: Ord s => Substn s -> Expr s -> (Bool, Expr s)
esubst sub (Var v) =  vsubst sub v
esubst sub (App fn es)
 = let (esdiff, es') = essubst sub es
   in  (esdiff, App fn es')
esubst sub (Sub e sub')
 = let
    (diff1,e1) = esubst sub' e
    (diff2,e2) = esubst sub e1
   in (diff1||diff2, e2)
esubst sub e = (same, e)

essubst _ [] = (same,[])
essubst sub (e:es)
 = let
    (ediff, e') = esubst sub e
    (esdiff, es') = essubst sub es
   in (ediff||esdiff, e':es')
\end{code}

\HDRc{Variable Substitution}~
\begin{code}
vsubst :: Substn s -> String -> (Bool, Expr s)
vsubst [] v = (same, Var v)
vsubst ((u,e):subs) v
 | u == v  =  (diff, e)
 | otherwise  =  vsubst subs v
\end{code}

\HDRb{Substitution composition}

We can define it as follows, where common target variables ($x_i$) are listed
first in each w.l.o.g.:
\begin{eqnarray*}
   \lefteqn{[e_1,\ldots,e_c,e_{c+1},\ldots,e_{c+m}
            /x_1,\ldots,x_c,y_1,\ldots,y_m]}
\\ \lefteqn{~[f_1,\ldots,f_c,f_{c+1},\ldots,f_{c+n}
            /x_1,\ldots,x_c,z_1,\ldots,z_n]}
\\ &\defs& [ e_1\rho,\ldots,e_c\rho,e_{c+1}\rho,\ldots,e_{c+m}\rho
           ~,~
             f_{c+1},\ldots,f_{c+n}
           / x_1,\ldots,x_c,y_1,\ldots,y_m
           ~,~
             z_1,\ldots,z_n]
\\ &=& \mathit{zip}~ v~ (v\sigma\rho)
\\ && \WHERE
\\ && \rho = [f_1,\ldots,f_c,f_{c+1},\ldots,f_{c+n}
             /x_1,\ldots,x_c,z_1,\ldots,z_n]
\\ && \sigma = [e_1,\ldots,e_c,e_{c+1},\ldots,e_{c+m}
               /x_1,\ldots,x_c,y_1,\ldots,y_m]
\\ && v = \seqof{x_1,\ldots,x_c,y_1,\ldots,y_m
                ,
                z_1,\ldots,z_n}
\end{eqnarray*}
\begin{code}
subcomp :: Ord s => Substn s -> Substn s -> Substn s
subcomp sub2 sub1
 = subsub++newsub
 where
   subsub = map (vesubst sub2) sub1
   vs' = map fst sub1
   newsub = filter (not . covered vs') sub2
   covered vs' (v,e) = v `elem` vs'

vesubst :: Ord s => Substn s -> (String, Expr s) -> (String, Expr s)
vesubst sub (v,e) = (v,snd $ esubst sub e)
\end{code}



\HDRb{Predicate Simplification}


\HDRc{Simplify}\label{hc:simplify}

Now, the predicate simplifier:
\begin{code}
simplified = "simplify"
simplify :: (Mark m, Ord s, Show s)
         => Dict m s -> m -> MPred m s -> BeforeAfter m s
\end{code}
For atomic predicates,
we simplify the underlying expression,
and lift any variable booleans to their predicate equivalent.
\begin{code}
simplify d m mpr@(ms,pr@(Atm e))
 = case esimp d e of
    (chgd,B True)   ->  mkCR pr T        ms simplified m chgd
    (chgd,B False)  ->  mkCR pr F        ms simplified m chgd
    (chgd,e')       ->  mkCR pr (Atm e') ms simplified m chgd
\end{code}
For equality we simplify both expressions,
and then attempt to simplify the equality to true or false.
\begin{code}
simplify d m mpr@(ms,(Equal e1 e2))
 = let
    (chgd1,e1') = esimp d e1
    (chgd2,e2') = esimp d e2
    (chgd',pr') = sEqual e1' e2'
    chgd = chgd1 || chgd2 || chgd'
   in if chgd then (addMark m mpr, simplified, addMark m (ms,pr'))
              else (mpr,"",mpr)
\end{code}
For composites,
we first simplify the components,
and then look in the dictionary by name for a simplifier.
\begin{code}
simplify d m mpr@(ms,pr@(Comp name mprs))
 = let
    (subchgs,befores,afters) = subsimp d m same [] [] mprs
    (what,comppr') = compsimp d m name afters
    topchgd = not $ null what
   in assemble mpr comppr' (Comp name) befores afters
              ms simplified m (subchgs||topchgd) topchgd
 where

   subsimp d m chgd befores afters []
    = ( chgd, reverse befores, reverse afters )
   subsimp d m chgd befores afters  (mpr:mprs)
    = let (before,what,after) = simplify d m mpr
      in if null what
       then subsimp d m chgd (mpr:befores) (mpr:afters)  mprs
       else subsimp d m diff (before:befores) (after:afters) mprs
\end{code}
\textbf{WARNING: }
\textit{the \texttt{psimp} simplifier below must not call \texttt{simplify}!
To do so risks an infinite loop.
}
\begin{code}
   compsimp d m name mprs'
    = case plookup name d of
       Just (PredEntry _ _ _ psimp)  ->  psimp d mprs'
       _                             ->  ("",Comp name mprs')
\end{code}
Assembling the result:
\begin{code}
   assemble orig top' compN befores afters ms what m False _
    = ( orig, "", orig )
   assemble orig top' compN befores afters ms what m _ False
    = ( (ms,compN befores), what, (ms,compN afters) )
   assemble orig top' compN befores afters ms what m _ True
    = ( addMark m (ms,compN befores)
      , what, addMark m (ms,top') )
\end{code}
For predicate substitutions,
we first simplify the substitution part,
and them
make a distinction between predicate variables,
and general predicates.
\begin{code}
simplify d m mpr@(ms,(PSub spr subs))
 = sbstsimp d m ms (ssimp d subs) spr
 where
\end{code}
For predicate variables,
we look to see if we have information about their alphabets,
which can be used to remove some elements from the substitution.
\RLEQNS{
   P[\vec e/\vec x] &=& P[\vec e/\vec x]\!|_{\alpha P}
   & \elabel{pvar-substn}
}
\begin{code}
  sbstsimp d m ms (subchgd,subs') spr@(mp,PVar p)
   = case vlookup p d of
      Just (AlfEntry alf)
       -> ( addMark m mpr
          , ""
          , addMark m
             (ms,mkPSub spr $ filter ((`elem` alf) . fst) subs'))
      _ -> (mpr,"",mpr)
\end{code}
In the general case,
we simplify both predicate and substitution parts,
and combine.
\begin{code}
  sbstsimp d m ms (subschgd,subs') spr
   = let
      (before,what,after) = simplify d m spr
      predchgd = not $ null what
      (topchgd,npr') = psubst m d subs' after
     in assemble mpr npr' before after subs'
                ms simplified m
                (subschgd||topchgd||predchgd) topchgd
   where
    assemble orig top'  before after subs' ms what m False _
     = (orig, "", orig)
    assemble orig top' before after subs' ms what m _ False
     = ((ms,mkPSub before subs'), what, (ms,mkPSub after subs'))
    assemble orig top' before after subs' ms what m _ True
     = ( addMark m (ms,mkPSub before subs')
       , what, addMark m (ms,top') )
\end{code}
All other cases are as simple as can be, considering\ldots
\begin{code}
simplify d m mpr@(ms,pr) = ( mpr, "", mpr)
\end{code}

\HDRc{Equality Predicate Simplification}~
\begin{code}
sEqual :: Eq s => Expr s -> Expr s -> (Bool, Pred m s)

sEqual (St s1) (St s2)
 | s1 == s2     = (diff,T)
 | otherwise    = (diff,F)

sEqual (B t1) (B t2)
 | t1 == t2   =  (diff,T)
 | otherwise  =  (diff,F)

sEqual (Z i1) (Z i2)
 | i1 == i2   =  (diff,T)
 | otherwise  =  (diff,F)

sEqual (Var v1) (Var v2)
 | v1 == v2   = (diff,T)

sEqual (St _) (B _) = (diff,F)
sEqual (B _) (St _) = (diff,F)
sEqual (Z _) (St _) = (diff,F)
sEqual (St _) (Z _) = (diff,F)
sEqual (Z _)  (B _) = (diff,F)
sEqual (B _)  (Z _) = (diff,F)

sEqual e1 e2
 | e1 == e2   =  (diff,T)
 | otherwise  =  (same,Equal e1 e2)
\end{code}


\newpage
\HDRc{Predicate Substitution}

We note that some constructs
cannot be substituted into until their definitions are expanded.

\begin{code}
psubst :: (Ord s, Mark m)
       => m -> Dict m s -> Substn s -> MPred m s
       -> (Bool, Pred m s)

psubst m d _ (_,T) = (diff,T)
psubst m d _ (_,F) = (diff,F)

psubst m d sub (_,Equal e1 e2)
 = let
     (ediff1, e1') = (esubst sub e1)
     (ediff2, e2') = (esubst sub e2)
   in (ediff1||ediff2, Equal e1' e2')

psubst m d sub (_,Atm e)
 = let (ediff, e') = esubst sub e
   in  (ediff, Atm e')

psubst m d sub (_,Comp name mprs)
 | canSub d name
    = let (_, mprs') = pssubst m d sub mprs
      in  (diff, Comp name mprs')

-- we need subcomp here, unlike in expression substitution,
-- because psubst m d can return a PSub
psubst m d sub (_,PSub mpr sub')
                            = psubst m d (subcomp sub sub') mpr

-- -- the rest are non-substitutable (n.s.)
psubst m d sub mpr@(_,pr)  =  (same, mkPSub mpr sub)
\end{code}
Handling lists of predicates:
\begin{code}
pssubst :: (Ord s, Mark m)
        => m -> Dict m s -> Substn s -> [MPred  m s]
        -> (Bool, [MPred m s])
pssubst m d _ [] = (same,[])
pssubst m d sub (mp@(ms,p):mps)
 = let
    (pdiff, p') = psubst m d sub mp
    mp' = (ms,p')
    mmp = if pdiff then addMark m mp' else mp'
    (psdiff, mps') = pssubst m d sub mps
   in (pdiff||psdiff, mp':mps')

\end{code}

\newpage
We sometimes need to know when we can substitute:
\begin{code}
canSub :: Dict m s -> String -> Bool
canSub d name
 = case plookup name d of
     Just (PredEntry cansub _ _ _)  ->  cansub
     _                              ->  False
     
substitutable :: Dict m s -> MPred m s -> Bool
substitutable d (_,Comp name _)
 = case plookup name d of
    Just pe@(PredEntry cansub _ _ _)  -> cansub
    _ -> False
substitutable _ _ = True
\end{code}
