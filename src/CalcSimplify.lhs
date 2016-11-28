\HDRa{Calculator Simplification}\label{ha:calc-simp}
\begin{code}
module CalcSimplify where
import Data.List
import CalcTypes
import CalcAlphabets
import CalcPredicates
import CalcSysTypes
\end{code}

\begin{code}
import Debug.Trace
dbg str x = trace (str++show x) x
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
we return a \texttt{RWResult} --- either nothing
or Just a triple of a string, a predicate,
plus a boolean indicator if the top-level changed.
The string supplies a (short ?!) justification/explanation
for what has happened.



\HDRb{Expression Simplification}


The top-level expression simplifier.
\begin{code}
esimp :: Dict -> Expr -> (Bool, Expr)
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
esimps :: Dict -> Bool -> [Expr]-> [Expr] -> (Bool, [Expr])
esimps d chgd se [] = (chgd, reverse se)
esimps d chgd se (e:es)
 = let (chgd',e') = esimp d e
   in esimps d (chgd||chgd') (e':se) es
\end{code}

\HDRc{Function Simplification}~
\begin{code}
asimp :: Dict -> String -> (Bool,[Expr]) -> (Bool, Expr)
asimp d fn (chgd,es)
 = case elookup fn d of
     Nothing  ->  (chgd, App fn es)
     Just (ExprEntry _ _ _ evalf _)
       -> case evalf d es of
            ( "", _ )  ->  (chgd, App fn es)
            ( _, e)    ->  (diff, e)
\end{code}

\HDRc{Substitution Simplification}~
\begin{code}
ssimp :: Dict -> Substn -> (Bool,Substn)
ssimp d subs
 = let
    (vs,es) = unzip subs
    (chgd,es') = esimps d False [] es
   in (chgd, zip vs es')
\end{code}

\HDRc{Expression Substitution}~
\begin{code}
esubst :: Substn -> Expr -> (Bool, Expr)
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
vsubst :: Substn -> String -> (Bool, Expr)
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
subcomp :: Substn -> Substn -> Substn
subcomp sub2 sub1
 = subsub++newsub
 where
   subsub = map (vesubst sub2) sub1
   vs' = map fst sub1
   newsub = filter (not . covered vs') sub2
   covered vs' (v,e) = v `elem` vs'

vesubst :: Substn -> (String, Expr) -> (String, Expr)
vesubst sub (v,e) = (v,snd $ esubst sub e)
\end{code}



\HDRb{Predicate Simplification}\label{hb:simplify}

Now, the predicate simplifier:
\begin{code}
simplified = "simplify"
simplify :: Dict -> Mark -> MPred -> Maybe (BeforeAfter)
\end{code}

\HDRc{Atomic Simplifier}\label{hc:simplify-atomic}

For atomic predicates,
we simplify the underlying expression,
and lift any variable booleans to their predicate equivalent.
\begin{code}
simplify d m mbefore@(Atm e,mt)
 = case esimp d e of
    (chgd,B True)   ->  atmBeforeAfter T        chgd
    (chgd,B False)  ->  atmBeforeAfter F        chgd
    (chgd,e')       ->  atmBeforeAfter (Atm e') chgd
 where
  atmBeforeAfter after chgd
   | chgd       =  Just ( addMark m mbefore
                        , simplified
                        , addMark m (after,mt) )
   | otherwise  =  Nothing
\end{code}

\HDRc{Equality Simplifier}\label{hc:simplify-equal}

For equality we simplify both expressions,
and then attempt to simplify the equality to true or false.
\begin{code}
simplify d m mpr@(Equal e1 e2, mt)
 = let
    (chgd1,e1') = esimp d e1
    (chgd2,e2') = esimp d e2
    (chgd',pr') = sEqual d e1' e2'
    chgd = chgd1 || chgd2 || chgd'
   in if chgd then Just ( addMark m mpr
                        , simplified
                        , addMark m (pr', mt) )
              else Nothing
\end{code}

\newpage
\HDRc{Composite Simplifier}\label{hc:simplify-comp}

For composites,
we first simplify the components,
and then look in the dictionary by name for a simplifier.
\begin{code}
simplify d m mpr@(pr@(Comp name prs), mt@(MT ms mts))
 = let
    (subchgs,befores,afters) = subsimp same [] [] $ zip prs mts
    mcomppr' = compsimp $ map fst afters
   in case mcomppr' of
    Nothing
     -> assemble (Comp name $ map fst afters)
                 (unzip befores) (unzip afters)
                 subchgs False
    Just (what,comppr',topchgd)
     -> assemble comppr'
                 (unzip befores) (unzip afters)
                 (subchgs||topchgd) topchgd
 where

   subsimp chgd befores afters []
    = ( chgd, reverse befores, reverse afters )
   subsimp chgd befores afters  (mpr:mprs)
    =  case simplify d m mpr of
        Nothing -> subsimp chgd (mpr:befores) (mpr:afters)  mprs
        Just (before,what,after)
         -> subsimp diff (before:befores) (after:afters) mprs
\end{code}
\textbf{WARNING: }
\textit{the \texttt{psimp} simplifier below must not call \texttt{simplify}!
To do so risks an infinite loop.
}
\begin{code}
   compsimp prs'
    = case plookup name d of
       Just (PredEntry _ _ _ _ psimp)  ->  psimp d prs'
       _                               ->  Nothing
\end{code}
Assembling the result:
\begin{code}
   assemble _ _ _ False _ = Nothing
   assemble top' (befores, mbef) (afters, maft) _ False
    = Just ( (Comp name befores, MT ms mbef)
           , simplified
           , (Comp name afters, MT ms maft) )
   assemble top' (befores, mbef) (afters, maft) _ True
    = Just ( addMark m (Comp name befores, MT ms mbef)
           , simplified
           , addMark m $ buildMarks top' )
\end{code}

\newpage
\HDRc{Predicate Substitution Simplifier}\label{hc:simplify-pred-subst}

For predicate substitutions,
we first simplify the substitution part,
and then
make a distinction between predicate variables and nullary composites
on the one hand,
and composites of at least one component on the other.
\begin{code}
simplify d m mpr@(PSub spr subs, mt@(MT ms [smt]))
 = case simplify d m (spr, smt) of
    Nothing -> sbstsimp subs' smt spr
    Just (mpr',what,(spr',smt'))
     -> if null what then sbstsimp subs' smt spr
                     else sbstsimp subs' smt' spr'
 where
  subs' = ssimp d subs
\end{code}
For predicate variables,
we look to see if we have information about their alphabets,
which can be used to remove some elements from the substitution.
\RLEQNS{
   P[\vec e/\vec x] &=& P[\vec e/\vec x]\!|_{\alpha P}
   & \elabel{pvar-substn}
}
\begin{code}
  sbstsimp (subchgd,subs') smt spr@(PVar p)
   = case plookup p d of
      Just (PredEntry _ _ alf _ _)
       -> Just ( addMark m mpr
               , "pvar-substn"
               , addMark m
                  ( mkPSub spr
               -- should check that filter below makes a change!
                      $ filter ((`elem` alf) . fst) subs'
                  , mt ) )
      _ -> Nothing
\end{code}
Nullary composites are treated the same:
\begin{code}
  sbstsimp (subchgd,subs') smt spr@(Comp p [])
   = case plookup p d of
      Just (PredEntry _ _ alf _ _)
       -> Just ( addMark m mpr
               , "null-comp-substn"
               , addMark m
                   ( mkPSub spr
               -- should check that filter below makes a change!
                        $ filter ((`elem` alf) . fst) subs'
                   , mt ) )
      _ -> Nothing
\end{code}

\emph{Non-nullary composites require us to simplify sub-parts
and then drive substition in if the comp is substitutable
(need to call \texttt{psubst} a bit more than we do)}

In the general case,
we simplify both predicate and substitution parts,
and combine
\begin{code}
  sbstsimp (subschgd,subs') smt spr
   = let (topchgd,mpr'@(npr',nmt'))
           = psubst m d subs' (spr,smt)
     in assemble npr' (spr,smt) mpr' subs'
                 (subschgd||topchgd) topchgd
   where
    assemble _ _ _ _ False _ = Nothing
    assemble top' (before, mbef) (after, maft) subs' _ False
     = Just ( (mkPSub before subs', MT ms [mbef])
            , simplified
            , (mkPSub after subs', MT ms [maft]) )
    assemble top' (before, mbef) (after, maft) subs'  _ True
     = Just ( addMark m (mkPSub before subs', MT ms [mbef])
            , simplified
            , addMark m $ buildMarks top' )
\end{code}
All other cases are as simple as can be, considering\ldots
\begin{code}
simplify _ _ _ = Nothing
\end{code}

Sometimes we want to simply a \texttt{Pred} without any fuss:
\begin{code}
psimp :: Dict -> Pred -> Pred
psimp d pr
 = case simplify d 0 $ buildMarks pr of
     Just (_,_,(pr',_))  ->  pr'
     Nothing             ->  pr
\end{code}

\HDRd{Simplify ``Double-Tap''}

It is often worth running simplify twice!
\begin{code}
simplify2 :: Dict -> Mark -> MPred -> Maybe (BeforeAfter)
simplify2 d m mpr
 = case simplify d m mpr of
    Nothing -> Nothing
    Just simp1@(before,what1,middle)
     -> case simplify d m middle of
         Nothing -> Just simp1
         Just simp2@(_,     what2,after )
          -> Just (before,what1,after)
\end{code}

\newpage
\HDRc{Equality Predicate Simplification}~
\begin{code}
sEqual :: Dict -> Expr -> Expr -> (Bool, Pred)

sEqual d St St  = (same, Equal St St) -- can't decide this now

sEqual d (B t1) (B t2)
 | t1 == t2   =  (diff,T)
 | otherwise  =  (diff,F)

sEqual d (Z i1) (Z i2)
 | i1 == i2   =  (diff,T)
 | otherwise  =  (diff,F)

sEqual d (Var v1) (Var v2)
 | v1 == v2   = (diff,T)

sEqual d St    (B _) = (diff,F)
sEqual d (B _) St    = (diff,F)
sEqual d (Z _) St    = (diff,F)
sEqual d St    (Z _) = (diff,F)
sEqual d (Z _) (B _) = (diff,F)
sEqual d (B _) (Z _) = (diff,F)

sEqual d e1@(App nm1 args1) e2@(App nm2 args2)
 | nm1 == nm2
    = case elookup nm1 d of
       Nothing  ->  (same,Equal e1 e2)
       (Just ed)
        -> case (isEqual ed) d args1 args2 of
            Nothing     ->  (same,Equal e1 e2)
            Just True   ->  (diff,T)
            Just False  ->  (diff,F)

sEqual d e1 e2
 | e1 == e2   =  (diff,T)
 | otherwise  =  (same,Equal e1 e2)
\end{code}


\newpage
\HDRc{Predicate Substitution}

We note that some constructs
cannot be substituted into until their definitions are expanded.

\begin{code}
psubst :: Mark -> Dict -> Substn -> MPred
       -> (Bool, MPred)

psubst _ d _ mpr@(T,_) = (diff,mpr)
psubst _ d _ mpr@(F,_) = (diff,mpr)

psubst _ d sub (Equal e1 e2, mt)
 = let
     (ediff1, e1') = (esubst sub e1)
     (ediff2, e2') = (esubst sub e2)
   in (ediff1||ediff2, (Equal e1' e2', mt))

psubst _ d sub (Atm e, mt)
 = let (ediff, e') = esubst sub e
   in  (ediff, (Atm e', mt))

psubst m d sub mpr@(pr@(Comp name prs), mt@(MT ms mts))
 | canSub sub d name
    = let (chgd,mprs') = pssubst m d sub $ zip (prs) mts
          (prs',mts')  = unzip mprs'
      in (chgd, addMark m ( Comp name prs', MT ms mts' ) )
 | otherwise = (same, (PSub pr sub, MT [] [mt]))
-- we need subcomp here, unlike in expression substitution,
-- because psubst can return a PSub
psubst m d sub (PSub pr sub', MT ms [smt])
 = psubst m d (subcomp sub sub') (pr, smt)

-- -- the rest are non-substitutable (n.s.)
psubst m d sub (pr, mt)  =  (same, (mkPSub pr sub, MT [] [mt]))
\end{code}
Handling lists of predicates:
\begin{code}
pssubst :: Mark -> Dict -> Substn -> [MPred]
        -> (Bool, [MPred])
pssubst m d _ [] = (same,[])
pssubst m d sub (mpr:mprs)
 = let
    (pdiff, mpr') = psubst m d sub mpr
    mpr'' = if pdiff then addMark m mpr' else mpr'
    (psdiff, mprs') = pssubst m d sub mprs
   in (pdiff||psdiff, mpr'':mprs')
\end{code}

\newpage
We sometimes need to know when we can substitute:
\begin{code}
canSub :: Substn -> Dict -> String -> Bool
canSub subs d name
 = case plookup name d of
    Just (PredEntry cansub _ _ _ _)
       ->  cansub == anyVars || null (map fst subs \\ cansub)
    _  ->  False

substitutable :: Dict -> MPred -> Bool
substitutable d (Comp name _,_)
 = case plookup name d of
    Just (PredEntry cansub _ _ _ _)  ->  not $ null cansub
    _                                ->  False
substitutable _ _ = True
\end{code}

\newpage
\HDRb{Invariant Checking}\label{hb:inv-check}

We will generally have a list of invariants to check:
\begin{code}
chkInvariants :: Dict
             -> InvState
             -> Mark
             -> MPred
             -> Maybe (BeforeAfter)

chkInvariants d [] m mpr = Nothing

chkInvariants d ((ichk,inv):invrest) m mpr
 = case chkInvariant (ichk d inv) m mpr of
    Nothing  ->  chkInvariants d invrest m mpr
    Just (before, what, after)
     -> case chkInvariants d invrest m after of
          Nothing  ->  Just (before, what, after)
          Just (_,what',after')
           -> Just (before,what',after')

\end{code}

\newpage
We explore the current predicate,
bottom-up, like simplify,
except we have a fixed simplification function
and we don't enter expressions or go under substitutions.
\begin{code}
chkInvariant :: (Pred -> Maybe Bool)
             -> Mark
             -> MPred
             -> Maybe (BeforeAfter)

chkInvariant chk m mpr@(pr@(Comp name prs), mt@(MT ms mts))
 = let
    (subchgs,befores,afters) = subchk same [] [] $ zip prs mts
    pr' = Comp name $ map fst afters
   in case chk pr' of
    Nothing
     -> assemble "inv-chk : applicable deeper" pr'
                 (unzip befores) (unzip afters)
                 subchgs False
    Just True
     -> assemble "inv-chk : TRUE" pr'
                 (unzip befores) (unzip afters)
                 True True
    Just False
     -> assemble "inv-chk : FALSE" F
                 (unzip befores) ([],[])
                 True True
 where

   subchk chgd befores afters []
    = ( chgd, reverse befores, reverse afters )
   subchk chgd befores afters  (mpr:mprs)
    =  case chkInvariant chk m mpr of
        Nothing -> subchk chgd (mpr:befores) (mpr:afters)  mprs
        Just (before,what,after)
         -> subchk diff (before:befores) (after:afters) mprs

   assemble _ _ _ _ False _ = Nothing
   assemble what _ (befores, mbef) (afters, maft) _ False
    = Just ( (Comp name befores, MT ms mbef)
           , what
           , (Comp name afters, MT ms maft) )
   assemble what top' (befores, mbef) (afters, maft) _ True
    = Just ( addMark m (Comp name befores, MT ms mbef)
           , what
           , addMark m $ buildMarks top' )

chkInvariant chk m mpr = Nothing
\end{code}
