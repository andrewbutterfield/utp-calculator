\HDRa{Calculator Tests}\label{ha:calc-test}
\begin{code}
module TestCalc where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
import CalcAlphabets
import CalcSimplify
import CalcRecogniser
import CalcRun
import StdPredicates
import CalcZipper
import CalcSteps
import StdLaws
import UTCPSemantics
\end{code}

\HDRb{Default Mark Type}

We will generally use non-negative \emph{Int} as markers,
with $-1$ representing ``no mark'',
and incrementing being used to generate new marks.
\begin{code}
instance Mark Int where
  startm = 0
  nextm = (+1)
  prevm = subtract 1

type IPred s = MPred Int s
\end{code}

\HDRb{Concrete Builders}

\HDRc{Building Basic Predicates}

\begin{code}
iT, iF :: IPred s
iT = true
iF = false
iPV :: String -> IPred s
iPV = pvar
iEqual :: Expr s -> Expr s -> IPred s
iEqual = equal
iAtm :: Expr s -> IPred s
iAtm = atm
iComp :: String -> [IPred s] -> IPred s
iComp = comp
iPSub :: Ord s => IPred s -> Substn s -> IPred s
iPSub = psub
\end{code}

\HDRc{Building Standard Predicates}

\begin{code}
iTop, iBot, iSkip :: IPred s
iNot :: IPred s -> IPred s
iAnd, iOr, iNDC :: [IPred s] -> IPred s
iImp, iRfdby, iSeq, iIter :: IPred s -> IPred s -> IPred s
iCond :: IPred s -> IPred s -> IPred s -> IPred s

iTop = bTop
iBot = bBot
iNot mpr = noMark $ mkNot mpr
iAnd mprs = noMark $ mkAnd mprs
iOr mprs = noMark $ mkOr mprs
iNDC mprs = noMark $ mkNDC mprs
iImp mpr1 mpr2 = noMark $ mkImp mpr1 mpr2
iRfdby mpr1 mpr2 = noMark $ mkRfdby mpr1 mpr2
iCond mpr1 mpr2 mpr3 = noMark $ mkCond mpr1 mpr2 mpr3
iSkip = noMark mkSkip
iSeq mpr1 mpr2 = noMark $ mkSeq mpr1 mpr2
iIter mpr1 mpr2 = noMark $ mkIter mpr1 mpr2
\end{code}

\HDRb{Test Objects}


\HDRc{Test Variables}

\begin{code}
x = "x" ; vx = Var x ; px = iAtm vx
y = "y" ; vy = Var y ; py = iAtm vy
z = "z" ; vz = Var z ; pz = iAtm vz
\end{code}


\HDRc{Test Expressions}

\HDRc{Test Substitutions}

\begin{code}
x42 = [(x,Z 42)]
y42 = [(y,Z 42)]
y90 = [(y,Z 90)]
\end{code}

\HDRc{Test Predicates}

\begin{code}
xandy = iAnd [px,py]
xory = iOr [px,py]
sub42 :: Ord s => IPred s
sub42 = iPSub xandy x42

xeqy = iEqual vx vy

hasF = [px,py,iF,pz]
hasT = [py,iT,pz,px]
hasFT = [iF,px,iT,pz]
hasNone = [pz,py,px]

orF = iOr hasF
andT = iAnd hasT
xorF = iOr [iOr hasNone,orF]
xandT = iAnd [andT,iAnd hasNone]
bigOr = iOr [xorF,xandT,iAnd hasFT]
bigAnd = iAnd [xorF,xandT,iOr hasFT]
\end{code}

\HDRb{Test Functions}
\begin{code}
test ipr      = simplify stdDict 42 ipr
rtest (_,ipr) = simplify stdDict 99 ipr
\end{code}

Marking and displaying tests:
\begin{code}
marked :: IPred ()
marked = addMark 42
       $ iAnd [ addMark 1 $ iAtm $ Z 1
              , addMark 2 $ iAtm $ Z 2
              , addMark 3 $ iAtm $ Z 3
              , addMark 4 $ iAtm $ Z 4
              ]
mtest m = putStrLn $ pmdshow 80 stdDict (stepshow m) marked
\end{code}

\HDRb{Test Dictionaries}

\HDRc{Implies-False Dictionary}

First, a dictionary that defines negation, conjunction, disjunction
and non-determinisitic choice in a layered way
on top of implication and False.
\RLEQNS{
    \lnot P &\defs& P \implies false
}
\begin{code}
notImpFalse :: Dict m s -> [MPred m s] -> (String, Pred m s)
notImpFalse _ [mpr] = ( "not-ImpFalse", mkImp mpr $ noMark F )
notImpFalse _ mprs = ( "", Comp "Not" mprs )

notIFEntry :: (Show s, Ord s) => (String, Entry m s)
notIFEntry
 = ( "Not"
   , PredEntry True ppNot notImpFalse simpNot )
\end{code}
\RLEQNS{
    P \lor Q &\defs& \lnot P \implies Q
}
\begin{code}
orImpFalse :: Dict m s -> [MPred m s] -> (String, Pred m s)
orImpFalse _ [mp,mq]  =  ( "or-ImpFalse", mkImp (noMark $ mkNot mp) mq )
orImpFalse _ mprs     =  ( "", Comp "Or" mprs )

orIFEntry :: (Eq m, Show s, Ord s) => (String, Entry m s)
orIFEntry
 = ( "Or"
   , PredEntry True ppOr orImpFalse simpOr )
\end{code}
\RLEQNS{
   P \ndc Q &\defs& P \lor Q
}
\begin{code}
ndcImpFalse :: Dict m s -> [MPred m s] -> (String, Pred m s)
ndcImpFalse _ [mp,mq]  =  ( "ndc-ImpFalse", mkOr [mp,mq] )
ndcImpFalse _ mprs     =  ( "", Comp "NDC" mprs )

ndcIFEntry :: (Eq m, Show s, Ord s) => (String, Entry m s)
ndcIFEntry
 = ( "NDC"
   , PredEntry True ppNDC ndcImpFalse simpNDC )
\end{code}
\RLEQNS{
   P \land Q &\defs& \lnot(\lnot P \lor \lnot Q)
}
\begin{code}
andImpFalse :: Dict m s -> [MPred m s] -> (String, Pred m s)
andImpFalse _ [mp,mq]
 = ( "and-ImpFalse"
   , mkNot $ noMark $ mkOr [noMark $ mkNot mp, noMark $ mkNot mq] )
andImpFalse _ mprs     =  ( "", Comp "And" mprs )

andIFEntry :: (Eq m, Show s, Ord s) => (String, Entry m s)
andIFEntry
 = ( "And"
   , PredEntry True ppAnd andImpFalse simpAnd )
\end{code}

\begin{code}
impFalseDict :: (Eq m, Ord s, Show s) => Dict m s
impFalseDict
 = M.fromList
    [ notIFEntry
    , andIFEntry
    , orIFEntry
    , ndcIFEntry
    ]
\end{code}

\HDRc{Abstract Alphabet Dictionary}

\begin{code}
absAlfDict
 = stdAlfDictGen
      ["v1","v2"] -- Script
      ["m1","m2"] -- Model
      ["p1","p2"] -- Static
\end{code}

Now some predicates for this
\begin{code}
pA = noMark $ PVar "A"
pB = noMark $ PVar "B"

eqVV = iEqual (Var "v1") (Var "v2")
eqVK = iEqual (Var "v1") (Z 42)
eqMV = iEqual (Var "m1") (Var "v2")
eqMK = iEqual (Var "m1") (Z 42)
eqPV = iEqual (Var "p1") (Var "v2")
eqPK = iEqual (Var "p1") (Z 42)

eqVVthenA = iSeq eqVV pA
eqVKthenA = iSeq eqVK pA
eqMVthenA = iSeq eqMV pA
eqMKthenA = iSeq eqMK pA
eqPVthenA = iSeq eqPV pA
eqPKthenA = iSeq eqPK pA

eqV'V = iEqual (Var "v1'") (Var "v2")
eqV'K = iEqual (Var "v1'") (Z 42)
eqM'V = iEqual (Var "m1'") (Var "v2")
eqM'V' = iEqual (Var "m1'") (Var "v2'")
eqM'K = iEqual (Var "m1'") (Z 42)

eqV'VthenA = iSeq eqV'V pA
eqV'KthenA = iSeq eqV'K pA
eqM'VthenA = iSeq eqM'V pA
eqM'KthenA = iSeq eqM'K pA

eqDyn'KthenA
 = iSeq (iAnd $ map eqIt ["m1'","v2'","v1'","m2'"]) pA

eqDuh'KthenA
 = iSeq (iAnd $ map eqIt ["m1'","v2'","m2'"]) pA

aAndeqDny'KthenB
 = iSeq (iAnd $ pA : map eqIt ["m1'","v2'","m2'"]) pB

aAndeqDny'KthenEq
 = iSeq (iAnd $ pA : map eqIt ["m1'","v2'","m2'"]) eqM'V'

eqIt v' = iEqual (Var v') (Z 42)
\end{code}

\HDRc{Test Laws}

\begin{code}
creduceTest :: Mark m => CDictRWFun m s
creduceTest d (_,Comp "Imp" [(_,ante),mconsq])
 = ( "discharge assumption"
   , [ ( ante, mconsq )                 -- True  => P  =  P
     , ( mkNot $ noMark ante, true ) ] )  -- False => _  =  True
creduceTest _ mpr = ( "", [] )
\end{code}
Iteration  satisfies the loop-unrolling law:
\[
  c * P  \quad=\quad (P ; c * P ) \cond c \Skip
\]
\begin{code}
unrollTst :: (Ord s, Mark m) => DictRWFun m s
unrollTst d mw@(_,Comp "Iter"  [mc@(_,c), mpr])
 | isCondition c
           = ( "loop-unroll"
             , bCond (bSeq mpr mw) mc bSkip )
unrollTst _ mpr = ("", mpr)
\end{code}

\HDRc{Laws Dictionary}

\begin{code}
lawsEntry :: (Mark m, Ord s, Show s) => (String, Entry m s)
lawsEntry = ("laws",LawEntry [reduceStd] [creduceTest] [unrollTst])

lawsDict :: (Mark m, Ord s, Show s) => Dict m s
lawsDict = M.fromList [ lawsEntry ]
\end{code}

\HDRb{Test Calculator}

\HDRc{Test Dictionary}

The test dictionary
\begin{code}
testDict :: (Eq m, Mark m, Ord s, Show s) => Dict m s
testDict = impFalseDict
           `dictMrg` absAlfDict
           `dictMrg` lawsDict
           `dictMrg` stdDict
\end{code}

\HDRc{Test Calculator Top-Level}

\begin{code}
calc mpr = calcREPL testDict mpr
putcalc :: (Mark m, Eq m, Show m, Ord s, Show s) => MPred m s -> IO ()
putcalc mpr
  = do res <- calc mpr
       putStrLn "\n\nTRANSCRIPT:"
       putStrLn $ calcPrint res
\end{code}
