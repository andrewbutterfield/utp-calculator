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
import UTCPLaws
import UTCPCReduce
import UTCPCalc
\end{code}



\HDRb{Test Objects}


\HDRc{Test Variables}

\begin{code}
x = "x" ; vx = Var x ; px = atm vx
y = "y" ; vy = Var y ; py = atm vy
z = "z" ; vz = Var z ; pz = atm vz
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
xandy = bAnd [px,py]
xory = bOr [px,py]
sub42 :: Ord s => MPred s
sub42 = psub xandy x42

xeqy = equal vx vy

hasF = [px,py,false,pz]
hasT = [py,true,pz,px]
hasFT = [false,px,true,pz]
hasNone = [pz,py,px]

orF = bOr hasF
andT = bAnd hasT
xorF = bOr [bOr hasNone,orF]
xandT = bAnd [andT,bAnd hasNone]
bigOr = bOr [xorF,xandT,bAnd hasFT]
bigAnd = bAnd [xorF,xandT,bOr hasFT]
\end{code}

\HDRb{Test Functions}
\begin{code}
test ipr      = simplify stdDict 42 ipr
rtest (_,ipr) = simplify stdDict 99 ipr
\end{code}

Marking and displaying tests:
\begin{code}
marked :: MPred ()
marked = addMark 42
       $ bAnd [ addMark 1 $ atm $ Z 1
              , addMark 2 $ atm $ Z 2
              , addMark 3 $ atm $ Z 3
              , addMark 4 $ atm $ Z 4
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
notImpFalse :: Dict s -> [MPred s] -> (String, Pred s)
notImpFalse _ [mpr] = ( "not-ImpFalse", mkImp mpr $ noMark F )
notImpFalse _ mprs = ( "", Comp "Not" mprs )

notIFEntry :: (Show s, Ord s) => (String, Entry s)
notIFEntry
 = ( "Not"
   , PredEntry True ppNot notImpFalse simpNot )
\end{code}
\RLEQNS{
    P \lor Q &\defs& \lnot P \implies Q
}
\begin{code}
orImpFalse :: Dict s -> [MPred s] -> (String, Pred s)
orImpFalse _ [mp,mq]  =  ( "or-ImpFalse", mkImp (noMark $ mkNot mp) mq )
orImpFalse _ mprs     =  ( "", Comp "Or" mprs )

orIFEntry :: (Show s, Ord s) => (String, Entry s)
orIFEntry
 = ( "Or"
   , PredEntry True ppOr orImpFalse simpOr )
\end{code}
\RLEQNS{
   P \ndc Q &\defs& P \lor Q
}
\begin{code}
ndcImpFalse :: Dict s -> [MPred s] -> (String, Pred s)
ndcImpFalse _ [mp,mq]  =  ( "ndc-ImpFalse", mkOr [mp,mq] )
ndcImpFalse _ mprs     =  ( "", Comp "NDC" mprs )

ndcIFEntry :: (Show s, Ord s) => (String, Entry s)
ndcIFEntry
 = ( "NDC"
   , PredEntry True ppNDC ndcImpFalse simpNDC )
\end{code}
\RLEQNS{
   P \land Q &\defs& \lnot(\lnot P \lor \lnot Q)
}
\begin{code}
andImpFalse :: Dict s -> [MPred s] -> (String, Pred s)
andImpFalse _ [mp,mq]
 = ( "and-ImpFalse"
   , mkNot $ noMark $ mkOr [noMark $ mkNot mp, noMark $ mkNot mq] )
andImpFalse _ mprs     =  ( "", Comp "And" mprs )

andIFEntry :: (Show s, Ord s) => (String, Entry s)
andIFEntry
 = ( "And"
   , PredEntry True ppAnd andImpFalse simpAnd )
\end{code}

\begin{code}
impFalseDict :: (Ord s, Show s) => Dict s
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

eqVV = equal (Var "v1") (Var "v2")
eqVK = equal (Var "v1") (Z 42)
eqMV = equal (Var "m1") (Var "v2")
eqMK = equal (Var "m1") (Z 42)
eqPV = equal (Var "p1") (Var "v2")
eqPK = equal (Var "p1") (Z 42)

eqVVthenA = bSeq eqVV pA
eqVKthenA = bSeq eqVK pA
eqMVthenA = bSeq eqMV pA
eqMKthenA = bSeq eqMK pA
eqPVthenA = bSeq eqPV pA
eqPKthenA = bSeq eqPK pA

eqV'V = equal (Var "v1'") (Var "v2")
eqV'K = equal (Var "v1'") (Z 42)
eqM'V = equal (Var "m1'") (Var "v2")
eqM'V' = equal (Var "m1'") (Var "v2'")
eqM'K = equal (Var "m1'") (Z 42)

eqV'VthenA = bSeq eqV'V pA
eqV'KthenA = bSeq eqV'K pA
eqM'VthenA = bSeq eqM'V pA
eqM'KthenA = bSeq eqM'K pA

eqDyn'KthenA
 = bSeq (bAnd $ map eqIt ["m1'","v2'","v1'","m2'"]) pA

eqDuh'KthenA
 = bSeq (bAnd $ map eqIt ["m1'","v2'","m2'"]) pA

aAndeqDny'KthenB
 = bSeq (bAnd $ pA : map eqIt ["m1'","v2'","m2'"]) pB

aAndeqDny'KthenEq
 = bSeq (bAnd $ pA : map eqIt ["m1'","v2'","m2'"]) eqM'V'

eqIt v' = equal (Var v') (Z 42)
\end{code}

\HDRc{Test Laws}

\begin{code}
creduceTest :: CDictRWFun s
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
unrollTst :: Ord s => DictRWFun s
unrollTst d mw@(_,Comp "Iter"  [mc, mpr])
 | isCondition mc
           = ( "loop-unroll"
             , bCond (bSeq mpr mw) mc bSkip )
unrollTst _ mpr = ("", mpr )
\end{code}

\HDRc{Laws Dictionary}

\begin{code}
lawsEntry :: (Ord s, Show s) => (String, Entry s)
lawsEntry = ("laws",LawEntry [reduceStd] [creduceTest] [unrollTst])

lawsDict :: (Ord s, Show s) => Dict s
lawsDict = M.fromList [ lawsEntry ]
\end{code}

\HDRb{Test Calculator}

\HDRc{Test Dictionary}

Test dictionarys
\begin{code}
testDict :: (Ord s, Show s) => Dict s
testDict = dictUTCP
           -- `dictMrg` impFalseDict
           -- `dictMrg` absAlfDict
           -- `dictMrg` lawsDict
           `dictMrg` stdDict
\end{code}

\HDRc{Test Calculator Top-Level}

\begin{code}
calc mpr = calcREPL testDict mpr
putcalc :: (Ord s, Show s) => MPred s -> IO ()
putcalc mpr
  = do res <- calc mpr
       putStrLn "\n\nTRANSCRIPT:"
       putStrLn $ calcPrint res
\end{code}
