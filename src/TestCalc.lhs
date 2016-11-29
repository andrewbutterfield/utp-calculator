\HDRa{Calculator Tests}\label{ha:calc-test}
\begin{code}
module TestCalc where
import Utilities
import Data.List
import Data.Char
import Data.Maybe
import Debug.Trace
import PrettyPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
import CalcAlphabets
import CalcSysTypes
import CalcSimplify
import CalcRecogniser
import CalcRun
import StdPredicates
import StdLaws
import CalcZipper
import CalcSteps
import StdUTPPredicates
import StdUTPLaws
import UTCPSemantics
import UTCPLaws
import UTCPCReduce
import UTCPCalc
\end{code}

\textbf{\emph{This test file is badly out of date
and won't compile.}}

\HDRb{Test Objects}


\HDRc{Test Variables}

\begin{code}
x = "x" ; vx = Var x ; px = Atm vx
y = "y" ; vy = Var y ; py = Atm vy
z = "z" ; vz = Var z ; pz = Atm vz
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
xandy = mkAnd [px,py]
xory = mkOr [px,py]
sub42 :: Ord s => Pred s
sub42 = PSub xandy x42

xeqy = Equal vx vy

hasF = [px,py,F,pz]
hasT = [py,T,pz,px]
hasFT = [F,px,T,pz]
hasNone = [pz,py,px]

orF = mkOr hasF
andT = mkAnd hasT
xorF = mkOr [mkOr hasNone,orF]
xandT = mkAnd [andT,mkAnd hasNone]
bigOr = mkOr [xorF,xandT,mkAnd hasFT]
bigAnd = mkAnd [xorF,xandT,mkOr hasFT]
\end{code}


\HDRb{Test Dictionaries}

\HDRc{Implies-False Dictionary}

First, a dictionary that defines negation, conjunction, disjunction
and non-deterministic choice in a layered way
on top of implication and False.
\RLEQNS{
    \lnot P &\defs& P \implies false
}
\begin{code}
notImpFalse :: Dict s -> [Pred s] -> RWResult s
notImpFalse _ [pr] = lred "not-ImpFalse" $ mkImp pr F
notImpFalse _ _ = Nothing

notIFEntry :: (Show s, Ord s) => (String, Entry s)
notIFEntry
 = ( "Not"
   , PredEntry subAny ppNot [] notImpFalse simpNot)
\end{code}
\RLEQNS{
    P \lor Q &\defs& \lnot P \implies Q
}
\begin{code}
orImpFalse :: Dict s -> [Pred s] -> RWResult s
orImpFalse _ [p,q]  =  lred "or-ImpFalse" $ mkImp (mkNot p) q
orImpFalse _ _ = Nothing

orIFEntry :: (Show s, Ord s) => (String, Entry s)
orIFEntry
 = ( "Or"
   , PredEntry subAny ppOr [] orImpFalse simpOr )
\end{code}
\RLEQNS{
   P \ndc Q &\defs& P \lor Q
}
\begin{code}
ndcImpFalse :: Dict s -> [Pred s] -> RWResult s
ndcImpFalse _ [mp,mq]  =  lred "ndc-ImpFalse" $  mkOr [mp,mq]
ndcImpFalse _ _ = Nothing

ndcIFEntry :: (Show s, Ord s) => (String, Entry s)
ndcIFEntry
 = ( "NDC"
   , PredEntry subAny ppNDC [] ndcImpFalse simpNDC )
\end{code}
\RLEQNS{
   P \land Q &\defs& \lnot(\lnot P \lor \lnot Q)
}
\begin{code}
andImpFalse :: Dict s -> [Pred s] -> RWResult s
andImpFalse _ [mp,mq]
 = lred "and-ImpFalse"
     $ mkNot $ mkOr [mkNot mp, mkNot mq]
andImpFalse _ _ = Nothing

andIFEntry :: (Show s, Ord s) => (String, Entry s)
andIFEntry
 = ( "And"
   , PredEntry subAny ppAnd [] andImpFalse simpAnd )
\end{code}

\begin{code}
impFalseDict :: (Ord s, Show s) => Dict s
impFalseDict
 = makeDict
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
pA = PVar "A"
pB = PVar "B"

eqVV = Equal (Var "v1") (Var "v2")
eqVK = Equal (Var "v1") (Z 42)
eqMV = Equal (Var "m1") (Var "v2")
eqMK = Equal (Var "m1") (Z 42)
eqPV = Equal (Var "p1") (Var "v2")
eqPK = Equal (Var "p1") (Z 42)

eqVVthenA = mkSeq eqVV pA
eqVKthenA = mkSeq eqVK pA
eqMVthenA = mkSeq eqMV pA
eqMKthenA = mkSeq eqMK pA
eqPVthenA = mkSeq eqPV pA
eqPKthenA = mkSeq eqPK pA

eqV'V = Equal (Var "v1'") (Var "v2")
eqV'K = Equal (Var "v1'") (Z 42)
eqM'V = Equal (Var "m1'") (Var "v2")
eqM'V' = Equal (Var "m1'") (Var "v2'")
eqM'K = Equal (Var "m1'") (Z 42)

eqV'VthenA = mkSeq eqV'V pA
eqV'KthenA = mkSeq eqV'K pA
eqM'VthenA = mkSeq eqM'V pA
eqM'KthenA = mkSeq eqM'K pA

eqDyn'KthenA
 = mkSeq (mkAnd $ map eqIt ["m1'","v2'","v1'","m2'"]) pA

eqDuh'KthenA
 = mkSeq (mkAnd $ map eqIt ["m1'","v2'","m2'"]) pA

aAndeqDny'KthenB
 = mkSeq (mkAnd $ pA : map eqIt ["m1'","v2'","m2'"]) pB

aAndeqDny'KthenEq
 = mkSeq (mkAnd $ pA : map eqIt ["m1'","v2'","m2'"]) eqM'V'

eqIt v' = Equal (Var v') (Z 42)
\end{code}

A test for atomic substitution
\begin{code}
asubjunk :: Pred ()
asubjunk = PSub pA [("x",Z 42),("y'",Z 666)]
\end{code}

\HDRc{Test Laws}

\begin{code}
creduceTest :: CRWFun s
creduceTest d (Comp "Imp" [ante,mconsq])
 = Just ( "discharge assumption"
        , [ ( ante, mconsq, diff )                 -- True  => P  =  P
          , ( mkNot ante, T, diff ) ] )  -- False => _  =  True
creduceTest _ mpr = Nothing
\end{code}
Iteration  satisfies the loop-unrolling law:
\[
  c * P  \quad=\quad (P ; c * P ) \cond c \Skip
\]
\begin{code}
unrollTst :: Ord s => String -> RWFun s
unrollTst _ d mw@(Comp "Iter"  [mc, mpr])
 | isCondition mc
           = Just ( "loop-unroll"
                  , mkCond (mkSeq mpr mw) mc mkSkip
                  , diff )
unrollTst _ _ _ = Nothing
\end{code}

\HDRc{Laws Dictionary}

\begin{code}
lawsEntry :: (Ord s, Show s) => (String, Entry s)
lawsEntry = (laws,LawEntry [reduceStd] [creduceTest] [unrollTst])

lawsDict :: (Ord s, Show s) => Dict s
lawsDict = makeDict [ lawsEntry ]
\end{code}

\HDRb{Test Calculator}

\HDRc{Test Dictionary}

Test dictionarys
\begin{code}
utcpDict :: (Ord s, Show s) => Dict s
utcpDict = dictUTCP
           `dictMrg` stdUTPDict
           `dictMrg` lawsDict
           `dictMrg` stdDict

impDict :: (Ord s, Show s) => Dict s
impDict  = impFalseDict
           `dictMrg` absAlfDict
           `dictMrg` lawsDict
           `dictMrg` stdDict
\end{code}

\HDRc{Test Calculator Top-Level}

\begin{code}
calc :: (Ord s, Show s) => Dict s -> Pred s -> IO (CalcLog s)
calc d pr = calcREPL d noInvariant $ buildMarks pr
putcalc :: (Ord s, Show s) => Dict s -> Pred s -> IO ()
putcalc d pr
  = do res <- calc d pr
       putStrLn "\n\nTRANSCRIPT:"
       putStrLn $ calcPrint res

ucalc, icalc :: (Ord s, Show s) => Pred s -> IO (CalcLog s)
uput,  iput  :: (Ord s, Show s) => Pred s -> IO ()

ucalc = calc utcpDict
uput = putcalc utcpDict

icalc = calc impDict
iput = putcalc impDict

tshow :: (Show s, Ord s) => Pred s -> String
tshow = pmdshow 80 utcpDict noStyles . buildMarks
tput :: (Show s, Ord s) => Pred s -> IO ()
tput = putStrLn . tshow
tsimp :: (Show s, Ord s) => Pred s -> Maybe (BeforeAfter s)
tsimp = simplify utcpDict 42 . buildMarks
\end{code}
