\HDRa{Calculator Tests}\label{ha:calc-test}
\begin{code}
module CalcTest where
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
import CalcSimplify
import CalcRecogniser
import StdPredicates
import CalcZipper
import CalcSteps
\end{code}

\HDRb{Default Mark Type}

We will generally use non-negative \emph{Int} as markers,
with $-1$ representing ``no mark'',
and incrementing being used to generate new marks.
\begin{code}
instance Mark Int where
  startm = 0
  nextm = (+1)

type IPred s = MPred Int s
\end{code}

\HDRb{Concrete Builders}

\HDRc{Building Basic Predicates}

\begin{code}
iT, iF :: IPred s
iT = bT
iF = bF
iPV :: String -> IPred s
iPV = bPV
iEqual :: Expr s -> Expr s -> IPred s
iEqual = bEqual
iAtm :: Expr s -> IPred s
iAtm = bAtm
iComp :: String -> [IPred s] -> IPred s
iComp = bComp
iPSub :: Ord s => IPred s -> Substn s -> IPred s
iPSub = bPSub
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
xandy = iAnd [px,py,pz]
sub42 :: Ord s => IPred s
sub42 = iPSub xandy x42

xeqy = iEqual vx vy
\end{code}

\HDRb{Test Functions}
\begin{code}
test ipr = simplify 42 stdDict ipr
rtest (_,ipr) = simplify 99 stdDict ipr
\end{code}
