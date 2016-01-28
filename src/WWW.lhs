\HDRa{Wheels Within Wheels}\label{ha:WWW}
\begin{code}
module WWW where
-- import Utilities
-- import qualified Data.Map as M
import Data.List
-- import Data.Char
-- import Data.Maybe
-- import Debug.Trace
import PrettyPrint
import CalcTypes
import StdPrecedences
import CalcPredicates
import CalcAlphabets
import CalcSimplify
import CalcRecogniser
import CalcRun
import StdPredicates
import StdLaws
-- import CalcZipper
-- import CalcSteps
import StdUTPPredicates
import StdUTPLaws
\end{code}


\textbf{\emph{This is SeqPML, renamed WWW, provided the section/subsection
structured, with most syntactical, alphabet a predicate material
to be harvested in the first instance from the UTCP files}}
%%
%% local macros
%%
\def\wseq{\mathbin{;\!;}}
\def\wcond{\mathbin{\vartriangleleft\vartriangleright}}
\def\pgrd{\mathrel{\&}}

\HDRb{Introduction to WWW}\label{hb:WWW-intro}

This is UTCP where we explore the ``WWW'' variant
based on the healthiness condition:
\RLEQNS{
\mathbf{W}(P) &\defs& \lnot ls(out) * P
}

\newpage
\HDRb{Variables of WWW}\label{hb:WWW-vars}

\RLEQNS{
   p,q,r &\in& R & \say{Resource-Ids}
}
\begin{code}
p = "p" ; vp = Var p
q = "q" ; vq = Var q
r = "r" ; vr = Var r
\end{code}

\HDRc{Alphabet of WWW}\label{hb:WWW-alpha}

We have a (non-script) dynamic state ($res$) which records the current resource set
and another non-script dynamic ($rdy$) which propagates a willingnes to run
(because now satisfied) from later
processes back to those composed in front.
\begin{code}
res  = "res"  ; vres  = Var res
res' = "res'" ; vres' = Var res'
rdy  = "rdy"  ; vrdy  = Var rdy  ; ardy  = atm vrdy
rdy' = "rdy'" ; vrdy' = Var rdy' ; ardy' = atm vrdy'
\end{code}

\HDRc{The Alphabet Dictionary}\label{hc:WWW-alfa-dict}

\begin{code}
wAlfDict = stdAlfDictGen [res]  -- script (dynamic)
                         [rdy]  -- model (dynamic)
                         []     -- parameters (static)
\end{code}

\newpage
\HDRb{Expressions of WWW}\label{hb:WWW-expr}

We just have sets of resources,
and membership queries on same
\RLEQNS{
   rs,rr,pr &\in& RS & \say{Resource Sets}
\\ &\defs& r^* & \say{---Enumeration}
\\ &  |  & rs \cup rs & \say{---Union}
\\ &  |  & rs \cap rs & \say{---Intersection}
\\ &  |  & rs \setminus rs & \say{---Removal}
\\ &  |  & r \in rs & \say{---Membership}
\\ &  |  & rs \subseteq rs & \say{---Subset}
\\ g &\in& Grd & \say{Boolean Guards}
}
\begin{code}
rs = Var "rs"; rr = Var "rr" ; pr = Var "pr";
g = "g" ; vg = Var "g" ; ag = atm vg
\end{code}


\HDRc{Set Enumerations}\label{hc:WWW-set-enum}
\RLEQNS{
   rs,rr,pr &\in& RS & \say{Resource Sets}
\\ &\defs& r^* & \say{---Enumeration}
}
\begin{code}
set es = App nset es ; nset = "set"

showSet :: Show s => Dict s -> [Expr s] -> String
showSet d es = "{"++dlshow d "," es++"}"

dSet :: Show s => (String, Entry s)
dSet = ( nset, ExprEntry True showSet $ justMakes set )
\end{code}


\HDRc{Set Union}\label{hc:WWW-set-union}
\RLEQNS{
   rs,rr,pr &\in& RS & \say{Resource Sets}
\\ &  |  & rs \cup rs & \say{---Union}
}
\begin{code}
u rs1 rs2 = App nu [rs1, rs2] ; nu = "U"

showU :: Show s => Dict s -> [Expr s] -> String
showU d [e,f] = "("++edshow d e++" U "++edshow d f++")"
showU d es = "<<BAD-U>>"

evalU d [App nm1 es1,App nm2 es2]
 | nm1==nset && nm2==nset  =  ("union",set (es1++es2))
evalU d [e,f] = ("", u e f)
evalU d es = ("bad-U",App "?U" es)

dU :: Show s => (String, Entry s)
dU = ( nu, ExprEntry True showU evalU )
\end{code}


\HDRc{Set Intersection}\label{hc:WWW-set-int}
\RLEQNS{
   rs,rr,pr &\in& RS & \say{Resource Sets}
\\ &  |  & rs \cap rs & \say{---Intersection}
}
\begin{code}
intsct rs1 rs2 = App nint [rs1, rs2] ; nint = "int"

showI :: Show s => Dict s -> [Expr s] -> String
showI d [e,f] = "("++edshow d e++" I "++edshow d f++")"
showI d es = "<<BAD-I>>"

evalI d [App nm1 es1,App nm2 es2]
 | nm1==nset && nm2==nset
                       = ("intersect",set (es1 `intersect` es2))
evalI d [e,f] = ("", intsct e f)
evalI d es = ("bad-I",App "?I" es)

dI :: (Eq s, Show s) => (String, Entry s)
dI = ( nint, ExprEntry True showI evalI )
\end{code}


\HDRc{Set Removal}\label{hc:WWW-set-rem}
\RLEQNS{
   rs,rr,pr &\in& RS & \say{Resource Sets}
\\ &  |  & rs \setminus rs & \say{---Removal}
}
\begin{code}
rmv rs1 rs2 = App nrem [rs1, rs2] ; nrem = "rem"

showR :: Show s => Dict s -> [Expr s] -> String
showR d [e,f] = "("++edshow d e++" \\ "++edshow d f++")"
showR d es = "<<BAD-\\>>"

evalR d [App nm1 es1,App nm2 es2]
 | nm1==nset && nm2==nset  =  ("remove",set (es1 \\ es2))
evalR d [e,f] = ("", rmv e f)
evalR d es = ("bad-R",App "?\\" es)

dR :: (Eq s, Show s) => (String, Entry s)
dR = ( nrem, ExprEntry True showR evalR )
\end{code}

\newpage
\HDRc{Set Membership}\label{hc:WWW-member}
\RLEQNS{
   rs,rr,pr &\in& RS & \say{Resource Sets}
\\ &  |  & r \in rs & \say{---Membership}
}
\begin{code}
mem r rs = App nmem [r, rs] ; nmem = "in"

showM :: Show s => Dict s -> [Expr s] -> String
showM d [e,f] = "("++edshow d e++" in "++edshow d f++")"
showM d es = "<<BAD-in>>"

evalM d [e,App nm es]
 | nm==nset   =  ("membership", B (e `elem` es))
evalM d [e,f] =  ("", mem e f)
evalM d es    =  ("bad-in", App "?in" es)

dM :: (Show s, Eq s) => (String, Entry s)
dM = ( nmem, ExprEntry True showM evalM )
\end{code}


\HDRc{Subsets}\label{hc:WWW-subset}
\RLEQNS{
   rs,rr,pr &\in& RS & \say{Resource Sets}
\\ &  |  & rs \subseteq rs & \say{---Subset}
}
\begin{code}
subset rs1 rs2 = App nsubset [rs1, rs2] ; nsubset = "subset"

showS :: Show s => Dict s -> [Expr s] -> String
showS d [e,f] = "("++edshow d e++" |= "++edshow d f++")"
showS d es = "<<BAD-S>>"

evalS d [App nm1 es1,App nm2 es2]
 | nm1==nset && nm2==nset  =  ("subset",B $ null (es1\\es2))
evalS d [e,f] = ("", subset e f)
evalS d es = ("bad-S",App "?S" es)

dS :: (Eq s, Show s) => (String, Entry s)
dS = ( nsubset, ExprEntry True showS evalS )
\end{code}


\HDRc{The Expression Dictionary}\label{hc:WWW-expr-dict}

\begin{code}
dictWE :: (Ord s, Show s) => Dict s
dictWE = makeDict [dSet, dU, dI, dR, dM]
\end{code}

\newpage
\HDRb{Predicates for WWW}\label{hb:WWW-stmt}

\RLEQNS{
   A,B &\in& PML_{Seq} & \say{SeqPML programs}
\\ &\defs& \Skip & \say{---Do nothing (UTP Std)}
\\ &|& N?rr!pr  & \say{---\texttt{action}}
\\ &|& A^\omega & \say{---\texttt{iteration}}
\\ &|& A ; B & \say{---\texttt{sequence} (UTP Std)}
\\ &|& A \wcond B & \say{---\texttt{select}}
\\ &|& g \pgrd B & \say{---Guarded Actions}
}
\begin{code}
pA             =  pvar nA           ; nA   = "A"
pB             =  pvar nB           ; nB   = "B"

precAct = precSpacer 9 + 5
precWhl = precSpacer 7 + 5
precSqc = precSpacer 4 + 5
precCnd = precSpacer 3 + 5
precGrd = precSpacer 8 + 5
\end{code}


\newpage
\HDRc{Basic Actions}\label{hc:WWW-action}
\RLEQNS{
   PML_{Seq} &= & \dots \mid  N?rr!pr \mid \dots
\\ N?rr!pr &\defs& rr \subseteq res
\\ && \pgrd
             res' = res \cup pr
}
\begin{code}
action n rr pr =  comp nact [atm $ Var n, atm rr, atm pr]
nact = "act"

ppAct :: (Show s, Ord s)
       => Dict s -> MarkStyle -> Int -> [MPred s] -> PP
ppAct d ms p [nm,rr,pr]
 = pplist [ mshowp d ms 0 nm
          , ppa "?"
          , mshowp d ms 0 rr
          , ppa "!"
          , mshowp d ms 0 pr ]
ppAct d ms p mprs = pps styleRed $ ppa "invalid-Act"

defAct d [_,rr,pr] = ( "INVALID", comp nact [] )
defAct d mprs = ( "INVALID", comp nact mprs )

dAct :: (Show s, Ord s) => (String,Entry s)
dAct = ( nact
        , PredEntry False ppAct (pNoChg nact) (pNoChg nact))
\end{code}

\newpage
\HDRc{Guarded Actions}\label{hc:WWW-guards}

Not part of the language per-se,
but a useful way -station,
and where all the ``real action'' happens.
\RLEQNS{
   PML_{Seq} &= & \dots \mid  g \pgrd B \mid \dots
\\ g \pgrd B &\defs& rdy = \lnot g \land (B \cond g W)
   & W \say{to be defined.}
}
We will determine $W$ once we see the contexts in which it arises.
\begin{code}
pgrd g p =  comp ngrd [atm $ g, p]
ngrd = "grd"

ppGrd :: (Show s, Ord s)
       => Dict s -> MarkStyle -> Int -> [MPred s] -> PP
ppGrd d ms p [mpr1,mpr2]
 = paren p precSqc
     $ ppopen " & " [ mshowp d ms precGrd mpr1
                    , mshowp d ms precGrd mpr2 ]
ppGrd d ms p mprs = pps styleRed $ ppa "invalid-&"

--
defGrd d [g,p] = ( "grd", mkAnd [ bEqv ardy g
                                , bCond pB ag pW ] )
defGrd d mprs = ( "INVALID", Comp ngrd mprs )

pW = pvar "W" -- the mysterious 'W' !
--
dGrd :: (Show s, Ord s) => (String,Entry s)
dGrd = ( ngrd
        , PredEntry False ppGrd defGrd (pNoChg nact))
\end{code}

\newpage
\HDRc{Omega Loops}\label{hc:WWW-iterate}
\RLEQNS{
   PML_{Seq} &=& \dots \mid A^\omega
\\ A^\omega &\defs& \lnot rdy' * A
\\
}

\textbf{Unfortunately this does not work: the fixed points for $c'*P$
are strange, at best. We need to use unique generators here
to construct indices that are themselves static parameters
but which point into part of a dynamic structure,
that allows a form of signalling between sub-components.}
\begin{code}
omega p        =  comp nw [p]       ; nw = "omega"

ppWhl :: (Show s, Ord s)
       => Dict s -> MarkStyle -> Int -> [MPred s] -> PP
ppWhl d ms p [mpr1]
 = pplist [ mshowp d ms precWhl mpr1
          , ppa "^w" ]
ppWhl d ms p mprs = pps styleRed $ ppa "invalid-Omega"

defOmega _ [p] = ( "omega", mkIter (bNot ardy') p )
defOmega d mprs = ( "INVALID", Comp nw mprs )

dOmega :: (Show s, Ord s) => (String,Entry s)
dOmega = ( nw
         , PredEntry False ppWhl defOmega (pNoChg nw))
\end{code}

\newpage
\HDRc{Selection}\label{hc:WWW-selection}
\RLEQNS{
   PML_{Seq} &=& \dots \mid A \wcond B
}
\begin{code}
pcond p q      =  comp ncnd [p, q]  ; ncnd = "pcond"

ppCnd d ms p [mprt,mpre]
 = paren p precCnd
      $ pplist [ mshowp d ms precCnd mprt
               , ppa " <|> "
               , mshowp d ms precCnd mpre ]
ppCnd d ms p mprs = pps styleRed $ ppa "invalid-<|>"

dCnd :: (Show s, Ord s) => (String,Entry s)
dCnd = ( ncnd
        , PredEntry False ppCnd (pNoChg ncnd) (pNoChg ncnd))
\end{code}

\HDRc{The Predicate Dictionary}\label{hc:WWW-pred-dict}

\begin{code}
dictWP :: (Ord s, Show s) => Dict s
dictWP = makeDict [dAct, dGrd, dOmega, dCnd]
\end{code}


\newpage
\HDRb{Reductions for WWW}\label{hb:WWW-reduce}

\begin{code}
wReduce ::DictRWFun s
\end{code}

Default case: no change.
\begin{code}
wReduce _ mpr = ( "", mpr )
\end{code}

\HDRc{The Reduction Entry}\label{hc:WWW-reduce-ent}

\begin{code}
wRedEntry :: (Ord s, Show s) => Dict s
wRedEntry = entry laws $ LawEntry [wReduce] [] []
\end{code}

\newpage
\HDRb{Conditional Reductions for WWW}\label{hb:WWW-creduce}

\begin{code}
wCReduce :: CDictRWFun s
\end{code}

Default case: no change.
\begin{code}
wCReduce _ mpr = ( "", [(T,mpr)] )
\end{code}

\HDRc{The Conditional Reduction Entry}\label{hc:WWW-reduce-ent}

\begin{code}
wCRedEntry :: (Ord s, Show s) => Dict s
wCRedEntry = entry laws $ LawEntry [] [wCReduce] []
\end{code}


\newpage
\HDRb{Loop Unrolling for WWW}\label{hb:WWW-unroll}

Here we remove the requirement that the loop predicate
be a condition.
Iteration  satisfies the loop-unrolling law:
\[
  C * P  \quad=\quad (P ; C * P ) \cond C \Skip
\]
\begin{code}
wUnroll :: Ord s => DictRWFun s
wUnroll d mw@(_,Comp nm  [mc, mpr])
 | nm == nIter = ( "WWW unroll"
                 , bCond (bSeq mpr mw) mc bSkip )
wUnroll _ mpr = ( "", mpr )
\end{code}

\HDRc{The Unroll Entry}\label{hc:WWW-reduce-ent}

\begin{code}
wLoopEntry :: (Ord s, Show s) => Dict s
wLoopEntry = entry laws $ LawEntry [] [] [wUnroll]
\end{code}

\newpage
\HDRb{Dictionary for WWW}\label{hb:WWW-laws}

\begin{code}
wDict :: (Ord s, Show s) => Dict s
wDict
 =  dictVersion "WWW 0.1"
    `dictMrg` dictWE
    `dictMrg` dictWP
    `dictMrg` wRedEntry
    `dictMrg` wCRedEntry
    `dictMrg` wLoopEntry
    `dictMrg` wAlfDict
    `dictMrg` stdUTPDict
    `dictMrg` stdDict
\end{code}

\newpage
\HDRb{WWW Calculator}\label{hb:WWW-CALC}

\begin{code}
wshow :: (Show s, Ord s) => MPred s -> String
wshow = pmdshow 80 wDict noStyles

wput :: (Show s, Ord s) => MPred s -> IO ()
wput = putStrLn . wshow


wcalc mpr = calcREPL wDict mpr
wputcalc :: (Ord s, Show s) => MPred s -> IO ()
wputcalc mpr = printREPL wDict mpr

wsimp :: (Show s, Ord s) => MPred s -> (String, MPred s)
wsimp mpr
  = (what,mpr')
  where (_,what,mpr') = simplify wDict 42 mpr
wsimp2 :: (Show s, Ord s) => (String, MPred s) -> (String, MPred s)
wsimp2 = wsimp . snd
\end{code}
