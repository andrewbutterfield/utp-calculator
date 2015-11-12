\HDRa{Demo: Calculation Highlighting}\label{ha:highlight-demo}
\begin{code}
module DemoCalcHighlighting where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Debug.Trace
\end{code}

This stand-alone module prototypes
a way to do calculations with the highlighting of interesting
sub-expressions, typically being those that are being modified
by calculation steps.

An expression language with explicit old and new markers
might look like the following:
\RLEQNS{
  E &=& N~\Int | V~\Char^+ | P~ E^2  | Old~E | New~E
}
However, this complicates the use of simplifiers and reducers
that basically want to ignore $Old$ and $New$ tags.
They have to be cluttered with extra clauses like:
\begin{verbatim}
simp (P (Old e1) e2) = simp (P e1 e2)
simp (P e1 (Old e2)) = simp (P e1 e2)
simp (P (New e1) e2) = simp (P e1 e2)
simp (P e1 (New e2)) = simp (P e1 e2)
\end{verbatim}
which in themselves aren't really enough as we want to leave those tags intact.
So instead, we wrap an expression up with a marker component,
where we view the set $M$ of markers as a parameter:
\RLEQNS{
   E_M  &=& N~\Int | V~\Char^+ | P~ME_M^2
\\      &=& \Int + \Char^+ + ME_M^2
\\      & & \textbf{where~}  N,V,P  = 1,2,3
\\ ME_M &=& M \times E_M
\\      &=& M \times \Int + M \times \Char^+ + M \times ME_M^2
}
We are using the following definition of type sum:
\RLEQNS{
  T_1 + T_2 + \cdots + T_n
  &\defs&
  \setof 1 \times T_1
  \cup
  \setof 2 \times T_2
  \cup \ldots \cup
\setof n \times T_n
}

\begin{code}
data E m = N Int    -- number
         | V String -- variable
         | P (ME m) (ME m)    -- plus
       deriving (Ord, Show)

instance Eq (E m) where -- ignore values of m
  (N n1) == (N n2)  =  n1 == n2
  (V v1) == (V v2)  =  v1 == v2
  (P (_,e11) (_,e12)) == (P (_,e21) (_,e22))  =  e11 == e21 && e12 == e22
  _ == _   =  False

type ME m = ( m, E m )
\end{code}

A standard recursive simplifier:
\begin{code}
stdsimp :: ME m -> ME m
stdsimp ( m0, P me1 me2)
 = let
   me1'@(m1',e1') = stdsimp me1
   me2'@(m2',e2') = stdsimp me2
   in case (e1', e2') of
     (N 0 , _   )  ->  (m2',e2')
     (_   , N 0 )  ->  (m1',e1')
     (N n1, N n2)  ->  (m0, N (n1+n2))
     _             ->  (m0, P me1' me2')
stdsimp me = me
\end{code}

A standard one-step reducer:
\begin{code}
stdreduce :: ME m -> ME m
stdreduce (m0, P (_,N 0)  me2       ) = me2
stdreduce (m0, P me1      (_,(N 0)) ) = me1
stdreduce (m0, P (_,N n1) (_,N n2)  ) = (m0, N (n1+n2))
stdreduce me = me
\end{code}

A standard one-step re-arranger:
\begin{code}
stdarrange :: ME m -> ME m
stdarrange (m0, P (m1, P me1 me2) me3) = (m0, P me1 (m1, P me2 me3))
stdarrange (m0, P me1 me2) = (m0, P me2 me1)
stdarrange me = me
\end{code}

A recursive search for an applicable step:
\begin{code}
stdapply :: (ME m -> ME m) -> ME m -> ME m
stdapply step me
 = let me' = step me
   in if snd me == snd me' then stdrecapply step me
   else me'

stdrecapply ::  (ME m -> ME m) -> ME m -> ME m
stdrecapply step me@(m0, P me1 me2)
 = let
    me1' = stdapply step me1
    me2' = stdapply step me2
   in if snd me1' /= snd me1
       then (m0, P me1' me2)
       else if snd me2' /= snd me2
             then (m0, P me1 me2')
             else me
stdrecapply step me = me
\end{code}

Wanted: something that can do the above,
but return two expressions:
\begin{enumerate}
  \item one identical to the input,
        except that a marker $Old$
        has been attached to whatever changed.
  \item one modified as per the steps above,
         but with a $New$ marker
         attached to the change.
\end{enumerate}
If nothing has changed, there should be no change to either marking.
In fact, we shall not simply use two markers $Old$ and $New$ but rather
adopt the use of natural numbers as markers, incrementing for each step.
This will remove the need to change ``new'' markings to ``old'' markings.


We shall try to explore using Conor McBride's Datatype differentiation \cite{McB:derrti}
to construct a ``zipper'' \cite{JFP::Huet1997}.

We remember that the \texttt{ME m} data definition
has the following sum-of-products equation:
\RLEQNS{
   ME_M &=& F(ME_M)
\\   &=& M \times \Int + M \times \Char^+ + M \times ME_M^2
\\   & & \textbf{where~} N,V,P = 1,2,3
}
We can then ``differentiate'' $F(ME_M)$ w.r.t to $ME_M$ to get
\RLEQNS{
\\ ME'_M &=& \partial_{ME_M}(F)
\\    &=& M \times \mathbf 2 \times ME_M
}
We can code this up as a new datatype, where we prime the tags:
\begin{code}
data ME' m = P'     -- parent is a P node
             m      -- parent market
             Bool   -- False, we are left subtree;
                    -- True, we are the right subtree.
             (ME m) -- other subtree of the parent
\end{code}
We then define a zipper as being an expression
together with a list of expression derivatives:
\begin{code}
type MEZipper m = ( ME m    -- the current (focus) expression
                  , [ME' m] -- the steps we took to get here,
                            -- and what we passed on the way.
                  )
\end{code}
We have an operation that combines one $ME'$ with an $ME$,
effectively moving up a level:
\RLEQNS{
   \_\lessdot\_ &:& ME'_M \times ME_M \fun ME_M
\\ (\setof{P'},m,\true, e') \lessdot e &\defs& (m,(\setof{P},e',e))
\\ (\setof{P'},m,\false,e') \lessdot e &\defs& (m,(\setof{P},e,e'))
}
\begin{code}
plugstep :: ME' m -> ME m -> ME m
plugstep (P' m True  me') me  =  (m, P me' me)
plugstep (P' m False me') me  =  (m, P me me')
\end{code}
We then lift this to work with lists of steps,
where the top-most (outer-most step is first)
\RLEQNS{
    \_\dotplus\_ &:& (ME'_M)^* \times ME_M \fun ME_M
\\ \nil \dotplus e &=& e
\\ (s:ss) \dotplus e &=& s \lessdot (ss \dotplus e)
}
\begin{code}
plugin :: [ME' m] -> ME m -> ME m
plugin [] me = me
plugin (s:ss) me = plugstep s $ plugin ss me
\end{code}

As a zipper, we want to keep the list in the reverse order,
with the bottom-most (inner-most) step first.

We start zipping:
\begin{code}
startZip :: ME m -> MEZipper m
startZip me = ( me, [] )
\end{code}

We go down by specifying which branch, if necessary:
\begin{code}
down :: Int -> MEZipper m -> MEZipper m
down 1 ( (m, P me1 me2), ss ) = ( me1, P' m False me2 : ss )
down 2 ( (m, P me1 me2), ss ) = ( me2, P' m True  me1 : ss )
down _ ez = ez -- default case, do nothing
\end{code}

Also up:
\begin{code}
up :: MEZipper m -> MEZipper m
up ( me, (s:ss) ) = ( plugstep s me, ss)
up ez = ez
\end{code}

Modifying the focus:
\begin{code}
upd :: (ME m -> ME m) -> MEZipper m -> MEZipper m
upd f ( me, ss ) = ( f me, ss )
\end{code}

We can also end zipping:
\begin{code}
endZip :: MEZipper m -> ME m
endZip ( me, ss ) = unZip ss me

unZip :: [ME' m] -> ME m -> ME m
unZip [] me = me
unZip (s:ss) me = unZip ss $ plugstep s me
\end{code}

Some test code --- building a full binary tree of given depth:
\begin{code}
fbt :: m -> Int -> ME m
fbt lbl k
 = p k 0
 where
  p 0 x = (lbl, N x)
  p k x = (lbl, P (p k' x) (p k' (x+2^(k-1)))) where k' = k-1
\end{code}

Imagine an expression $e$ to which we apply $step$ three times,
which results in the following changes:
\[
  step_i : t_i \mapsto t'_i
\]
The presentation of the calculation should look like the following,
where underlining denotes ``old'' and the colour red denotes ``new'':
\RLEQNS{
\\ && e
\EQ{defn of $e$ (w.l.o.g.)}
\\&& ( \ldots \OLD{t_1} \ldots t_2 \ldots t_3 \ldots)
\EQm{step_1}
\\&& ( \ldots \NEW{t'_1} \ldots \OLD{t_2} \ldots t_3 \ldots)
\EQm{step_2}
\\&& ( \ldots t'_1 \ldots \NEW{t'_2} \ldots \OLD{t_3} \ldots)
\EQm{step_3}
\\&& ( \ldots t'_1 \ldots t'_2 \ldots \NEW{t'_3} \ldots)
}
Notice how each $step_i$ affects the Old/New marking of both its predecessor
and successor expressions.
Rather than having two markings (Old/New) it turns out to be more effiecient
to have a numeric marking, so $step_i$ introduces mark number $i$.
The interpetation of such marks as old, new or irrelevant can then be done
relative to the numbering of the step outcome being rendered for display.

We can breakdown the above calculation using mark numbers ($M_i$) as follows
\RLEQNS{
   e  && ( \ldots t_1 \ldots t_2 \ldots t_3 \ldots)
\EQm{step_1}
\\ pe_1 && ( \ldots \OLD{M_1(t_1)} \ldots t_2 \ldots t_3 \ldots) & \mbox{display 1=Old}
\\
\\ ne_1 && ( \ldots M_1(t'_1) \ldots t_2 \ldots t_3 \ldots)
\EQm{step_2}
\\ pe_2 && ( \ldots \NEW{M_1(t'_1)} \ldots \OLD{M_2(t_2)} \ldots t_3 \ldots) & \mbox{display 1=New, 2=Old}
\\
\\ ne_2 && ( \ldots M_1(t'_1) \ldots M_2(t'_2) \ldots t_3 \ldots)
\EQm{step_3}
\\ pe_3 && ( \ldots M_1(t'_1) \ldots \NEW{M_2(t'_2)} \ldots \OLD{M_3(t_3)} \ldots) & \mbox{display 2=New, 3=Old}
\\
\\ ne_3 && ( \ldots M_1(t'_1) \ldots M_2(t'_2) \ldots \NEW{M_3(t'_3)} \ldots) & \mbox{display 3=New}
}

So we see that $step_i$ takes $ne_{i-1}$ and produces:
\begin{itemize}
  \item $pe_i$, where $M_i$ has been wrapped around $t_i$
  \item $ne_i$, which is $pe_i$, where $t_i$ (already marked with $M_i$)
   is replaced by $t'_i$.
\end{itemize}
This seems to present a problem for the zipper,
as we have to identify corresponding locations,
where $t_i$ and $t'_i$ reside,
in two different versions of a single expression.
However the structure of the two expressions is identical everywhere else
so a single zipper ``path'' can be applied to both.

Let us begin with numeric marks and ways to mark and unmark things things
\begin{code}
type Mark = Int
type NME  = ME Mark
type NMEStep = NME -> NME
type NMEZipper = MEZipper Mark

mark :: m -> E m -> ME m
mark m e = ( m, e )

nom :: Mark
nom = -1
noMark :: ME m -> ME Mark
noMark (_,e) = mark nom $ noMark' e
noMark' (N n) = N n
noMark' (V v) = V v
noMark' (P me1 me2) = P (noMark me1) (noMark me2)

mupd :: m -> ME m -> ME m
mupd m (_,e) = mark m e
\end{code}

Performing a step --- top-level:
\begin{code}
tagstep :: Mark -> NMEStep -> NME -> Maybe (NME, NME)
tagstep m step ne
 = let
    (t,t',ss) = tagapply m step $ startZip ne
    pe' = unZip ss $ mupd m t
    ne' = unZip ss $ mupd m t'
   in if t==t' then Nothing else Just (pe',ne')
\end{code}

tagged apply:
\begin{code}
tagapply :: Mark -> NMEStep -> NMEZipper -> (NME, NME, [ME' Mark])
tagapply m step ( me, ss )
 = let me' = step me
   in if me == me' then tagrecapply m step ( me, ss )
      else (me,me',ss)
\end{code}

If we fail at the current level to apply a step then we recurse
into the composite seeing if we can get a result with any of
its sub-components:
\begin{code}
tagrecapply :: Mark -> NMEStep -> NMEZipper -> (NME, NME, [ME' Mark])
tagrecapply m step ( (mP,P me1 me2), ss )
 = let res1@(pe1,ne1,_)
        =  tagapply m step ( me1, P' mP False me2 : ss )
   in if pe1 /= ne1
      then res1
      else  tagapply m step ( me2, P' mP True me1 : ss )
tagrecapply m step ( me, ss ) = (me,me,ss)
\end{code}

Now, code to repeatedly run step until no change occurs:
\begin{code}
stepRepeat step me
 = rep step 1 me
 where
   rep step m ne
    = case tagstep m step ne of
        Nothing -> [ne]
        Just (pe',ne') -> pe' : rep step (m+1) ne'
\end{code}

Highlighting stuff:
\begin{code}
freset = "\ESC[m\STX"
fuline = "\ESC[4m\STX"
fcolor ccode = "\ESC[1;3"++ccode:"m\STX"
fred = fcolor '1'
fgreen = fcolor '2'
fblue = fcolor '4'
fyellow = '3'
fmagenta = '5'
fcyan = '6'
fwhite = '7' --light grey
\end{code}
We have a problem, in that we cannot nest escape-sequence formatting effectively.
The reset \verb'\ESC[m\STX' fragmemt resets all prior formatting.
So we need a rendering system that tracks the current set of formats being applied
and which handles a change by doing a reset followed by re-instating what needs to remain.
\begin{code}
data Style = ULine | Red deriving (Eq, Ord, Show)

renderStyle ULine = fuline
renderStyle Red   = fred

type StyledString = ( [Style], String )

adds :: Style -> [Style] -> [Style]
adds s ss = nub $ sort(s:ss)

style :: Mark -> Mark -> NME -> [StyledString]
style umark rmark me
 = r [] me
 where

   r ss ( m, e )
    | m == umark  =  r' (adds ULine ss) e
    | m == rmark  =  r' (adds Red ss) e
    | otherwise   =  r' ss e

   r' ss (N n)        =  [(ss,show n)]
   r' ss (V v)        =  [(ss,v)]
   r' ss (P me1 me2)  =  r ss me1 ++ [(ss," + ")] ++ r ss me2

renderSS :: StyledString -> String
renderSS ( ss, str )
 = (concat $ map renderStyle ss) ++ str ++ freset

render = concat . map renderSS

plain = concat . map snd . style nom nom

displayCalc :: [NME] -> String
displayCalc nmes
 = unlines $ disp 1 0 nmes
 where
   disp old new [] = []
   disp old new (nme:nmes)
     = (render $ style old new nme)
       :
       disp (old+1) old nmes
\end{code}

A fun test:
\begin{code}
demo = putStrLn $ displayCalc $ stepRepeat stdreduce $ noMark $ fbt () 3
\end{code}
