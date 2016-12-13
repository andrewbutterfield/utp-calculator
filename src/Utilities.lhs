\section{General Utility Code}
\begin{code}
module Utilities where
import Data.List
import Data.Char
\end{code}


Here we give useful bits and pieces of code.

\begin{code}
lshow sep xs = concat (intersperse sep $ map show xs)

sshow xs  =  "{" ++ lshow "," xs ++ "}"

mshow Nothing  = ""
mshow (Just x) = show x

mshowWith sh Nothing  = ""
mshowWith sh (Just x) = sh x

trim = ltrim . reverse . ltrim . reverse
ltrim "" = ""
ltrim str@(c:cs)
 | isSpace c  =  ltrim cs
 | otherwise  =  str

unlines' [] = []
unlines' [s] = s
unlines' (l:ls) = l ++ '\n' : unlines' ls

ttail [] = []
ttail (_:xs) = xs
\end{code}

Code to indent lines by looking for newlines and inserting spaces immediately afterwards.
\begin{code}
indshow :: Show a => a -> String
indshow = indent . show

indent str
 = ' ':' ':ind str
 where
  ind "" = ""
  ind (c:cs)
   | c == '\n'  =  c:' ':' ':ind cs
   | otherwise  =  c:ind cs
\end{code}

We need to show disjunctions a lot...
\begin{code}
showDisj i [] = ind i ++ "FALSE"
showDisj i [pr] = ind i ++ show pr
showDisj i (pr:prs)
 = ind i ++ "(   " ++ show pr
   ++ '\n':(unlines $ map showpr prs)
   ++ ind i ++ ")"
 where
   showpr pr = ind i ++ " \\/ " ++ show pr

ind i = replicate i ' '
\end{code}

Functions for pairs:
\begin{code}
appfst f    (a,b) = (f a,   b)
appsnd g    (a,b) = (  a, g b)
appboth f g (a,b) = (f a, g b)

mapfst f = map $ appfst f
mapsnd f = map $ appsnd f
mapboth f g = map $ appboth f g
\end{code}

Test combinators
\begin{code}
someOf, allOf :: [a -> Bool] -> a -> Bool
someOf ps x = or $ applyAll ps x
allOf ps x = and $ applyAll ps x

applyAll :: [a->Bool] -> a -> [Bool]
applyAll [] _ = []
applyAll (p:ps) x = p x : applyAll ps x
\end{code}
