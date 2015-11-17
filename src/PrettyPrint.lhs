\HDRa{Pretty Printer}\label{ha:pretty-printer}
\begin{code}
module PrettyPrint where
import Utilities
import Data.List
\end{code}

Our pretty printer handles atomic pieces, which render as is,
and composite parts, defined as a list of parts, along with descriptions
of the left and right delimiters and a separator part.
Composites will be rendered with line breaks and indentation
in a manner that is hopefully maximally pleasing.
We also provide a (simple) means for applying ``styles''.

\HDRb{Styles}

Styles (keeping it very simple for now):
\begin{code}
data Style = Underline
           | Colour Char
           deriving (Eq,Ord)

instance Show Style where
  show Underline   =  setUnderline
  show (Colour c)  =  setColour c

setUnderline     = "\ESC[4m\STX"
setColour colour = "\ESC[1;3"++colour:"m\STX"

setStyle :: [Style] -> String
setStyle  = concat . map show
resetStyle :: String
resetStyle  = "\ESC[m\STX"
reset = putStrLn resetStyle -- useful in GHCi to tidy up!

colourRed :: String
colourRed = setColour '1'
-- green   '2'
-- blue    '4'
-- yellow  '3'
-- magenta '5'
-- cyan    '6'
-- white   '7' --light grey!!

addStyle s ss = nub $ sort (s:ss)
\end{code}


\HDRb{Pretty-Printing Types}

\begin{eqnarray*}
  pp &::=& pp_{atom} |  pp_{ldelim} ~ pp_{delim} ~ pp_{sep} ~ pp^*
\end{eqnarray*}
We implement these using two mutually recursive datatypes where
the top level-one (\texttt{PP}) wraps the above structure with an integer that gives the
rendered length of the structure, at each level.
\begin{code}
data PP = PP Int PP' deriving (Eq,Ord,Show)

data PP' = PPA String        -- atom
         | PPS Style PP   -- style
         | PPC PP PP PP [PP] -- rdelim ldelim sep pps
         deriving (Eq,Ord,Show)
\end{code}

\HDRb{Simple Rendering}

It is useful to get the size of a \texttt{PP}, as well as the string produced
if it is all rendered on one line.
\begin{code}
ppsize :: PP -> Int
ppsize (PP s _) = s

ppstr :: [Style] -> PP -> String

ppstr _ (PP _ (PPA str)) = str

ppstr stls (PP _ (PPS style pp))
 = let stls' = addStyle style stls
   in concat [ show style -- set new style style
             , ppstr stls' pp -- recurse with styles updated
             , resetStyle -- clear all styles
             , setStyle stls -- restore current style
             ]

ppstr stls (PP _ (PPC lpp rpp sepp [])) = ppstr stls lpp ++ ppstr stls rpp
ppstr stls (PP _ (PPC lpp rpp sepp pps))
 | ppsize lpp == 0  =  pppps stls rpp sepp pps
 | otherwise        =  ppstr stls lpp ++ pppps stls rpp sepp pps

pppps :: [Style] -> PP -> PP -> [PP] -> String
pppps stls rpp sepp []        =  ppstr stls rpp
pppps stls rpp sepp [pp]      =  ppstr stls pp ++ ppstr stls rpp
pppps stls rpp sepp (pp:pps)
  =  ppstr stls pp ++ ppstr stls sepp ++ pppps stls rpp sepp pps
\end{code}

\HDRb{Smart Constructors}

We build smart versions of the \texttt{PPA} and \texttt{PPC} constructors
that automatically accumulate the length information.
\begin{code}
ppa :: String -> PP
ppa str = PP (length str) $ PPA str

pps :: Style -> PP -> PP
pps style pp@(PP len _) = PP len $ PPS style pp

ppc :: PP -> PP -> PP -> [PP] -> PP
ppc lpp rpp sepp pps
 = PP len $ PPC lpp rpp sepp pps
 where
  len = ppsize lpp + ppsize rpp + seps pps * ppsize sepp
         + sum (map ppsize pps)
  seps xs
   | len == 0  =  0
   | otherwise  =  len - 1
   where len = length xs
\end{code}

We then provide some useful builders for common idioms,
mostly where delimiters and separators are atomic.
\begin{code}
ppnul :: PP
ppnul = ppa ""

ppopen' = ppc ppnul ppnul

ppopen :: String -> [PP] -> PP
ppopen sepstr pps = ppopen' (ppa sepstr) pps

pplist :: [PP] -> PP
pplist = ppopen ""

ppclosed :: String -> String -> String -> [PP] -> PP
ppclosed lstr rstr sepstr pps
  = ppc (ppa lstr) (ppa rstr) (ppa sepstr) pps
\end{code}


\HDRb{Full Rendering}

Now, rendering it as a `nice' string.
We provide the desired column width at the top level,
along with an initial indentation of zero.
\begin{code}
render :: Int -> PP -> String
render w0 = fmtShow . layout [] w0 0
\end{code}

\HDRc{Lines and Formatting}

We have two types of strings present:
those representing lines of visible text;
and those that have font format encodings.
We need to keep these distinct as we weave our layout.
We also need to explicitly identify newlines and indents.
\begin{code}
data Layout = NL | Ind Int | Txt String | Fmt String deriving Show
\end{code}
We obtain the final string by merging \texttt{Fmt} with \texttt{Txt} on either
side before calling \texttt{unlines}
(otherwise formatting commands introduce spurious linebreaks).
\begin{code}
lstr NL         =  "\n"
lstr (Ind i)    =  ind i
lstr (Txt str)  =  str
lstr (Fmt str)  =  str

fmtShow :: [Layout] -> String
fmtShow = concat . map lstr

fmtMerge :: [Layout] -> [String]
fmtMerge [] = []
fmtMerge (Txt str:rest) = gotTxt [str] rest
fmtMerge (Fmt str:rest) = needTxt [str] rest

gotTxt :: [String] -> [Layout] -> [String]
gotTxt strs [] = [revMerge strs]
gotTxt strs (Txt str:rest) = revMerge strs : gotTxt [str] rest
gotTxt strs (Fmt str:rest) = gotTxt (str:strs) rest

needTxt :: [String] -> [Layout] -> [String]
needTxt strs [] = [revMerge strs]
needTxt strs (Txt str:rest) = gotTxt (str:strs) rest
needTxt strs (Fmt str:rest) = needTxt (str:strs) rest

revMerge :: [String] -> String
revMerge = concat . reverse
\end{code}

\HDRd{List viewer}

Show list elements one per line:
\begin{code}
ldisp :: Show a => [a] -> IO ()
ldisp = putStrLn . unlines' . map show
\end{code}

\HDRc{Rendering Utilities}
Some useful utilities.

Extend the start of the first line
with a new prefix:
\begin{code}
preext :: [a] -> [[a]] -> [[a]]
preext prefix [] = [prefix] -- if nothing, just add it anyway.
preext prefix (ln:lns) = (prefix ++ ln):lns
\end{code}

Replace the start of the first line
with a new indent and prefix.
We \emph{assume} that the line starts with an indent larger
than the length of the new items combined.
\begin{code}
prefuse :: Int -> String -> [Layout] -> [Layout]

-- if empty (1st line or whole thing), add in anyway.
prefuse i s [] = [Ind i, Txt s]
prefuse i prefix layout@(NL:_) = Ind i : Txt prefix : layout

-- ignore formatting
prefuse i s (fmt@(Fmt _):lns) = fmt:(prefuse i s lns)

-- expected use-case
prefuse newi prefix (Ind oldi:rest)
 = Ind newi : Txt prefix : Ind remi : rest
 where remi = oldi - (newi + length prefix)

-- no change, otherwise
prefuse _ _ layout = layout
\end{code}

Extend the last \texttt{Txt} line with a postfix
\begin{code}
postext :: String -> [Layout] -> [Layout]
postext postfix  = reverse . pext postfix . reverse
 where
   pext postfix [] = [Txt postfix]
   pext postfix (fmt@(Fmt _):lns) = fmt : pext postfix lns
   pext postfix ((Txt ln):lns) = (Txt (ln++postfix)) : pext postfix lns
\end{code}


\HDRc{Layout}

The main recursive layout algorithm has a width and indentation parameter
---
the sum of these is always constant.
Also, we assume that the leading indent has been generated
when we call layout.
\begin{code}
-- w+i is constant;  w+i=w0 above
layout :: [Style] ->Int -> Int -> PP -> [Layout]

-- handle style changes
layout ss w i (PP _ (PPS s pp))
 = (Fmt $ show s) : (layout (addStyle s ss) w i pp)
     ++ [Fmt (resetStyle ++ setStyle ss)]

-- 1st three cases: cannot break, or can fit on line
layout _ _ i (PP _ (PPA str)) = [Txt str]
layout ss w i pp@(PP s _)
 | s <= w  =  [Txt $ppstr ss pp]
layout ss _ i pp@(PP _ (PPC _ _ _ [])) = [Txt $ ppstr ss pp]

-- case when non-trivial comp and it is too wide
layout ss w i (PP _ (PPC lpp rpp sepp pps))
 = layout' ss w i (w-s) (i+s) lpp rpp sepp pps -- pps not null
 where s = max (ppsize lpp) (ppsize sepp)
\end{code}

The helpers, \texttt{layout'} and \texttt{layout''} need to track outer (\texttt{w i})
and inner (\texttt{w' i'}) values of width and indentation.
\begin{code}
-- we need to split it up
layout' ss w i w' i' lpp rpp sepp [pp]
 = layout ss w i lpp
   ++ NL : Ind i' : layout ss w' i' pp
   ++ NL : Ind i' : layout ss w i rpp
layout' ss w i w' i' lpp rpp sepp (pp:pps)
 = prefuse i (ppstr ss lpp) (layout ss w' i' pp) -- header line
   ++
   NL : Ind i' : layout'' ss w i w' i' rpp sepp pps -- pps not null

layout'' ss w i w' i' rpp sepp [pp]
 = postext (ppstr ss rpp) $ prefuse i (ppstr ss sepp)
                          $ layout ss w' i' pp
layout'' ss w i w' i' rpp sepp (pp:pps)
 = prefuse i (ppstr ss sepp) $ layout ss w' i' pp
   ++
   NL : layout'' ss w i w' i' rpp sepp pps -- pps not null
\end{code}
