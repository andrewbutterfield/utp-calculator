\HDRa{Pretty Printer}\label{ha:pretty-printer}
\begin{code}
module PrettyPrint where
import Utilities
import Data.List
\end{code}

Version
\begin{code}
versionPrettyPrint = "PP-0.6"
\end{code}

Our pretty printer handles atomic pieces, which render as is,
and composite parts, defined as a list of parts, along with descriptions
of the left and right delimiters and a separator part.
Composites will be rendered with line breaks and indentation
in a manner that is hopefully maximally pleasing.
We also provide a (simple) means for applying ``styles''.

Styles (keeping it very simple for now):
\begin{code}
data Style = Underline
           | Colour Char
           deriving (Eq,Ord)
           
instance Show Style where
  show Underline   =  setUnderline
  show (Colour c)  =  setColour c

resetStyle       = "\ESC[m\STX"
setUnderline     = "\ESC[4m\STX"
setColour colour = "\ESC[1;3"++colour:"m\STX"

colourRed = setColour '1'
--green = fcolor '2'
--blue = fcolor '4'
--yellow = '3'
--magenta = '5'
--cyan = '6'
--white = '7' --light grey!!

addStyle s ss = nub $ sort (s:ss)
setStyle = concat . map show
\end{code}



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

\newpage
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


Now, rendering it as a `nice' string.
We provide the desired column width at the top level,
along with an initial indentation of zero.
\begin{code}
render :: Int -> PP -> String
render w0 = unlines' . layout w0 0
\end{code}

Some useful utilities:
\begin{code}
prefuse :: [a] -> [[a]] -> [[a]]
prefuse prefix [] = [prefix]
prefuse prefix (ln:lns) = (prefix ++ drop (length prefix) ln):lns

addon postfix [] = [postfix]
addon postfix [ln] = [ln++postfix]
addon postfix (ln:lns) = ln:addon postfix lns
\end{code}


\newpage
The main recursive layout algorithm has a width and indentation parameter
---
the sum of these is always constant.
\begin{code}
-- w+i is constant;  w+i=w0 above
layout :: Int -> Int -> PP -> [String]

-- 1st three cases: cannot break, or can fit on line
layout _ i (PP _ (PPA str)) = [ind i ++ str]
layout w i pp@(PP s _)
 | s <= w  =  [ind i ++ ppstr [] pp]
layout _ i pp@(PP _ (PPC _ _ _ [])) = [ind i ++ ppstr [] pp]

-- case when non-trivial comp and it is too wide
layout w i (PP _ (PPC lpp rpp sepp pps))
 = layout' w i (w-s) (i+s) lpp rpp sepp pps -- pps not null
 where s = max (ppsize lpp) (ppsize sepp)
\end{code}

The helpers, \texttt{layout'} and \texttt{layout''} need to track outer (\texttt{w i})
and inner (\texttt{w' i'}) values of width and indentation.
\begin{code}
-- we need to split it up
layout' w i w' i' lpp rpp sepp [pp]
 = layout w i lpp
   ++ layout w' i' pp
   ++ layout w i rpp
layout' w i w' i' lpp rpp sepp (pp:pps)
 = prefuse (ind i ++ ppstr [] lpp) (layout w' i' pp) -- header line
   ++
   layout'' w i w' i' rpp sepp pps -- pps not null

layout'' w i w' i' rpp sepp [pp]
 = addon (ppstr [] rpp) $ prefuse (ind i ++ ppstr [] sepp)
                     $ layout w' i' pp
layout'' w i w' i' rpp sepp (pp:pps)
 = prefuse (ind i ++ ppstr [] sepp) $ layout w' i' pp
   ++
   layout'' w i w' i' rpp sepp pps -- pps not null
\end{code}