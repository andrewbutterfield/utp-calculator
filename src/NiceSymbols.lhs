\HDRa{Nice Symbols}\label{ha:nice}

\begin{code}
{-# LANGUAGE CPP #-}
module NiceSymbols where
import Data.Char
\end{code}

We define some nice symbols using unicode, for non-Windows usage,
along with dull ASCII equivalents for Windows users.

We assume UTF-8 throughout.

Given a LaTeX symbol macro like \verb"\xyz"
we define a Haskell variable \verb"_xyz"
to be a string that gives either a Unicode/UTF-8 glyph for that symbol,
or an approximation using ``ASCII-art''.

\HDRb{Alphabet conversions}

How to convert ASCII `a' to `z' into different fontstyles, in UTF-8
(See \verb"http://qaz.wtf/u/convert.cgi?text=az").

\begin{tabular}{|l|r|r|}
  \hline
  Style & Code for 'A' & Code for `a'
  \\\hline
  ASCII & 65 & 97
  \\\hline
  Math Sans Bold & 120276 & 120302 \\
  \\\hline
\end{tabular}
\begin{code}
styleShift code_A code_a c
 | isUpper c  =  chr (ord c + upperShift)
 | isLower c  =  chr (ord c + lowerShift)
 | otherwise  =  c
 where
   upperShift = code_A - ord 'A'
   lowerShift = code_a - ord 'a'

mathBold     = map $ styleShift 119808 119834
mathSansBold = map $ styleShift 120276 120302
flags        = map $ styleShift 127462 127462
test = map $ styleShift 119886 119886
\end{code}

\HDRb{Weight Conversions}

\HDRc{Weight Conversion for Unix/OS X}

\begin{code}
#ifndef mingw32_HOST_OS

eSGR n = "\ESC["++show n++"m"

resetSGR = eSGR 0
boldSGR  = eSGR 1
ovlSGR   = eSGR 9

bold str = boldSGR ++ str ++ resetSGR
overline c = ovlSGR ++ c:resetSGR
#endif
\end{code}

\HDRc{Weight ``Conversion'' for Windows}

\begin{code}
#ifdef mingw32_HOST_OS

bold str = str
#endif
\end{code}


\HDRb{Nice Symbols for OS X/Unix}

\begin{code}
#ifndef mingw32_HOST_OS

_ll = "\171"
_gg = "\187"

_alpha = "\945"
_pi = "\x03C0"
_epsilon = "\x03F5"
_tau = "\x03C4"
_Sigma = "\x2211"
_omega = "\x1d714"

_top = "\x22A4"
_bot = "\x22A5"
_sqcap = "\8851"
_sqcup = "\8852"
_sqsubseteq = "\8849"

_true = bold "true"
_false = bold "false"
_lnot = "\172"
_land = "\8743"
_lor = "\8744"
_implies = "\8658"
_equiv = "\8801"

_emptyset = "\8709"
_cup = "\8746"
_cap = "\8745"
_setminus = "\8726"
_in = "\8712"
_subseteq = "\8838"

_langle = '\x27e8'
_rangle = '\x27e9'

_parallel = "\8214"
_Cap = "\8914"

_infty = "\x221e"
_star = "\9733"

_overline str = "\ESC[9m"++follow str '\x35e'++"\ESC[0m"

_supChar '1' = '\185'
_supChar '2' = '\178'
_supChar '3' = '\179'

_supChar 'A' = '\7468'
_supChar 'B' = '\7470'
_supChar 'D' = '\7472'
_supChar 'E' = '\7473'

_supChar 'a' = '\7491'
_supChar 'b' = '\7495'
_supChar 'c' = '\7580'
_supChar 'd' = '\7496'
_supChar 'e' = '\7497'
_supChar 'f' = '\7584'
_supChar 'g' = '\7501'
_supChar 'h' = '\688'
_supChar 'i' = '\8305'
_supChar 'j' = '\690'
_supChar 'k' = '\7503'
_supChar 'l' = '\737'
_supChar 'm' = '\7504'
_supChar 'n' = '\8319'
_supChar 'o' = '\7506'
_supChar 'p' = '\7510'
-- no q !
_supChar 'r' = '\691'
_supChar 's' = '\738'
_supChar 't' = '\7511'
_supChar 'u' = '\7512'
_supChar 'v' = '\7515'
_supChar 'w' = '\695' -- also '\7514'
_supChar 'x' = '\739'
_supChar 'y' = '\696'
_supChar 'z' = '\7611'

_supChar '+' = '\8314'
_supChar '-' = '\8315'
_supChar '(' = '\8317'
_supChar ')' = '\8318'

_supChar ',' = ','
_supChar '*' = '*'
_supChar '\x221e' = '\x221e'  -- infty
_supChar '\120596' = '\7514'  -- omega
_supChar '\9733' = '*'    -- star

_supChar c
  | isDigit c = chr (ord c - ord '0' + 8304)
  | otherwise = c

_supStr s = map _supChar s
_supNum n = _supStr $ show n

-- _mathcal 'B' = '\x212c' -- not great!
_mathcal 'E' = '\x2130'
-- _mathcal 'F' = '\x2131'
-- _mathcal 'H' = '\x210b'
-- _mathcal 'I' = '\x2110'
-- _mathcal 'L' = '\x2112'
-- _mathcal 'M' = '\x2133'
-- _mathcal 'R' = '\x211b'
_mathcal c
 | isUpper c  =  chr (ord c - ord 'A' + 0x1d4d0)
 | otherwise  =  c

#endif
\end{code}


\HDRb{``Nice'' Symbols for Windows }

\begin{code}
#ifdef mingw32_HOST_OS

_ll = "<<"
_gg = ">>"

_alpha = "alf"
_pi = "pi"
_epsilon = "eps"
_tau = "tau"
_Sigma = "Sigma"

_top = "T"
_bot = "_|_"
_sqcap = "|~|"
_sqcup = "|_|"
_sqsubseteq = "|="

_true = "true"  -- bold true
_false = "false" -- bold false
_lnot = "~"
_land = "/\\"
_lor = "\\/"
_implies = "==>"
_equiv = "=="

_emptyset = "{}"
_cup = "U"
_cap = "I"
_setminus = "\\"
_in = "in"
_subseteq = "subset"

_langle = '<'
_rangle = '>'

_parallel = "||"
_Cap = "II"

_infty = "inf"
_star = "*"

_overline str = "ovl("++str++")"

_supStr = ('^':)
_supNum n = _supStr $ show n

_mathcal c = c

#endif
\end{code}

\HDRb{Platform Independent Code}

\begin{code}
follow "" _ = ""
follow (c:cs) a = c:a:follow cs a
\end{code}

Basically a catalog of our nice symbols that is easy to display in GHCi
\begin{code}
nice
 = [ ("_ll", _ll)
   , ("_gg", _gg)
   , ("_pi", _pi)
   , ("_epsilon", _epsilon)
   , ("_tau", _tau)
   , ("_Sigma", _Sigma)
   , ("_omega", _omega)
   , ("_top", _top)
   , ("_bot", _bot)
   , ("_sqcap", _sqcap)
   , ("_sqcup", _sqcup)
   , ("_true", _true)
   , ("_false", _false)
   , ("_lnot", _lnot)
   , ("_land", _land)
   , ("_lor", _lor)
   , ("_implies", _implies)
   , ("_equiv", _equiv)
   , ("_emptyset", _emptyset)
   , ("_cup", _cup)
   , ("_cap", _cap)
   , ("_setminus", _setminus)
   , ("_in", _in)
   , ("_subseteq", _subseteq)
   , ("_parallel", _parallel)
   , ("_Cap", _Cap)
   , ("_infty",_infty)
   , ("_overline(p)", _overline "p")
   , ("_supNum(42)", _supNum 42)
   , ("_mathcal(A)", [_mathcal 'A'])
   ]

niceRender w (_nm, nm)
 = _nm ++ (replicate (w-length _nm) ' ') ++ "  " ++ nm
\end{code}
\begin{code}
main
 = do putStrLn $ unlines $ map (niceRender maxw) nice
 where maxw = maximum $ map (length . fst) nice
\end{code}

\HDRc{UnicodeData.txt Utilities}

The official Unicode reference is
\verb"http://ftp.unicode.org/Public/UNIDATA/UnicodeData.txt"

Here is code to extract subsets, based on sub-strings.
\begin{code}
uniSubset keep keepName
 = do unicodeData <- readFile "UnicodeData.txt"
      let keepData = filter keep $ lines unicodeData
      writeFile keepName $ unlines keepData

isSubSeq sub seq
 = isSS sub seq
 where
  isSS [] _       = True
  isSS _ []       = False
  isSS (s:ss) (x:xs)
   | s == x       =  vfySS xs ss xs
   | otherwise    =  isSS sub xs
  vfySS bxs [] _  =  True
  vfySS bxs _ []  =  isSS sub bxs
  vfySS bxs (s:ss) (x:xs)
   | s == x       =  vfySS bxs ss xs
   | otherwise    =  isSS sub bxs

uniShow preamble subsetName
 = do subsetData <- readFile subsetName
      let codes = map getCode $ lines subsetData
      putStrLn $ unlines $ map addpre codes
 where addpre c = show (ord c) ++ " " ++ preamble++[c]

getCode = chr . toHex . takeWhile (/=';')

toHex = toH . reverse
 where
   toH "" = 0
   toH (c:cs) = digitToInt c + 16 * toH cs
\end{code}
