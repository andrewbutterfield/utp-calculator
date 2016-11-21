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
   
mathSansBold = map $ styleShift 120276 120302
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

_top = "\x22A4"
_bot = "\x22A5"
_sqcap = "\8851"
_sqcup = "\8852"

_true = "\119957\119955\119958\119942"  -- bold true
_false = "\119943\119938\119949\119956\119942" -- bold false
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

_parallel = "\8214"
_double_intersection = "\8914"

_overline str = "\ESC[9m"++follow str '\x35e'++"\ESC[0m"
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

_parallel = "||"
_double_intersection = "II"

_overline str = "ovl("++str++")"
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
   , ("_double_intersection", _double_intersection)
   , ("_overline(p)", _overline "p")
   ]

niceRender w (_nm, nm)
 = _nm ++ (replicate (w-length _nm) ' ') ++ "  " ++ nm
\end{code}
\begin{code}
main
 = do putStrLn $ unlines $ map (niceRender maxw) nice
 where maxw = maximum $ map (length . fst) nice
\end{code}
