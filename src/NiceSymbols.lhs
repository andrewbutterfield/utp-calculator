\HDRa{Nice Symbols}\label{ha:nice}

\begin{code}
{-# LANGUAGE CPP #-}
module NiceSymbols where
\end{code}

We define some nice symbols using unicode, for non-Windows usage,
along with dull ASCII equivalents for Windows users.

We assume UTF-8 throughout.


\begin{code}
#ifndef mingw32_HOST_OS
\end{code}

\HDRb{Nice Symbols for OS X/Unix}


\begin{code}
s_pi    = "\x03C0"
s_eps   = "\x03F5"
s_tau   = "\x03C4"
s_Sigma = "\x2211"
s_top   = "\x22A4"
s_bot   = "\x22A5"
\end{code}


\begin{code}
\end{code}


\begin{code}
#else
\end{code}

\HDRb{``Nice'' Symbols for Windows }

\begin{code}
s_pi = "pi"
s_eps   = "eps"
s_tau   = "tau"
s_Sigma = "Sigma"
s_top   = "top"
s_bot   = "bot"
\end{code}

\begin{code}
#endif
\end{code}

\HDRb{Platform Independent Code}

\begin{code}
nice
 = [ "s_pi    = "++s_pi
   , "s_eps   = "++s_eps
   , "s_tau   = "++s_tau
   , "s_Sigma = "++s_Sigma
   , "s_top   = "++s_top
   , "s_bot   = "++s_bot
   ]
\end{code}
\begin{code}
main
 = do putStrLn $ unlines nice
\end{code}
