\HDRa{Calculator Zipper}\label{ha:calc-zipper}
\begin{code}
module CalcZipper where
import CalcTypes
import CalcPredicates
import CalcSysTypes
\end{code}


\HDRb{Zipper Setup}

\begin{code}
startMPZ :: MPred -> MPZipper
startMPZ mp = ( mp, [] )
\end{code}

\HDRb{Going Deeper}

We go down by specifying which sub-component, if necessary,
with components numbered from 0 upwards
\begin{code}
downMPZ :: Int -> MPZipper -> MPZipper
downMPZ _ ( (PSub pr subs, MT ms [smt]), ss )
         = ( (pr, smt), (PSub' subs, MT' ms [] []) : ss )
downMPZ i ( (Comp name prs, MT ms mts), ss )
 | 0 <= i && i < length prs
   = (  (pri, mi), (Comp' name before after, MT' ms mbef maft) : ss )
   where
     ( before, (pri:after) ) = splitAt i prs
     ( mbef, (mi:maft) ) = splitAt i mts
downMPZ _ mpz = mpz -- default case, do nothing
\end{code}

\HDRb{Coming Back Up}

We can plug an \texttt{MPred} into a\texttt{ MPred'} to get an \texttt{MPred},
effectively moving up one level
\begin{code}
plugMPZ :: MPred' -> MPred -> MPred
plugMPZ (Comp' name before after, MT' ms mbef maft) (pr, mt)
                            =  ( Comp name (before++pr:after)
                               , MT ms (mbef++mt:maft) )
plugMPZ (PSub' subs, MT' ms _ _) (pr, mt)  =  (PSub pr subs, MT ms [mt])
\end{code}

We then lift this to work with a zipper
where the top-most (inner-most) step is first
\begin{code}
upMPZ :: MPZipper -> MPZipper
upMPZ ( mpr, (s:ss) ) = ( plugMPZ s mpr, ss )
upMPZ mpz = mpz -- taken if currently at top
\end{code}

\HDRb{Modifying the Focus}

\begin{code}
updateMPZ :: (MPred -> MPred)
          -> MPZipper -> MPZipper
updateMPZ f ( mpr, ss ) = ( f mpr, ss )
\end{code}

\HDRb{Exiting the Zipper}

We can unzip by repeatedly plugging in:
\begin{code}
unzipMPZ :: [MPred'] -> MPred -> MPred
unzipMPZ [] mpr = mpr
unzipMPZ (s:ss) mpr = unzipMPZ ss $ plugMPZ s mpr
\end{code}

We exit by unzipping as above:
\begin{code}
exitMPZ :: MPZipper -> MPred
exitMPZ ( mpr, ss ) = unzipMPZ ss mpr
\end{code}
