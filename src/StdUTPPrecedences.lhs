\HDRa{Standard UTP Precedences}\label{ha:std-UTP-precs}
\begin{code}
module StdUTPPrecedences where
import StdPrecedences
\end{code}

%\input{src/Precedences}

\newpage
\HDRb{Standard UTP Predicates}\label{hb:standard-UTP-preds}

We provide syntax precedence values
for common UTP program/specification constructs as follows:
\UTPSTANDARD

Now, standard UTP precedences, higher is tighter, 0 is ``loosest'':
\begin{code}
precRfdby = precSpacer  1
precCond  = precSpacer  3
precSeq   = precSpacer  4
precNDC   = precSpacer  5
precIter  = precSpacer  7
\end{code}
