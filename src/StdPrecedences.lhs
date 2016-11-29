\HDRa{Standard Precedences}\label{ha:std-precs}
\begin{code}
module StdPrecedences where
\end{code}

%\input{src/Precedences} -- need to add/commit

\newpage
\HDRb{Standard Predicates}\label{hb:standard-preds}

We provide syntax precedence values
for a fairly standard predicate language as follows:
\STANDARD

In the code we move these up and spread them out,
making it easier to fit other constructs around them
\begin{code}
precSpacer :: Int -> Int
precSpacer n = 100 + 10 * n
\end{code}

Predicate precedences, higher is tighter, 0 is ``loosest''.
\begin{code}
precEqv   = precSpacer  1
precImp   = precSpacer  2
precOr    = precSpacer  5
precAnd   = precSpacer  6
precNot   = precSpacer  8
precEq    = precSpacer  9
precSbs   = precSpacer 10
\end{code}

Expression precedences
\begin{code}
precAdd = precSpacer 11
precSub = precSpacer 11
precMul = precSpacer 12
precDiv = precSpacer 12
\end{code}
