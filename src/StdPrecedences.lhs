\HDRa{Standard Precedences}\label{ha:std-precs}
\begin{code}
module StdPrecedences where
\end{code}

\HDRb{Syntax}

We provide dictionary entries that instantiate particular composites
to produce
a fairly standard UTP predicate language as follows:
\RLEQNS{
   p \in P &::=& \ldots & \mbox{As per \secref{hc:PredData}}
\\ &|& \top & \mbox{(Lattice) Top, a.k.a. miracle}
\\ &|& \bot & \mbox{(Lattice) Bottom, a.k.a. abort/Chaos}
\\ &|& \lnot p  & \mbox{Negation}
\\ &|& p_1 \land p_2 \land \ldots \land p_n  & \mbox{Conjunction}
\\ &|& p_1 \lor p_2 \lor \ldots \lor p_n & \mbox{Disjunction}
\\ &|& p_1 \ndc p_2 \ndc \ldots \ndc p_n & \mbox{Non-Det. Choice}
\\ &|& p_1 \implies p_2 & \mbox{Implication}
\\ &|& p_1 \refinedby p_2 & \mbox{Refinement}
\\ &|& p_1 \cond{p_2} p_3 & \mbox{Conditional}
\\ &|& \Skip & \mbox{Skip}
\\ &|& p_1 \seq p_2 & \mbox{Sequencing}
\\ &|& p_1 * p_2 & \mbox{Iteration}
}

\newpage
\HDRb{Precedences}

These are the current precedence levels for predicates,
determined by the following \emph{choices}%
\footnote{These are not laws,
just conventions we feel are most useful
for the kinds of things we usually write.}%
:
\RLEQNS{
   P \refinedby Q \implies R &=& P \refinedby (Q \implies R) & \refinedby_1
\\ P \implies Q \cond R S &=& P \implies (Q \cond R S) & \implies_2
\\ P \cond Q R \seq S     &=& P \cond Q (R \seq D)     & \cond\!_3
\\ P \seq Q \lor R        &=& P \seq (Q \lor R)        & \seq_4
\\ P \lor Q \land R       &=& P \lor (Q \land R)       & \lor_5, \ndc_5
\\ P \land c * Q          &=& P \land (c * Q)          & \land_6
\\ \lnot c * P            &=& (\lnot c) * P            & *_7
\\ \lnot e = f            &=& \lnot(e=f)               & \lnot_8
\\ e = f[e/x]             &=& e = (f[e/x])             & =_9, [/]_{10}
}

In the code we move these up and spread them out,
making it easier to fit other constructs around them
\begin{code}
precSpacer :: Int -> Int
precSpacer n = 100 + 10 * n
\end{code}
Now, precedences, higher is tighter, 0 is ``loosest''.
\begin{code}
precRfdby = precSpacer  1
precImp   = precSpacer  2
precCond  = precSpacer  3
precSeq   = precSpacer  4
precOr    = precSpacer  5
precNDC   = precSpacer  5
precAnd   = precSpacer  6
precIter  = precSpacer  7
precNot   = precSpacer  8
precEq    = precSpacer  9
precSub   = precSpacer 10
\end{code}

Hold these in reserve
\begin{verbatim}
-- precPCond = 1
-- precPPar  = 2
-- precPSeq  = 3
-- precPIter = 6
\end{verbatim}
