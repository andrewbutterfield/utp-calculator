\HDRa{POrd}\label{ha:POrd}
\begin{code}
module POrd where
\end{code}


We need to define a partial-order class.
\texttt{Data.Poset} is not suitable as it ``overloads'' \texttt{Ord}.
Others require various type/class extensions I prefer to avoid.
The following is inspired by Wren Romano's \texttt{Data.Numbers.Ord}.

First, we need an ordering datatype that allows an incomparable outcome:
\begin{code}
data POrdering = PNC | PLT | PEQ | PGT deriving (Eq, Show)
\end{code}

Then we define the partial order class and methods
\begin{code}
class Eq t => POrd t where
  pcmp :: t -> t -> POrdering
  lt   :: t -> t -> Bool
  le   :: t -> t -> Bool
  gt   :: t -> t -> Bool
  ge   :: t -> t -> Bool
  nc   :: t -> t -> Bool
\end{code}

We consider the minimal definition to be \texttt{pcmp},
and define the others in terms of this.
\begin{code}
  lt a b = pcmp a b == PLT

  le a b = case pcmp a b of
            PLT  ->  True
            PEQ  ->  True
            _    ->  False

  gt a b = pcmp a b == PGT

  ge a b = case pcmp a b of
            PGT  ->  True
            PEQ  ->  True
            _    ->  False

  nc a b = pcmp a b == PNC
\end{code}
We add the following,
so enabling \texttt{lt} as another minimal definition.
\begin{code}
  pcmp a b
   | a  ==  b  =  PEQ
   | a `lt` b  =  PLT
   | b `lt` a  =  PGT
   | otherwise =  PNC
\end{code}
