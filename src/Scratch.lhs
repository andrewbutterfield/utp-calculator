\HDRa{Scratch}\label{ha:SCRATCH}
\begin{code}
module Scratch where -- we rapidly prototype stuff
import Data.List
\end{code}

\HDRb{Generator Syntax}
We define a very simple abstract syntax for generator expressions $G$,
over a single variable $g$:
\[
  G ::= g | \ell_G | G: | G1 | G2
\]
\begin{code}
data G = V | L G | N G | S1 G | S2 G deriving (Eq,Ord)

instance Show G where
  show V = "g"
  show (L g)  = 'l':show g
  show (N g)  = show g ++ "'"
  show (S1 g) = show g ++ "1"
  show (S2 g) = show g ++ "2"

instance Read G where
  readsPrec _ = readG
    where
      readG str
       = case parseG str of
          Nothing -> []
          Just g  -> [(g,"")]

      parseG ('l':'g':rest)
       = do g <- parseG' V rest
            return $ L g
      parseG ('g':rest)
       = parseG' V rest
      parseG _ = fail "generator expression must start with g or lg"

      parseG' g "" = return g
      parseG' g ('\'':rest) = parseG' (N g) rest
      parseG' g ( '1':rest) = parseG' (S1 g) rest
      parseG' g ( '2':rest) = parseG' (S2 g) rest
      parseG' _ _ = fail "not a valid generator expression"
\end{code}


\newpage

\HDRb{Sub-Generator Relation}
We can define a sub-generator relation as follows,
where $F(G)$ is $\ell_G$, $G_:$, $G_1$ or $G_2$:
\begin{mathpar}
  \inferrule
     { }
     {G \subseteq g} [\subseteq_1]
  \and
  \inferrule
     { }
     {G \subseteq G} [\subseteq_2]
  \and
  \inferrule
    {G' \subseteq G}
    {F(G') \subseteq G} [\subseteq_3]
\end{mathpar}
\begin{code}
gsub :: G -> G -> Bool
-- [gsub_1]
g       `gsub` V       = True
-- [gsub_2]
(N ga)  `gsub` (N gb)  = ga `gsub` gb
(S1 ga) `gsub` (S1 gb) = ga `gsub` gb
(S2 ga) `gsub` (S2 gb) = ga `gsub` gb
(L ga)  `gsub` (L gb)  = ga `gsub` gb
-- [gsub_3]
(N ga)  `gsub` gb      = ga `gsub` gb
(S1 ga) `gsub` gb      = ga `gsub` gb
(S2 ga) `gsub` gb      = ga `gsub` gb
(L ga)  `gsub` gb      = ga `gsub` gb
-- none of the above
_       `gsub` _       = False

ssub :: String -> String -> Bool
ssub sa sb = gsub (read sa) (read sb)
\end{code}

\HDRb{Label Sets}

We will want to work with sets of generators,
each considered as a set of labels
\begin{eqnarray*}
   G
   &=& \ell_G \uplus {G_:} \uplus G_1 \uplus G_2
\end{eqnarray*}
where $A \uplus B$ is $A \cup B$, but only if $A \cap B = \emptyset$.
We write $A \uplus B \uplus C$ as $[A|B|C]$
to emphasise that they form a partition (of their union).
\begin{code}
newtype LS = LS [G]

instance Show LS where
 show (LS ls) = '[':(concat $ intersperse "|" $ map show ls)++"]"

nil = LS []
infixr 5 +++
(LS ls1) +++ (LS ls2) = LS (ls1++ls2)
\end{code}

\newpage
\HDRb{Generator Subtraction}

Next, generator subtraction,
where $\B F(G)$ is $\setof{\ell_G,G_:,G_1,G_2}\setminus \setof{F(G)}$.
\begin{eqnarray*}
   G - G &\defs& \emptyset
\\ G - F(G) &\defs& \uplus \B F(G)
\\ G - G'
   &\defs& \uplus \B F(G) \uplus (F(G)-G'), \quad G' \subseteq F(G)
\end{eqnarray*}

Note that $G = \uplus \B F(G) \uplus F(G)$ for any $F$.

We can establish that
\[
  g - F(G) = \uplus \B F(G) \uplus (g - G)
\]
It generalises to $g=G'$
\begin{eqnarray*}
  &      & G' - F(G) = \uplus \B F(G) \uplus (G' - G)
\\&\equiv& G' = F(G) \uplus \B F(G) \uplus (G' - G)
\\&\equiv& G' = G \uplus (G' - G)
\\&\equiv& G' = G'
\end{eqnarray*}

We have $G-g$ is $\emptyset$ if $G=g$, but is undefined otherwise,
so, to summarise:
\RLEQNS{
   G - G &\defs& \emptyset
\\ F(G) - g && \mbox{undefined}
\\ G' - F(G) &\defs& \uplus \B F(G) \uplus (G' - G)
}
\begin{code}
gminus :: Monad m => G -> G -> m LS
V       `gminus` V      = return nil
(L g')  `gminus` (L g)  = g' `gminus` g
(N g')  `gminus` (N g)  = g' `gminus` g
(S1 g') `gminus` (S1 g) = g' `gminus` g
(S2 g') `gminus` (S2 g) = g' `gminus` g
_       `gminus` V      = fail "gminus undefined"
g'      `gminus` (L g)  = do ls' <- (g' `gminus` g)
                             return (ls'+++LS[N g, S1 g, S2 g])
g'      `gminus` (N g)  = do ls' <- (g' `gminus` g)
                             return (ls' +++ LS [L g, S1 g, S2 g])
g'      `gminus` (S1 g) = do ls' <- (g' `gminus` g)
                             return (ls' +++ LS [L g, N g, S2 g])
g'      `gminus` (S2 g) = do ls' <- (g' `gminus` g)
                             return (ls' +++ LS [L g, N g, S1 g])
\end{code}

\newpage
\HDRb{Label Set Conjunction}

We interpret label-set
\[
  [L_1 | L_2 | \dots | L_n]
\]
as asserting that all the $L_i$ are mutually disjoint.
Conjunction of two such label-sets should result in a new label-set
that captures both disjointness constraints.

\HDRb{Test Values}
We would like some test values
\begin{code}
split4 :: G -> (G, G, G, G)
split4 (L _) = error "can't split a label!"
split4 g = (L g, N g, S1 g, S2 g)

g = V
(lg,g',g1,g2)     = split4 g
(lg',g'',g'1,g'2) = split4 g'
(lg'1,g'1',g'11,g'12) = split4 g'1
(lg1,g1',g11,g12) = split4 g1
(lg2,g2',g21,g22) = split4 g2
\end{code}
