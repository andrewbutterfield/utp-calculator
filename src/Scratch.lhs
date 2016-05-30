\HDRa{Scratch}\label{ha:SCRATCH}
\begin{code}
module Scratch where -- we rapidly prototype stuff
import Data.List
import Data.Maybe
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

-- g = V
-- (lg,g',g1,g2)     = split4 g
-- (lg',g'',g'1,g'2) = split4 g'
-- (lg'1,g'1',g'11,g'12) = split4 g'1
-- (lg1,g1',g11,g12) = split4 g1
-- (lg2,g2',g21,g22) = split4 g2
\end{code}

\newpage
\HDRb{Label-Set Invariants}

\RLEQNS{
   i \in I_\tau &::=& \tau \mid \otimes(i,\ldots,i) \mid \cup (i,\ldots,i)
}
\begin{code}
data I t = I t | U [I t] | X [I t] deriving Show
\end{code}

We shall assume labels are integers.
We want to take an invariant over labels
and a label-set to get the same structure over booleans.
This is the label occupancy structure:
\RLEQNS{
   occ &:& \power \Int \fun I_\Int \fun I_\Bool
\\ occ_L~\ell &\defs& \ell \in L
\\ occ_L~\otimes(i_1,\ldots,i_n)
   &\defs&
   \otimes(occ_L~i_1,\ldots,occ_L~i_n)
\\ occ_L~\cup(i_1,\ldots,i_n)
   &\defs&
   \cup(occ_L~i_1,\ldots,occ_L~i_n)
}
\begin{code}
occ :: Eq t => [t] -> I t -> I Bool
occ ls (I ell) = I (ell `elem`ls)
occ ls (U invs) = U $ map (occ ls) invs
occ ls (X invs) = X $ map (occ ls) invs
\end{code}

We now take a $I_\Bool$ and reduce it to a boolean
that asserts satisfaction.
In effect we look for failures
(can only come from $\oplus$)
and propagate these up.
\RLEQNS{
   prop &:& I_\Bool \fun (\setof{ok,fail}\times \Bool)
\\ prop(b) &\defs& (ok,true)
\\ prop(\cup(i_1,\ldots,i_n))
   &\defs&
   (fail,\_),
   \textbf{ if }\exists j @ prop(i_j) = (fail,\_)
\\ && (ok,b_1 \lor \dots \lor b_n),
   \textbf{ if }\forall j @ prop(i_j) = (ok,b_j)
\\ prop(\otimes(i_1,\ldots,i_n))
   &\defs&
   (fail,\_),
   \textbf{ if }\exists j @ prop(i_j) = (fail,\_)
\\&& (fail,\_) \mbox{ if more than one $(ok,true)$}
\\&& (ok,false) \mbox{ if all are $(ok,false)$}
\\&& (ok,true) \mbox{ if  exactly one $(ok,true)$}
}
\begin{code}
prop :: I Bool -> Maybe Bool
prop (I b) = Just b
prop (U occs)
 = do ps <- sequence $ map prop occs
      return $ any id ps
prop (X occs)
 = do ps <- sequence $ map prop occs
      let ps' = filter id ps
      case length ps' of
        0  ->  return False
        1  ->  return True
        _  ->  fail "not-exclusive"
\end{code}

\newpage
Put it all together:
\begin{code}
sat :: Eq t => I t -> [t] -> Bool
sat inv ls = isJust $ prop $ occ ls inv
\end{code}

Parallel composition invariant:
\[
  [in|[\ell_{g1}|\ell_{g1:}],[\ell_{g2}|\ell_{g2:}]|out]
\quad
\mbox{ using new notation}
\quad
  \otimes(in,\cup(\otimes(\ell_{g1},\ell_{g1:})
                  ,\otimes(\ell_{g2},\ell_{g2:})),out)
\]
\begin{code}
inp  =  1
out  =  2
lg1  =  3
lg1' =  4
lg2  =  5
lg2' =  6
inv  =  X [ I inp
          , U [ X [ I lg1, I lg1' ]
              , X [ I lg2, I lg2' ]
              ]
          , I out
          ]
lgen :: [a] -> [[a]]
lgen [] = [[]]
lgen (x:xs)
 = xs' ++ map (x:) xs'
 where xs' = lgen xs

par6 = lgen [1..6]
par7 = lgen [1..7]

apply ls = (inv `sat` ls,ls)

res6 = map apply par6
res7 = map apply par7

showres [] = return ()
showres ((b,ls):rest)
  = do if b then putStr "OK   "
            else putStr "FAIL "
       putStrLn $ show ls
       showres rest

split [] = ([],[])
split (l:r:rest) = (l:left,r:right)
 where (left,right) = split rest

irrelevant7 = (map fst left == map fst right)
 where (left,right) = split res7
\end{code}

\newpage
If we do \texttt{showres res6} we get:


\begin{verbatim}
     [ 1 |  ([ 3 | 4 ],[ 5 | 6 ]) | 2 ]

OK   []  yes
OK   [6]  yes
OK   [5]  yes
FAIL [5,6]  yes
OK   [4]  yes
OK   [4,6]  yes
OK   [4,5]  yes
FAIL [4,5,6]  yes
OK   [3]  yes
OK   [3,6]  yes
OK   [3,5]  yes
FAIL [3,5,6]  yes
FAIL [3,4]  yes
FAIL [3,4,6]  yes
FAIL [3,4,5]  yes
FAIL [3,4,5,6]  yes
OK   [2]  yes
FAIL [2,6]  yes
FAIL [2,5]  yes
FAIL [2,5,6]  yes
FAIL [2,4]  yes
FAIL [2,4,6]  yes
FAIL [2,4,5]  yes
FAIL [2,4,5,6]  yes
FAIL [2,3]  yes
FAIL [2,3,6]  yes
FAIL [2,3,5]  yes
FAIL [2,3,5,6]  yes
FAIL [2,3,4]  yes
FAIL [2,3,4,6]  yes
FAIL [2,3,4,5]  yes
FAIL [2,3,4,5,6]  yes
\end{verbatim}
\newpage
\begin{verbatim}
     [ 1 |  ([ 3 | 4 ],[ 5 | 6 ]) | 2 ]
-- all OK below
OK   [1]
FAIL [1,6]
FAIL [1,5]
FAIL [1,5,6]
FAIL [1,4]
FAIL [1,4,6]
FAIL [1,4,5]
FAIL [1,4,5,6]
FAIL [1,3]
FAIL [1,3,6]
FAIL [1,3,5]
FAIL [1,3,5,6]
FAIL [1,3,4]
FAIL [1,3,4,6]
FAIL [1,3,4,5]
FAIL [1,3,4,5,6]
FAIL [1,2]
FAIL [1,2,6]
FAIL [1,2,5]
FAIL [1,2,5,6]
FAIL [1,2,4]
FAIL [1,2,4,6]
FAIL [1,2,4,5]
FAIL [1,2,4,5,6]
FAIL [1,2,3]
FAIL [1,2,3,6]
FAIL [1,2,3,5]
FAIL [1,2,3,5,6]
FAIL [1,2,3,4]
FAIL [1,2,3,4,6]
FAIL [1,2,3,4,5]
FAIL [1,2,3,4,5,6]
\end{verbatim}
