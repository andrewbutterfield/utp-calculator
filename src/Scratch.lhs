\HDRa{Scratch}\label{ha:SCRATCH}
\begin{code}
module Scratch where -- we rapidly prototype stuff
\end{code}

We define a very simple abstract syntax for generators:
\[
  G ::= g | \ell_G | G: | G1 | G2
\]
\begin{code}
data G = V | L G | N G | S1 G | S2 G deriving (Eq,Ord)

instance Show G where
  show V = "g"
  show (L g) = 'l':show g
  show (N g) = show g ++ ":"
  show (S1 g) = show g ++ "1"
  show (S2 g) = show g ++ "2"

instance Read G where
  readsPrec _ = readG

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
parseG' g (':':rest) = parseG' (N g) rest
parseG' g ('1':rest) = parseG' (S1 g) rest
parseG' g ('2':rest) = parseG' (S2 g) rest
parseG' _ _ = fail "not a valid generator expression"
\end{code}
