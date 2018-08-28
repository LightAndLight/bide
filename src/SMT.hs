{-# options_ghc -fwarn-incomplete-patterns #-}
module SMT where

data Atom v = V v | N Int
  deriving (Eq, Show)

data Con v
  = Lt (Atom v) (Atom v)
  | Eq (Atom v) (Atom v)
  deriving (Eq, Show)

runEq :: Eq v => Atom v -> Atom v -> Con v -> [Con v]
runEq a b (Lt c d) | b == c = [Lt a d]
runEq a b (Eq c d) | b == c = [Eq a d]
runEq a b (Lt c d) | a == c = [Lt b d]
runEq a b (Eq c d) | a == c = [Eq b d]
runEq _ _ e = [e]

runLt :: Eq v => Atom v -> Atom v -> Con v -> [Con v]
runLt a b (Lt c d) | b == c = [Lt a d]
runLt a b (Eq c d) | b == c = [Lt a d]
runLt a b (Eq c d) | a == c = [Lt d b]
runLt _ _ e = [e]

hasSolution :: Eq v => [Con v] -> Bool
hasSolution [] = True
hasSolution (c : cs) =
  case c of
    Eq (N a) (N b) -> a == b && hasSolution cs
    Lt (N a) (N b) -> a < b && hasSolution cs

    Eq (V a) (V b) | a == b -> hasSolution cs
    Lt (V a) (V b) | a == b -> False

    Eq a b -> hasSolution (runEq a b =<< cs)
    Lt a b -> hasSolution (runLt a b =<< cs)
