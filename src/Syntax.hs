{-# language GADTs, DataKinds, StandaloneDeriving #-}
module Syntax where

data Constructor = Type
  deriving (Eq, Show)

data Destructor = DD
  deriving (Eq, Show)

data Cat = C | S

data Syntax cat where
  Constructor :: Constructor -> Syntax 'C
  Bracket :: Syntax 'S -> Syntax 'C
  Var :: Int -> Syntax 'S
  Ann :: Syntax 'C -> Syntax 'C -> Syntax 'S
  App :: Syntax 'S -> Destructor -> Syntax 'S
deriving instance Eq (Syntax cat)
deriving instance Show (Syntax cat)

-- | head = most recently bound variable
type Context = [Syntax 'C]

index :: Int -> [a] -> Maybe a
index 0 (a:_) = Just a
index n (_:as)
  | n < 0 = Nothing
  | otherwise = index (n-1) as

isTypeOf :: Context -> Syntax 'C -> Syntax 'C -> Bool
isTypeOf context ty (Bracket e) =
  case inferType context e of
    Nothing -> False
    Just ty' -> ty == ty'

inferType :: Context -> Syntax 'S -> Maybe (Syntax 'C)
inferType context (Var n) = index n context
inferType context (Ann tm ty)
  | isTypeOf context (Constructor Type) ty, isTypeOf context ty tm = Just tm
  | otherwise = Nothing
inferType context s = undefined

step :: Syntax cat -> Maybe (Syntax cat)
step = undefined
