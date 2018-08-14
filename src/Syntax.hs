{-# language GADTs, DataKinds, StandaloneDeriving #-}
module Syntax where

data Constructor = Type
  deriving (Eq, Show)

data Destructor = DD
  deriving (Eq, Show)

data Cat = C | S

data Syntax cat where
  Ctor :: Constructor -> Syntax 'C
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
isTypeOf = pre
  where
    pre :: Context -> Syntax 'C -> Syntax 'C -> Bool
    pre context ty tm =
      let
        ty' = steps step ty
      in
        go context ty' tm

    go :: Context -> Syntax 'C -> Syntax 'C -> Bool
    go context ty (Bracket e) =
      case inferType context e of
        Nothing -> False
        Just ty' -> ty == ty'

inferType :: Context -> Syntax 'S -> Maybe (Syntax 'C)
inferType = post
  where
    post :: Context -> Syntax 'S -> Maybe (Syntax 'C)
    post context tm = steps step <$> go context tm

    go :: Context -> Syntax 'S -> Maybe (Syntax 'C)
    go context (Var n) = index n context
    go context (Ann tm ty)
      | isTypeOf context (Ctor Type) ty, isTypeOf context ty tm = Just tm
      | otherwise = Nothing
    go context s = undefined

step :: Syntax cat -> Maybe (Syntax cat)
step = undefined

steps :: (a -> Maybe a) -> a -> a
steps f = go
  where
    go a = maybe a go (f a)
