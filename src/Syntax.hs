{-# language GADTs, DataKinds, StandaloneDeriving #-}
module Syntax where

data Constructor
data Destructor

data Cat = C | S

data Syntax cat where
  Constructor :: Constructor -> Syntax 'C
  Lambda :: Syntax 'S -> Syntax 'C
  Var :: Int -> Syntax 'S
  Ann :: Syntax 'C -> Syntax 'C -> Syntax 'S
  App :: Syntax 'S -> Destructor -> Syntax 'S
deriving instance Eq (Syntax cat)
deriving instance Show (Syntax cat)

-- | head = most recently bound variable
type Context = [Syntax 'C]

isTypeOf :: Context -> Syntax 'C -> Syntax 'C -> Bool
isTypeOf = undefined

hasType :: Context -> Syntax 'S -> Maybe (Syntax 'C)
hasType (Var n) = context !! n

step :: Syntax cat -> Maybe (Syntax cat)
step = undefined
