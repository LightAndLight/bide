{-# language GADTs, DataKinds, StandaloneDeriving #-}
{-# language BangPatterns #-}
{-# options_ghc -fwarn-incomplete-patterns #-}
module Syntax where

import Control.Applicative ((<|>))
import Data.Maybe

data Cat = C | S

data Syntax cat where
  -- Constructors, or introduction forms
  Type :: Syntax 'C
  Pi :: Syntax 'C -> Syntax 'C -> Syntax 'C
  Lambda :: Syntax 'C -> Syntax 'C

  -- Destructors, or elimination forms
  App :: Syntax 'S -> Syntax 'C -> Syntax 'S

  Embed :: Syntax 'S -> Syntax 'C
  Ann :: Syntax 'C -> Syntax 'C -> Syntax 'S

  Var :: !Int -> Syntax 'S
  Name :: !String -> Syntax 'S

deriving instance Eq (Syntax cat)
deriving instance Show (Syntax cat)

mkPi :: String -> Syntax 'C -> Syntax 'C -> Syntax 'C
mkLambda :: String -> Syntax 'C -> Syntax 'C

(mkPi, mkLambda) = (mkPi', mkLambda')
  where
    mkPi' a b c = Pi b (abstract a c)
    mkLambda' a b = Lambda $ abstract a b

    abstract :: String -> Syntax a -> Syntax a
    abstract name = go 0
      where
        go :: Int -> Syntax a -> Syntax a
        go !depth e =
          case e of
            Type -> Type
            Pi a b -> Pi (go depth a) (go (depth+1) b)
            Lambda a -> Lambda $ go (depth+1) a
            App a b -> App (go depth a) (go depth b)
            Embed a -> Embed $ go depth a
            Ann a b -> Ann (go depth a) (go depth b)
            Var n
              | n >= depth -> Var (n+1)
              | otherwise -> Var n
            Name s
              | s == name -> Var depth
              | otherwise -> Name s

subst :: Syntax 'S -> Syntax a -> Syntax a
subst x = go 0
  where
    go :: Int -> Syntax a -> Syntax a
    go !depth e =
      case e of
        Type -> Type
        Pi a b -> Pi (go depth a) (go (depth+1) b)
        Lambda a -> Lambda $ go (depth+1) a
        App a b -> App (go depth a) (go depth b)
        Embed a -> Embed $ go depth a
        Ann a b -> Ann (go depth a) (go depth b)
        Var n ->
          case compare n depth of
            LT -> Var n
            EQ -> x
            GT -> Var (n-1)
        Name a -> Name a

-- | head = most recently bound variable
type Context = [Syntax 'S]

index :: Int -> [a] -> Maybe a
index _ [] = Nothing
index n (a:as) =
  case compare n 0 of
    LT -> Nothing
    EQ -> Just a
    GT -> index (n-1) as

{- |

Σ(chk, (syn)chk)chk
σ(chk, chk)dst

⋆ ∋ S    x : S ⊢ ⋆ ∋ T(x)
————————————————————————
   ⋆ ∋ Σ(S, x. T[x])


 S ∋ s    T(s : S) ∋ t
———————————————————————
Σ(S, x. T[x]) ∋ σ(s, t)

-}
isTypeOf :: Context -> Syntax 'C -> Syntax 'C -> Bool
isTypeOf = pre
  where
    pre :: Context -> Syntax 'C -> Syntax 'C -> Bool
    pre context ty tm =
      let
        ty' = normalise context ty
      in
        go context ty' tm

    go :: Context -> Syntax 'C -> Syntax 'C -> Bool
    -- Wew! Feel the wind in your hair
    go context ty Type = ty == Type
    go context ty (Embed e) =
      case inferType context e of
        Nothing -> False
        Just ty' -> ty == ty'
    go context ty (Pi s t) =
      isTypeOf context Type s &&
      isTypeOf (Ann s Type : context) Type t &&
      ty == Type
    go context ty (Lambda x) =
      case ty of
        Pi s t ->
          isTypeOf context Type s &&
          isTypeOf (Ann s Type : context) t x
        _ -> False

inferType :: Context -> Syntax 'S -> Maybe (Syntax 'C)
inferType = post
  where
    post :: Context -> Syntax 'S -> Maybe (Syntax 'C)
    post context tm = normalise context <$> go context tm

    go :: Context -> Syntax 'S -> Maybe (Syntax 'C)
    go context Name{} = error "no rule for name"
    go context (Var n) =
      case index n context of
        Just (Ann _ t) -> Just t
        _ -> Nothing
    go context (Ann tm ty)
      | isTypeOf context Type ty, isTypeOf context ty tm = Just tm
      | otherwise = Nothing
    go context (App f x) = do
      fTy <- inferType context f
      case fTy of
        Pi s t | isTypeOf context s x -> Just $ subst (Ann x s) t
        _ -> Nothing

step :: Context -> Syntax cat -> Maybe (Syntax cat)
step context e =
  case e of
    Type -> Nothing
    Pi{} -> Nothing
    Lambda{} -> Nothing
    App f x ->
      (\f' -> App f' x) <$> step context f <|>
      App f <$> step context x <|>
      case f of
        Ann (Lambda a) (Pi b c) ->
          Just $ Ann (subst (Ann x b) a) (subst (Ann x b) c)
        _ -> error "stuck - applying argument to non-function"
    Embed (Ann a _) -> Just a
    Embed a -> Embed <$> step context a
    Ann a b ->
      (\a' -> Ann a' b) <$> step context a <|>
      Ann a <$> step context b
    Var n ->
      Just .
      fromMaybe
        (error $ "stuck - bound variable (" ++ show n ++ ") not in context (" ++ show context ++ ")")
        (index n context)
    Name{} -> error "stuck - named variable not in context"

steps :: (a -> Maybe a) -> a -> a
steps f = go where go a = maybe a go (f a)

normalise :: Context -> Syntax cat -> Syntax cat
normalise context = steps (step context)

test4 :: Bool
test4 =
  isTypeOf
    []
    (mkPi "x" Type $ mkPi "y" (Embed $ Name "x") (Embed $ Name "x"))
    (mkLambda "x" $ mkLambda "y" $ Embed $ Name "y")

identity :: Syntax 'S
identity =
  Ann
    (mkLambda "x" $ mkLambda "y" $ Embed $ Name "y")
    (mkPi "x" Type $ mkPi "y" (Embed $ Name "x") (Embed $ Name "x"))
