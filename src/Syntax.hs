{-# language GADTs, DataKinds, StandaloneDeriving #-}
{-# language BangPatterns #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language ScopedTypeVariables #-}
{-# language ExistentialQuantification #-}
{-# language FlexibleContexts #-}
{-# options_ghc -fwarn-incomplete-patterns #-}
module Syntax where

import Control.Applicative ((<|>))
import Control.Monad ((<=<))
import Control.Monad.State (StateT, runStateT, gets, modify)
import Control.Monad.Reader
  (MonadReader, ReaderT, runReaderT, ask, asks, local)
import Control.Monad.Trans.Class (lift)
import Data.Maybe (fromMaybe)

import SMT

data Cat = C | S

data Syntax v cat where
  -- Constructors, or introduction forms
  Type :: !(Maybe v) -> Syntax v 'C
  Pi :: Syntax v 'C -> Syntax v 'C -> Syntax v 'C
  Lambda :: Syntax v 'C -> Syntax v 'C
  Fst :: Syntax v 'C
  Snd :: Syntax v 'C
  Sigma :: Syntax v 'C -> Syntax v 'C -> Syntax v 'C
  MkSigma :: Syntax v 'C -> Syntax v 'C -> Syntax v 'C

  -- Destructors, or elimination forms
  App :: Syntax v 'S -> Syntax v 'C -> Syntax v 'S

  Embed :: Syntax v 'S -> Syntax v 'C
  Ann :: Syntax v 'C -> Syntax v 'C -> Syntax v 'S

  Var :: !Int -> Syntax v 'S
  Name :: !String -> Syntax v 'S

_Type :: Syntax v 'C
_Type = Type Nothing

deriving instance Eq v => Eq (Syntax v cat)
deriving instance Show v => Show (Syntax v cat)

abstract :: String -> Syntax v a -> Syntax v a
abstract name = go 0
  where
    go :: Int -> Syntax v a -> Syntax v a
    go !depth e =
      case e of
        Fst -> Fst
        Snd -> Snd
        Type i -> Type i
        Pi a b -> Pi (go depth a) (go (depth+1) b)
        Lambda a -> Lambda $ go (depth+1) a
        App a b -> App (go depth a) (go depth b)
        Sigma a b -> Sigma (go depth a) (go (depth+1) b)
        MkSigma a b -> MkSigma (go depth a) (go depth b)
        Embed a -> Embed $ go depth a
        Ann a b -> Ann (go depth a) (go depth b)
        Var n
          | n >= depth -> Var (n+1)
          | otherwise -> Var n
        Name s
          | s == name -> Var depth
          | otherwise -> Name s

mkPi :: String -> Syntax v 'C -> Syntax v 'C -> Syntax v 'C
mkPi a b c = Pi b (abstract a c)

mkSigma :: String -> Syntax v 'C -> Syntax v 'C -> Syntax v 'C
mkSigma a b c = Sigma b (abstract a c)

mkLambda :: String -> Syntax v 'C -> Syntax v 'C
mkLambda a b = Lambda $ abstract a b

subst :: forall v a. Syntax v 'S -> Syntax v a -> Syntax v a
subst x = go 0
  where
    go :: forall b. Int -> Syntax v b -> Syntax v b
    go !depth e =
      case e of
        Fst -> Fst
        Snd -> Snd
        Type i -> Type i
        Pi a b -> Pi (go depth a) (go (depth+1) b)
        Sigma a b -> Sigma (go depth a) (go (depth+1) b)
        MkSigma a b -> MkSigma (go depth a) (go depth b)
        Lambda a -> Lambda $ go (depth+1) a
        App a b -> App (go depth a) (go depth b)
        Embed a -> Embed $ go depth a
        Ann a b -> Ann (go depth a) (go depth b)
        Var n ->
          case compare n depth of
            LT -> Var n
            EQ -> x
            GT -> Var $ n-1
        Name a -> Name a

index :: Int -> [a] -> Maybe a
index _ [] = Nothing
index n (a:as) =
  case compare n 0 of
    LT -> Nothing
    EQ -> Just a
    GT -> index (n-1) as

data TCEnv v
  = TCEnv
  { _globalBindings :: [(String, Syntax v 'S)]
  , _localBindings :: [Syntax v 'S]
  }

data TCState v
  = TCState
  { _constraints :: [Con v]
  , _nameSupply :: [v]
  }

data TCError v
  = TCError
  | forall s t. TypeMismatch { expected :: Syntax v s, got :: Syntax v t }
  | forall s. ExpectedPi { got :: Syntax v s }
  | forall s. ExpectedSigma { got :: Syntax v s }
  | UniverseInconsistency
  | NameNotFound
deriving instance Show v => Show (TCError v)

newtype TC v a
  = TC
  { unTC
    :: ReaderT
         (TCEnv v)
         (StateT
            (TCState v)
            (Either (TCError v)))
         a
  }
  deriving (Functor, Applicative, Monad, MonadReader (TCEnv v))

runTC :: [(String, Syntax Int 'S)] -> TC Int a -> Either (TCError Int) a
runTC global (TC m) = do
  let
    initialEnv =
      TCEnv
      { _globalBindings = global
      , _localBindings = []
      }

    initialState =
      TCState
      { _constraints = []
      , _nameSupply = [0..]
      }

  (res, TCState cs _) <- runStateT (runReaderT m initialEnv) initialState
  if hasSolution cs
    then Right res
    else Left UniverseInconsistency

constrain :: Con v -> TC v ()
constrain c = TC . modify $ \s -> s { _constraints = c : _constraints s }

freshName :: TC v v
freshName =
  TC $ do
    v : vs <- gets _nameSupply
    modify $ \s -> s { _nameSupply = vs }
    pure v

tcError :: TCError v -> TC v a
tcError = TC . lift . lift . Left

tyEquiv
  :: Eq v
  => Syntax v s
  -> Syntax v t
  -> TC v (Bool, Syntax v s, Syntax v t)
tyEquiv (Pi s t) (Pi u v) = do
  (res1, s', u') <- tyEquiv s u
  (res2, t', v') <- tyEquiv t v
  pure (res1 && res2, Pi s' t', Pi u' v')
tyEquiv (Sigma s t) (Sigma u v) = do
  (res1, s', u') <- tyEquiv s u
  (res2, t', v') <- tyEquiv t v
  pure (res1 && res2, Sigma s' t', Sigma u' v')
tyEquiv (Type a) (Type b) = do
  i <- maybe freshName pure a
  j <- maybe freshName pure b
  constrain (Eq (V i) (V j))
  pure (True, Type (Just i), Type (Just j))
tyEquiv t (Ann u v) = do
  (res, t', u') <- tyEquiv t u
  pure (res, t', Ann u' v)
tyEquiv (Ann t u) v = do
  (res, t', v') <- tyEquiv t v
  pure (res, Ann t' u, v')
tyEquiv Fst Fst = pure (True, Fst, Fst)
tyEquiv Snd Snd = pure (True, Fst, Fst)
tyEquiv a (Embed b) = do
  (res, a', b') <- tyEquiv a b
  pure (res, a', Embed b')
tyEquiv (Embed a) b = do
  (res, a', b') <- tyEquiv a b
  pure (res, Embed a', b')
tyEquiv (Lambda a) (Lambda b) = do
  (res, a', b') <- tyEquiv a b
  pure (res, Lambda a', Lambda b')
tyEquiv (MkSigma s t) (MkSigma u v) = do
  (res1, s', u') <- tyEquiv s u
  (res2, t', v') <- tyEquiv t v
  pure (res1 && res2, MkSigma s' t', MkSigma u' v')
tyEquiv (App s t) (App u v) = do
  (res1, s', u') <- tyEquiv s u
  (res2, t', v') <- tyEquiv t v
  pure (res1 && res2, App s' t', App u' v')
tyEquiv a@(Name s) b@(Name t) = pure (s == t, a, b)
tyEquiv a@(Var s) b@(Var t) = pure (s == t, a, b)
tyEquiv a b = tcError $ TypeMismatch { expected = a, got = b }

{- |

Σ(chk, (syn)chk)chk
σ(chk, chk)chk

⋆ ∋ S    x : S ⊢ ⋆ ∋ T(x)
————————————————————————
   ⋆ ∋ Σ(S, x. T[x])


 S ∋ s    T(s : S) ∋ t
———————————————————————
Σ(S, x. T[x]) ∋ σ(s, t)


⋆ ∋ S   x : S ⊢ ⋆ ∋ T(x)    S = U
—————————————————————————————————
  fst ∋ Pi (y : Σ(S, x. T[x]) U

⋆ ∋ S   x : S ⊢ ⋆ ∋ T(x)   T(fst y) = U
———————————————————————————————————————
 snd ∋ Pi (y : Σ(S, x. T[x]) U

-}
isTypeOf :: (Eq v, Show v) => Syntax v 'C -> Syntax v 'C -> TC v (Syntax v 'C)
isTypeOf = pre
  where
    pre ty tm = do
      ty' <- normalise ty
      go ty' tm

    go :: (Eq v, Show v) => Syntax v 'C -> Syntax v 'C -> TC v (Syntax v 'C)
    go ty Fst =
      case ty of
        Pi (Sigma s t) u -> do
          type_i <- Type . Just <$> freshName
          s' <- isTypeOf type_i s
          t' <-
            local
              (\e -> e { _localBindings = Ann s' type_i : _localBindings e })
              (isTypeOf type_i t)
          (eq, s'', u') <- s' `tyEquiv` u
          if eq
            then pure $ Pi (Sigma s'' t') u'
            else tcError $ TypeMismatch { expected = s, got = u }
        _ -> tcError $ ExpectedPi { got = ty }
    go ty Snd =
      case ty of
        Pi (Sigma s t) u -> do
          type_i <- Type . Just <$> freshName
          s' <- isTypeOf type_i s
          t' <-
            local
              (\e -> e { _localBindings = Ann s' type_i : _localBindings e })
              (isTypeOf type_i t)
          let
            newSig = Sigma s' t'
            tFstY =
              abstract "y"
                (subst
                   (App (Ann Fst $ mkPi "z" newSig s') $ Embed $ Name "y")
                   t')
          (eq, _, u') <- tFstY `tyEquiv` u
          if eq
            then pure $ Pi newSig u'
            else tcError $ TypeMismatch { expected = tFstY, got = u }
        _ -> tcError $ ExpectedPi { got = ty }
    go ty (Type mi) =
      case ty of
        Type mj -> do
          i <- maybe freshName pure mi
          j <- maybe freshName pure mj
          constrain (Lt (V i) (V j))
          pure $ Type (Just i)
        _ -> tcError $ TypeMismatch { expected = Type Nothing, got = ty }
    go ty (Sigma s t) = do
      type_i <- Type . Just <$> freshName
      s' <- isTypeOf type_i s
      t' <-
        local
          (\e -> e { _localBindings = Ann s' type_i : _localBindings e })
          (isTypeOf type_i t)
      (eq, _, _) <- ty `tyEquiv` type_i
      if eq
        then pure $ Sigma s' t'
        else tcError $ TypeMismatch { expected = Type Nothing, got = ty }
    go ty (MkSigma s t) =
      case ty of
        Sigma sTy tTy -> do
          s' <- isTypeOf sTy s
          t' <-
            local
              (\e -> e { _localBindings = Ann s' sTy : _localBindings e })
              (isTypeOf tTy t)
          pure $ MkSigma s' t'
        _ -> tcError $ ExpectedSigma { got = ty }
    go ty (Embed e) = do
      ty' <- inferType e
      (eq, _, _) <- ty `tyEquiv` ty'
      if eq
        then pure $ Embed e
        else tcError $ TypeMismatch { expected = ty, got = ty' }
    go ty (Pi s t) = do
      type_i <- Type . Just <$> freshName
      s' <- isTypeOf type_i s
      t' <-
        local
          (\e -> e { _localBindings = Ann s' type_i : _localBindings e })
          (isTypeOf type_i t)
      (eq, _, _) <- ty `tyEquiv` type_i
      if eq
        then pure $ Pi s' t'
        else tcError $ TypeMismatch { expected = Type Nothing, got = ty }
    go ty (Lambda x) =
      case ty of
        Pi s t -> do
          type_i <- Type . Just <$> freshName
          s' <- isTypeOf type_i s
          x' <-
            local
              (\e -> e { _localBindings = Ann s' type_i : _localBindings e })
              (isTypeOf t x)
          pure $ Lambda x'
        _ -> tcError $ ExpectedPi { got = ty }

inferType :: (Eq v, Show v) => Syntax v 'S -> TC v (Syntax v 'C)
inferType = post
  where
    post = normalise <=< go

    go :: (Eq v, Show v) => Syntax v 'S -> TC v (Syntax v 'C)
    go Name{} = error "no rule for name"
    go (Var n) = do
      context <- asks _localBindings
      case index n context of
        Just (Ann _ t) -> pure t
        _ -> tcError NameNotFound
    go (Ann tm ty) = do
      type_i <- Type . Just <$> freshName
      ty' <- isTypeOf type_i ty
      _ <- isTypeOf ty' tm
      pure ty'
    go (App f x) = do
      fTy <- inferType f
      case fTy of
        Pi s t -> do
          s' <- isTypeOf s x
          pure $ subst (Ann x s') t
        _ -> tcError $ ExpectedPi { got = fTy }

step :: TCEnv v -> Syntax v cat -> Maybe (Syntax v cat)
step tcEnv e =
  case e of
    Fst -> Nothing
    Snd -> Nothing
    Sigma a b ->
      (\a' -> Sigma a' b) <$> step tcEnv a <|>
      Sigma a <$> step tcEnv b
    MkSigma a b ->
      (\a' -> MkSigma a' b) <$> step tcEnv a <|>
      MkSigma a <$> step tcEnv b
    Type{} -> Nothing
    Pi{} -> Nothing
    Lambda{} -> Nothing
    App f x ->
      (\f' -> App f' x) <$> step tcEnv f <|>
      App f <$> step tcEnv x <|>
      case f of
        Ann (Lambda a) (Pi b c) ->
          Just $ Ann (subst (Ann x b) a) (subst (Ann x b) c)
        _ -> error "stuck - applying argument to non-function"
    Embed (Ann a _) -> Just a
    Embed a -> Embed <$> step tcEnv a
    Ann a b ->
      (\a' -> Ann a' b) <$> step tcEnv a <|>
      Ann a <$> step tcEnv b
    Var n ->
      Just $
      fromMaybe
        (error $ "stuck - bound variable not in context")
        (index n $ _localBindings tcEnv)
    Name{} -> Nothing

steps :: (a -> Maybe a) -> a -> a
steps f = go where go a = maybe a go (f a)

normalise :: MonadReader (TCEnv v) m => Syntax v cat -> m (Syntax v cat)
normalise s = ($ s) . steps . step <$> ask

_ID = mkPi "x" _Type $ mkPi "y" (Embed $ Name "x") (Embed $ Name "x")
_id = mkLambda "x" $ mkLambda "y" $ Embed $ Name "y"

test3 :: Either (TCError Int) (Syntax Int 'C)
test3 = runTC [] $ isTypeOf _Type _ID

test4 :: Either (TCError Int) (Syntax Int 'C)
test4 = runTC [] $ isTypeOf _ID _id

test5 :: Either (TCError Int) (Syntax Int 'C)
test5 =
  runTC [] $
  isTypeOf
    (mkPi "x" _ID _ID)
    (Embed $ App (Ann _id _ID) _ID)

test6 :: Either (TCError Int) (Syntax Int 'C)
test6 =
  runTC [] $
  isTypeOf
    _ID
    (Embed $ App (App (Ann _id _ID) _ID) _id)

test7 :: Either (TCError Int) (Syntax Int 'C)
test7 =
  runTC [] $
  isTypeOf
    (mkPi "x" _Type _Type)
    (Embed $ App (Ann _id _ID) _Type)

test8 :: Either (TCError Int) (Syntax Int 'C)
test8 =
  runTC [] $
  isTypeOf
    _Type
    (Embed $ App (App (Ann _id _ID) _Type) _Type)

test9 :: Either (TCError Int) (Syntax Int 'C)
test9 =
  runTC [] $ do
    isTypeOf
      (Type $ Just 1) -- type-with-name-1 is the type of type-with-name-0
      (Type $ Just 0) -- which implies the constraint var(0) < var(1)

    local
      (const $ TCEnv [] [Ann (Type $ Just 0) (Type $ Just 1)])
      (isTypeOf
        -- (type-with-name-0 : type-with-name-1) : (type-with-name-0 : type-with-name-1)
        (Embed $ Var 0) -- this introduces the constraint var(1) = var(0)
        (Embed $ Var 0)) -- which is a contradiction, given var(0) < var(1)

identity :: Syntax v 'S
identity =
  Ann
    (mkLambda "x" $ mkLambda "y" $ Embed $ Name "y")
    (mkPi "x" _Type $ mkPi "y" (Embed $ Name "x") (Embed $ Name "x"))
