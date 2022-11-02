{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Control.MultiWalk.HasSub where

import Control.Applicative (liftA2)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import GHC.Generics

data SubSpec = SubSpec Type Type

type family SpecCarrier (t :: SubSpec) where
  SpecCarrier ('SubSpec a _) = a

class HasSub tag (ls :: [SubSpec]) t where
  modSub ::
    forall c m.
    (Applicative m, All c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> SpecCarrier s -> m (SpecCarrier s)) ->
    t ->
    m t
  getSub ::
    forall c m.
    (Monoid m, All c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> SpecCarrier s -> m) ->
    t ->
    m

instance HasSub tag '[] t where
  modSub _ _ = pure
  getSub _ _ = mempty

data GSubTag

instance (Generic t, HasSub' (l : ls) (Rep t)) => HasSub GSubTag (l : ls) t where
  modSub p f = fmap to . modSub' @(l : ls) p f . from
  getSub p f = getSub' @(l : ls) p f . from

-- Generic code

type family All (p :: k -> Constraint) (as :: [k]) :: Constraint where
  All p '[] = ()
  All p (a ': as) = (p a, All p as)

class HasSub' (ls :: [SubSpec]) (t :: Type -> Type) where
  modSub' ::
    forall c m p.
    (Applicative m, All c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> SpecCarrier s -> m (SpecCarrier s)) ->
    t p ->
    m (t p)
  getSub' ::
    forall c m p.
    (Monoid m, All c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> SpecCarrier s -> m) ->
    t p ->
    m

instance HasSub' ('SubSpec tc tt : ls) (K1 j tc) where
  modSub' _ f (K1 x) = K1 <$> f (Proxy @('SubSpec tc tt)) x
  getSub' _ f (K1 x) = f (Proxy @('SubSpec tc tt)) x

instance {-# OVERLAPPABLE #-} HasSub' ls (K1 j s) => HasSub' (l : ls) (K1 j s) where
  modSub' = modSub' @ls
  getSub' = getSub' @ls

instance HasSub' '[] (K1 j t) where
  modSub' _ _ = pure
  getSub' _ _ = mempty

instance (HasSub' s x, HasSub' s y) => HasSub' s (x :*: y) where
  modSub' p f (x :*: y) = liftA2 (:*:) (modSub' @s p f x) (modSub' @s p f y)
  getSub' p f (x :*: y) = getSub' @s p f x <> getSub' @s p f y

instance HasSub' s U1 where
  modSub' _ _ = pure
  getSub' _ _ = mempty

instance (HasSub' s x, HasSub' s y) => HasSub' s (x :+: y) where
  modSub' p f (L1 x) = L1 <$> modSub' @s p f x
  modSub' p f (R1 x) = R1 <$> modSub' @s p f x
  getSub' p f (L1 x) = getSub' @s p f x
  getSub' p f (R1 x) = getSub' @s p f x

instance (HasSub' s x) => HasSub' s (M1 a b x) where
  modSub' p f (M1 x) = M1 <$> modSub' @s p f x
  getSub' p f (M1 x) = getSub' @s p f x
