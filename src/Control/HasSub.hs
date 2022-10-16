{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}

module Control.HasSub where

import Control.Applicative (Applicative (liftA2))
import Data.Coerce (Coercible, coerce)
import Data.Functor.Compose (Compose (..))
import Data.Functor.Identity (Identity (..))
import Data.Kind (Constraint, Type)
import GHC.Generics
import GHC.TypeLits (ErrorMessage (..), TypeError)

class HasSub tag t s where
  modSub :: Applicative m => (s -> m s) -> t -> m t
  getSub :: Monoid m => (s -> m) -> t -> m
  default modSub ::
    ( Generic t,
      HasSub' s (Rep t),
      -- ContainsSome s (Rep t) t,
      Applicative m
    ) =>
    (s -> m s) ->
    t ->
    m t
  modSub f = fmap to . modSub' f . from
  default getSub ::
    ( Generic t,
      HasSub' s (Rep t),
      -- ContainsSome s (Rep t) t,
      Monoid m
    ) =>
    (s -> m) ->
    t ->
    m
  getSub f = getSub' f . from

data GTag t

-- Generic instance

instance {-# INCOHERENT #-} (Generic t, HasSub' s (Rep t), ContainsSome s (Rep t) t) => HasSub (GTag a) t s

-- Other useful instances

-- | Use this for matching with another type that is coercible to the functor you want.
newtype MatchWith s (g :: Type -> Type) a = MatchWith (g a)
  deriving (Eq, Ord, Show, Functor, Foldable, Generic)

instance (Traversable g) => Traversable (MatchWith s g) where
  traverse f (MatchWith xs) = MatchWith <$> traverse f xs
  sequenceA (MatchWith xs) = MatchWith <$> sequenceA xs

instance (HasSub tag t l, Coercible l (g s)) => HasSub tag t (MatchWith l g s) where
  modSub f = modSub @tag @t @l (fmap coerce . f . coerce)
  getSub f = getSub @tag @t @l (f . coerce)

-- | Use this for matching a subcomponent nested inside another type. Useful if
-- you don't want to add the middle type to the list of walkable types.
newtype Under (f :: Type -> Type) (b :: Type) (g :: Type -> Type) a = Under (g a)
  deriving (Eq, Ord, Show, Functor, Foldable, Generic)

instance (Traversable g) => Traversable (Under f b g) where
  traverse f (Under xs) = Under <$> traverse f xs
  sequenceA (Under xs) = Under <$> sequenceA xs

instance (Traversable f, HasSub tag a (f b), HasSub tag b (g c)) => HasSub tag a (Under f b g c) where
  modSub :: forall m. Applicative m => (Under f b g c -> m (Under f b g c)) -> a -> m a
  modSub f =
    let f' :: g c -> m (g c) = fmap coerce . f . coerce
     in modSub @tag @a @(f b) (traverse $ modSub @tag @b @(g c) f')
  getSub :: forall m. Monoid m => (Under f b g c -> m) -> a -> m
  getSub f =
    let f' :: g c -> m = f . coerce
     in getSub @tag @a @(f b) (foldMap $ getSub @tag @b @(g c) f')

-- | Instance for types wrapped around the identity functor
instance (HasSub tag t s) => HasSub tag t (Identity s) where
  modSub f = modSub @tag @t @s (fmap coerce . f . coerce)
  getSub f = getSub @tag @t @s (f . coerce)

-- Generic code

class HasSub' s t where
  modSub' :: Applicative m => (s -> m s) -> t p -> m (t p)
  getSub' :: Monoid m => (s -> m) -> t p -> m

instance {-# OVERLAPPING #-} HasSub' s (K1 j s) where
  modSub' f (K1 x) = K1 <$> f x
  getSub' f (K1 x) = f x

-- instance {-# OVERLAPPING #-} HasSub' (Identity s) (K1 j s) where
--   modSub' f (K1 x) = K1 <$> runIdentity <$> f (Identity x)
--   getSub' f (K1 x) = f (Identity x)

instance HasSub' s (K1 j t) where
  modSub' _ = pure
  getSub' _ = mempty

instance (HasSub' s x, HasSub' s y) => HasSub' s (x :*: y) where
  modSub' f (x :*: y) = liftA2 (:*:) (modSub' f x) (modSub' f y)
  getSub' f (x :*: y) = getSub' f x <> getSub' f y

instance HasSub' s U1 where
  modSub' _ = pure
  getSub' _ = mempty

instance (HasSub' s x, HasSub' s y) => HasSub' s (x :+: y) where
  modSub' f (L1 x) = L1 <$> modSub' f x
  modSub' f (R1 x) = R1 <$> modSub' f x
  getSub' f (L1 x) = getSub' f x
  getSub' f (R1 x) = getSub' f x

instance (HasSub' s x) => HasSub' s (M1 a b x) where
  modSub' f (M1 x) = M1 <$> modSub' f x
  getSub' f (M1 x) = getSub' f x

type family Or (a :: Constraint) (b :: Constraint) :: Constraint where
  Or () b = ()
  Or a () = ()

type family ClearProd s t :: Constraint where
  ClearProd s (S1 i (K1 j s)) = ()
  ClearProd s (xs :*: ys) = ClearProd s xs `Or` ClearProd s ys

type family ClearSum s t :: Constraint where
  ClearSum s (C1 _ xs) = ClearProd s xs
  ClearSum s (xs :+: ys) = ClearSum s xs `Or` ClearSum s ys

type family ContainsSome s t pt :: Constraint where
  ContainsSome s (D1 _ xs) pt =
    ClearSum s xs
      `Or` TypeError
             ( 'Text "Type "
                 ':<>: 'ShowType pt
                 ':<>: 'Text " does not contain any constructor with a field of type "
                 ':<>: 'ShowType s
             )

data Foo = Foo String [[Int]]
  deriving (Generic)

test :: HasSub (GTag ()) Foo (MatchWith ([[Int]]) (Compose [] []) Int) => ()
test = ()

test2 :: HasSub (GTag ()) Foo (Identity Int) => ()
test2 = ()
