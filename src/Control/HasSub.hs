{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module Control.HasSub where

import Control.Applicative (liftA2)
import Data.Coerce (Coercible, coerce)
import Data.Functor.Identity (Identity)
import Data.Kind (Constraint, Type)
import GHC.Generics

infixr 8 :?:

data QList :: Type -> [Type] -> Type where
  QNil :: QList m '[]
  (:?:) :: (x -> m) -> QList m xs -> QList m (x : xs)

class QContains (l :: [Type]) (t :: Type) where
  qGet :: QList m l -> t -> m
  qSet :: QList m l -> (t -> m) -> QList m l

instance {-# OVERLAPS #-} QContains (t : xs) t where
  qGet (f :?: _) = f
  qSet (_ :?: y) z = z :?: y

instance QContains xs t => QContains (x : xs) t where
  qGet (_ :?: y) = qGet y
  qSet (x :?: y) z = x :?: qSet y z


infixr 8 :.:

data FList :: (Type -> Type) -> [Type] -> Type where
  FNil :: FList m '[]
  (:.:) :: (x -> m x) -> FList m xs -> FList m (x : xs)

class FContains (l :: [Type]) (t :: Type) where
  fGet :: FList m l -> t -> m t
  fSet :: FList m l -> (t -> m t) -> FList m l

instance {-# OVERLAPS #-} FContains (t : xs) t where
  fGet (f :.: _) = f
  fSet (_ :.: y) z = z :.: y

instance FContains xs t => FContains (x : xs) t where
  fGet (_ :.: y) = fGet y
  fSet (x :.: y) z = x :.: fSet y z

class HasSub ls cs t where
  modSub :: (Applicative m, All (FContains fs) ls) => FList m fs -> t -> m t
  getSub :: (Monoid m, All (QContains fs) ls) => QList m fs -> t -> m

instance HasSub '[] '[] t where
  modSub _ = pure
  getSub _ = mempty

instance (Generic t, HasSub' (l : ls) (c : cs) (Rep t)) => HasSub (l : ls) (c : cs) t where
  modSub f = fmap to . modSub' @(l : ls) @(c : cs) f . from
  getSub f = getSub' @(l : ls) @(c : cs) f . from

-- Useful combinators

-- | Use this for matching with another type that is coercible to the functor you want.
newtype MatchWith s g a = MatchWith (g a)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

-- | Use this for matching a subcomponent nested inside another type. Useful if
-- you don't want to add the middle type to the list of walkable types.
newtype Under (f :: Type -> Type) (b :: Type) (g :: Type -> Type) a = Under (g a)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

-- Generic code

type family All (p :: k -> Constraint) (as :: [k]) :: Constraint where
  All p '[] = ()
  All p (a ': as) = (p a, All p as)

class HasSub' (ls :: [Type]) (cs :: [Type -> Type]) (t :: Type -> Type) where
  modSub' :: (Applicative m, All (FContains fs) ls) => FList m fs -> t p -> m (t p)
  getSub' :: (Monoid m, All (QContains fs) ls) => QList m fs -> t p -> m

instance (Traversable f, HasSub '[c] '[g] b) => HasSub' (c : ls) (Under f b g : cs) (K1 j (f b)) where
  modSub' fs (K1 x) = K1 <$> traverse (modSub @'[c] @'[g] fs) x
  getSub' fs (K1 x) = foldMap (getSub @'[c] @'[g] fs) x

instance (Coercible l (g s), Traversable g) => HasSub' (s : ls) (MatchWith l g : cs) (K1 j l) where
  modSub' fs (K1 x) = K1 . coerce <$> traverse (fGet fs) (coerce x :: g s)
  getSub' fs (K1 x) = foldMap (qGet fs) (coerce x :: g s)

instance Traversable t => HasSub' (s : ls) (t : cs) (K1 j (t s)) where
  modSub' fs (K1 x) = K1 <$> traverse (fGet fs) x
  getSub' fs (K1 x) = foldMap (qGet fs) x

instance HasSub' (s : ls) (Identity : cs) (K1 j s) where
  modSub' fs (K1 x) = K1 <$> fGet fs x
  getSub' fs (K1 x) = qGet fs x

instance {-# OVERLAPPABLE #-} HasSub' ls cs (K1 j s) => HasSub' (l : ls) (c : cs) (K1 j s) where
  modSub' = modSub' @ls @cs
  getSub' = getSub' @ls @cs

instance HasSub' '[] '[] (K1 j t) where
  modSub' _ = pure
  getSub' _ = mempty

instance (HasSub' s c x, HasSub' s c y) => HasSub' s c (x :*: y) where
  modSub' f (x :*: y) = liftA2 (:*:) (modSub' @s @c f x) (modSub' @s @c f y)
  getSub' f (x :*: y) = getSub' @s @c f x <> getSub' @s @c f y

instance HasSub' s cs U1 where
  modSub' _ = pure
  getSub' _ = mempty

instance (HasSub' s c x, HasSub' s c y) => HasSub' s c (x :+: y) where
  modSub' f (L1 x) = L1 <$> modSub' @s @c f x
  modSub' f (R1 x) = R1 <$> modSub' @s @c f x
  getSub' f (L1 x) = getSub' @s @c f x
  getSub' f (R1 x) = getSub' @s @c f x

instance (HasSub' s c x) => HasSub' s c (M1 a b x) where
  modSub' f (M1 x) = M1 <$> modSub' @s @c f x
  getSub' f (M1 x) = getSub' @s @c f x
