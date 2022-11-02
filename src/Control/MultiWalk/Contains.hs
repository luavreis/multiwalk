{-# LANGUAGE GADTs #-}

module Control.MultiWalk.Contains where

import Control.MultiWalk.HasSub (All, SpecCarrier, HasSub (..), SubSpec (..))
import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))

modSubWithFList ::
  forall tag ls t fs m.
  (HasSub tag ls t, Applicative m, All (TContains fs) ls) =>
  FList m fs ->
  t ->
  m t
modSubWithFList fs =
  modSub @tag @ls @t (Proxy @(TContains fs)) (\(_ :: Proxy s) -> tGetW @fs @s fs)

getSubWithQList ::
  forall tag ls t fs m.
  (HasSub tag ls t, Monoid m, All (TContains fs) ls) =>
  QList m fs ->
  t ->
  m
getSubWithQList fs =
  getSub @tag @ls @t (Proxy @(TContains fs)) (\(_ :: Proxy s) -> tGetQ @fs @s fs)

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

type family CombinatorCarrier (b :: Type) :: Type where
  CombinatorCarrier (Under tag s a) = s
  CombinatorCarrier (MatchWith s a) = s
  CombinatorCarrier (Trav f a) = f a
  CombinatorCarrier a = a

type BuildSpec (b :: Type) = 'SubSpec (CombinatorCarrier b) b

class TContains (fs :: [Type]) (t :: SubSpec) where
  tGetW :: Applicative m => FList m fs -> SpecCarrier t -> m (SpecCarrier t)
  tGetQ :: Monoid m => QList m fs -> SpecCarrier t -> m

instance
  {-# OVERLAPPABLE #-}
  (FContains fs a, QContains fs a) =>
  TContains fs ('SubSpec a a)
  where
  tGetW = fGet
  tGetQ = qGet

-- Useful combinators

-- | Use this for matching with a type inside a traversable functor.
data Trav (k :: Type -> Type) (a :: Type)

instance
  ( Traversable f,
    FContains fs a,
    QContains fs a
  ) =>
  TContains fs ('SubSpec (f a) (Trav f a))
  where
  tGetW = traverse . fGet
  tGetQ = foldMap . qGet

-- | Use this for matching with another type that is coercible to the functor you want.
data MatchWith (s :: Type) (a :: Type)

instance
  ( TContains fs (BuildSpec a),
    Coercible (CombinatorCarrier a) s
  ) =>
  TContains fs ('SubSpec s (MatchWith s a))
  where
  tGetW fs = fmap coerce . tGetW @fs @(BuildSpec a) fs . coerce
  tGetQ fs = tGetQ @fs @(BuildSpec a) fs . coerce

-- | Use this for matching a subcomponent nested inside another type. Useful if
-- you don't want to add the middle type to the list of walkable types.
data Under (tag :: Type) (b :: Type) (a :: Type)

instance
  ( TContains fs (BuildSpec a),
    HasSub tag '[BuildSpec a] b
  ) =>
  TContains fs ('SubSpec b (Under tag b a))
  where
  tGetW = modSubWithFList @tag @'[BuildSpec a] @b @fs
  tGetQ = getSubWithQList @tag @'[BuildSpec a] @b @fs
