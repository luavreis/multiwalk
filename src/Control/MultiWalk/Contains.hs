{-# LANGUAGE GADTs #-}

module Control.MultiWalk.Contains (
  module Control.MultiWalk.HasSub,
  module Control.MultiWalk.Contains,
) where

import Control.MultiWalk.HasSub hiding (Carrier, HasSub (..), ToSpec, ToSpecSel)
import qualified Control.MultiWalk.HasSub as HS
import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))

data MWCTag

type family ContainsCarrier (a :: Type) :: Type where
  ContainsCarrier (Under b s a) = b
  ContainsCarrier (MatchWith s a) = s
  ContainsCarrier (Trav f a) = f (Carrier a)
  ContainsCarrier a = a

type instance HS.Carrier MWCTag a = ContainsCarrier a
type instance HS.Carrier MWCTag a = ContainsCarrier a

type HasSub tag ls t = HS.HasSub MWCTag tag ls t
type Carrier a = HS.Carrier MWCTag a
type ToSpec a = HS.ToSpec MWCTag a
type ToSpecSel s a = HS.ToSpecSel MWCTag s a

modSubWithFList ::
  forall tag ls t fs m.
  (HasSub tag ls t, Applicative m, AllMods (TContains fs) ls) =>
  FList m fs ->
  t ->
  m t
modSubWithFList fs =
  HS.modSub @MWCTag @tag @ls @t (Proxy @(TContains fs)) (\(_ :: Proxy s) -> tGetW @fs @s fs)

getSubWithQList ::
  forall tag ls t fs m.
  (HasSub tag ls t, Monoid m, AllMods (TContains fs) ls) =>
  QList m fs ->
  t ->
  m
getSubWithQList fs =
  HS.getSub @MWCTag @tag @ls @t (Proxy @(TContains fs)) (\(_ :: Proxy s) -> tGetQ @fs @s fs)

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

class TContains (fs :: [Type]) (t :: Type) where
  tGetW :: Applicative m => FList m fs -> ContainsCarrier t -> m (ContainsCarrier t)
  tGetQ :: Monoid m => QList m fs -> ContainsCarrier t -> m

instance
  {-# OVERLAPPABLE #-}
  ( FContains fs (Carrier a)
  , QContains fs (Carrier a)
  ) =>
  TContains fs a
  where
  tGetW = fGet
  tGetQ = qGet

-- Useful combinators

-- | Use this for matching with a type inside a traversable functor.
data Trav (k :: Type -> Type) (a :: Type)

instance
  ( Traversable f
  , TContains fs a
  ) =>
  TContains fs (Trav f a)
  where
  tGetW = traverse . tGetW @fs @a
  tGetQ = foldMap . tGetQ @fs @a

-- | Use this for matching with another type that is coercible to the functor you want.
data MatchWith (s :: Type) (a :: Type)

instance
  ( TContains fs a
  , Coercible (Carrier a) s
  ) =>
  TContains fs (MatchWith s a)
  where
  tGetW fs = fmap coerce . tGetW @fs @a fs . coerce
  tGetQ fs = tGetQ @fs @a fs . coerce

{- | Use this for matching a subcomponent nested inside another type. Useful if
you don't want to add the middle type to the list of walkable types.
-}
data Under (b :: Type) (s :: SelSpec) (a :: Type)

instance
  ( TContains fs a
  , HasSub GSubTag '[ 'SubSpec s a (Carrier a)] b
  ) =>
  TContains fs (Under b s a)
  where
  tGetW = modSubWithFList @GSubTag @'[ 'SubSpec s a (Carrier a)] @b @fs
  tGetQ = getSubWithQList @GSubTag @'[ 'SubSpec s a (Carrier a)] @b @fs
