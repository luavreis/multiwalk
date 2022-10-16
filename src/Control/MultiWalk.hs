{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.MultiWalk (walkM, FList (..), MultiWalkTag (..), MultiWalk (..)) where

import Data.Kind (Constraint, Type)
import Control.HasSub

class
  All (MultiWalk tag) (MultiWalkTypes tag) =>
  MultiWalkTag tag
  where
  type MultiWalkTypes tag :: [Type]

class
  ( All (HasSub' tag t) (SubTypes t),
    All (MultiWalk tag) (SubTypes t),
    WalkAllSub tag (SubTypes t),
    FContains t (MultiWalkTypes tag)
  ) =>
  MultiWalk tag t
  where
  type SubTypes t :: [Type]

walkM ::
  forall tag m a.
  ( Monad m,
    MultiWalk tag a
  ) =>
  FList m (MultiWalkTypes tag) ->
  a ->
  m a
walkM fs x = walkAllSub @tag @(SubTypes a) fs x

walkSub ::
  forall tag m a t.
  ( Monad m,
    HasSub' tag a t,
    MultiWalk tag t
  ) =>
  FList m (MultiWalkTypes tag) ->
  (t -> m t) ->
  a ->
  m a
walkSub fs f x =
  setSub @tag x <$> (walkM @tag fs =<< f (getSub @tag x))

type family AllSubTypes (ls :: [Type]) :: [[Type]] where
  AllSubTypes '[] = '[]
  AllSubTypes (t : ts) = SubTypes t : AllSubTypes ts

class MultiWalkTag tag => WalkAllSub tag (ls :: [Type]) where
  walkAllSub ::
    forall m t.
    ( Monad m,
      All (HasSub' tag t) ls,
      All (MultiWalk tag) ls
    ) =>
    FList m (MultiWalkTypes tag) ->
    t ->
    m t

instance MultiWalkTag tag => WalkAllSub tag '[] where
  walkAllSub _ = pure

instance
  ( WalkAllSub tag xs
  ) =>
  WalkAllSub tag (x : xs)
  where
  walkAllSub ::
    forall m t.
    ( Monad m,
      All (HasSub' tag t) (x : xs),
      All (MultiWalk tag) (x : xs)
    ) =>
    FList m (MultiWalkTypes tag) ->
    t ->
    m t
  walkAllSub fs a =
    walkSub @tag fs (fGet @x fs) a
      >>= walkAllSub @tag @xs @m @t fs

-- | @All p as@ ensures that the constraint @p@ is satisfied by all the 'types' in
--   @as@.
type family All (p :: k -> Constraint) (as :: [k]) :: Constraint where
  All p '[] = ()
  All p (a ': as) = (p a, All p as)

data FList :: (Type -> Type) -> [Type] -> Type where
  FNil :: FList m '[]
  (:.:) :: (x -> m x) -> FList m xs -> FList m (x : xs)

class FContains (t :: Type) (l :: [Type]) where
  fGet :: FList m l -> t -> m t

instance {-# OVERLAPS #-} FContains t (t : xs) where
  fGet (x :.: _) = x

instance FContains t xs => FContains t (x : xs) where
  fGet (_ :.: xs) = fGet xs
