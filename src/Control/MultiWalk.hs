{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.MultiWalk
  ( query,
    multiQuery,
    walkM,
    multiWalkM,
    FList (..),
    MultiWalk (..),
    (.>),
    (?>),
  )
where

import Control.HasSub
import Data.Foldable (fold)
import Data.Kind (Constraint, Type)

class (Traversable c, HasSub tag t (c s)) => HasSubT tag t s c

instance (Traversable c, HasSub tag t (c s)) => HasSubT tag t s c

class
  ( All (MultiWalk tag ts) (SubTypes t),
    All2 (HasSubT tag t) (SubTypes t) (Containers t),
    WalkAllSub tag (SubTypes t) (Containers t),
    QueryAllSub tag (SubTypes t) (Containers t),
    QContains t ts,
    FContains t ts
  ) =>
  MultiWalk tag ts t
  where
  type SubTypes t :: [Type]
  type Containers t :: [Type -> Type]
  type Containers t = DefaultContainers (SubTypes t)

type family DefaultContainers (xs :: [Type]) :: [Type -> Type] where
  DefaultContainers '[] = '[]
  DefaultContainers (x : xs) = [] ': DefaultContainers xs

query ::
  forall tag a m t ts.
  ( Monoid m,
    QId ts,
    QContains t ts,
    MultiWalk tag ts a
  ) =>
  (t -> m) ->
  a ->
  m
query f = multiQuery @tag (qId @ts ?> f)

walkM ::
  forall tag a m t ts.
  ( Monad m,
    FId ts,
    FContains t ts,
    MultiWalk tag ts a
  ) =>
  (t -> m t) ->
  a ->
  m a
walkM f = multiWalkM @tag (fId @ts .> f)

multiQuery ::
  forall tag a m ts.
  ( Monoid m,
    MultiWalk tag ts a
  ) =>
  QList m ts ->
  a ->
  m
multiQuery fs x =
  queryAllSub @tag @(SubTypes a) @(Containers a) fs x
    <> qGet @a fs x

multiWalkM ::
  forall tag a m ts.
  ( Monad m,
    MultiWalk tag ts a
  ) =>
  FList m ts ->
  a ->
  m a
multiWalkM fs x =
  walkAllSub @tag @(SubTypes a) @(Containers a) fs x
    >>= fGet @a fs

querySub ::
  forall tag t c m a ts.
  ( Monoid m,
    HasSubT tag a t c,
    MultiWalk tag ts t
  ) =>
  QList m ts ->
  a ->
  m
querySub fs =
  let act = fold @c . fmap (multiQuery @tag @t fs)
   in getSub @tag act

class QueryAllSub tag (ls :: [Type]) (cs :: [Type -> Type]) where
  queryAllSub ::
    forall m t ts.
    ( Monoid m,
      All2 (HasSubT tag t) ls cs,
      All (MultiWalk tag ts) ls
    ) =>
    QList m ts ->
    t ->
    m

instance QueryAllSub tag '[] '[] where
  queryAllSub = mempty

instance
  ( QueryAllSub tag xs cs
  ) =>
  QueryAllSub tag (x : xs) (c : cs)
  where
  queryAllSub ::
    forall m t ts.
    ( Monoid m,
      All2 (HasSubT tag t) (x : xs) (c : cs),
      All (MultiWalk tag ts) (x : xs)
    ) =>
    QList m ts ->
    t ->
    m
  queryAllSub fs a =
    querySub @tag @x @c fs a <> queryAllSub @tag @xs @cs @m @t fs a

walkSub ::
  forall tag t c m a ts.
  ( Monad m,
    HasSubT tag a t c,
    MultiWalk tag ts t
  ) =>
  FList m ts ->
  a ->
  m a
walkSub fs =
  let act = mapM @c (multiWalkM @tag @t fs)
   in modSub @tag act

class WalkAllSub tag (ls :: [Type]) (cs :: [Type -> Type]) where
  walkAllSub ::
    forall m t ts.
    ( Monad m,
      All2 (HasSubT tag t) ls cs,
      All (MultiWalk tag ts) ls
    ) =>
    FList m ts ->
    t ->
    m t

instance WalkAllSub tag '[] '[] where
  walkAllSub _ = pure

instance
  ( WalkAllSub tag xs cs
  ) =>
  WalkAllSub tag (x : xs) (c : cs)
  where
  walkAllSub ::
    forall m t ts.
    ( Monad m,
      All2 (HasSubT tag t) (x : xs) (c : cs),
      All (MultiWalk tag ts) (x : xs)
    ) =>
    FList m ts ->
    t ->
    m t
  walkAllSub fs a =
    walkSub @tag @x @c fs a
      >>= walkAllSub @tag @xs @cs @m @t fs

type family All2 (p :: k -> l -> Constraint) (as :: [k]) (bs :: [l]) :: Constraint where
  All2 p '[] '[] = ()
  All2 p (a ': as) (b ': bs) = (p a b, All2 p as bs)

type family All (p :: k -> Constraint) (as :: [k]) :: Constraint where
  All p '[] = ()
  All p (a ': as) = (p a, All p as)

data QList :: Type -> [Type] -> Type where
  QNil :: QList m '[]
  (:?:) :: (x -> m) -> QList m xs -> QList m (x : xs)

class QId ls where
  qId :: Monoid m => QList m ls

instance QId '[] where
  qId = QNil

instance QId xs => QId (x : xs) where
  qId = mempty :?: qId

(?>) :: QContains t ls => QList m ls -> (t -> m) -> QList m ls
(?>) = qSet

class QContains (t :: Type) (l :: [Type]) where
  qGet :: QList m l -> t -> m
  qSet :: QList m l -> (t -> m) -> QList m l

instance {-# OVERLAPS #-} QContains t (t : xs) where
  qGet (x :?: _) = x
  qSet (_ :?: y) z = (z :?: y)

instance QContains t xs => QContains t (x : xs) where
  qGet (_ :?: xs) = qGet xs
  qSet (x :?: y) z = (x :?: qSet y z)

data FList :: (Type -> Type) -> [Type] -> Type where
  FNil :: FList m '[]
  (:.:) :: (x -> m x) -> FList m xs -> FList m (x : xs)

class FId ls where
  fId :: Monad m => FList m ls

instance FId '[] where
  fId = FNil

instance FId xs => FId (x : xs) where
  fId = pure :.: fId

(.>) :: FContains t ls => FList m ls -> (t -> m t) -> FList m ls
(.>) = fSet

class FContains (t :: Type) (l :: [Type]) where
  fGet :: FList m l -> t -> m t
  fSet :: FList m l -> (t -> m t) -> FList m l

instance {-# OVERLAPS #-} FContains t (t : xs) where
  fGet (x :.: _) = x
  fSet (_ :.: y) z = (z :.: y)

instance FContains t xs => FContains t (x : xs) where
  fGet (_ :.: xs) = fGet xs
  fSet (x :.: y) z = (x :.: fSet y z)
