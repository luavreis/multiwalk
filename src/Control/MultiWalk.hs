{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.MultiWalk
  ( query,
    walkM,
    buildMultiW,
    buildMultiQ,
    (.>),
    (?>),
    Walk,
    Query,
    FList (..),
    QList (..),
    MultiTag (..),
    MultiWalk (..),
  )
where

import Control.HasSub
import Control.Monad ((>=>))
import Data.Kind (Type)

class
  ( BuildF (MultiWalk tag) (MultiTypes tag),
    BuildQ (MultiWalk tag) (MultiTypes tag)
  ) =>
  MultiTag tag
  where
  type MultiTypes tag :: [Type]

class
  ( All (QContains (MultiTypes tag)) (SubTypes t),
    All (FContains (MultiTypes tag)) (SubTypes t),
    QContains (MultiTypes tag) t,
    FContains (MultiTypes tag) t,
    HasSub (SubTypes t) (Containers t) t
  ) =>
  MultiWalk tag t
  where
  type SubTypes t :: [Type]
  type Containers t :: [Type -> Type]
  type Containers t = DefaultContainers (SubTypes t)

type family DefaultContainers (xs :: [Type]) :: [Type -> Type] where
  DefaultContainers '[] = '[]
  DefaultContainers (x : xs) = [] ': DefaultContainers xs

query ::
  forall tag m t a.
  ( MultiTag tag,
    MultiWalk tag a,
    MultiWalk tag t,
    Monoid m
  ) =>
  (t -> m) ->
  a ->
  m
query f =
  buildMultiQ @tag $ \go l ->
    l ?> \x -> f x <> go x

walkM ::
  forall tag a m t.
  ( Monad m,
    MultiTag tag,
    MultiWalk tag a,
    MultiWalk tag t
  ) =>
  (t -> m t) ->
  a ->
  m a
walkM f =
  buildMultiW @tag $ \go l ->
    l .> (f >=> go)

type Query tag m = forall t. MultiWalk tag t => t -> m

buildMultiQ ::
  forall tag m a.
  (MultiTag tag, MultiWalk tag a, Monoid m) =>
  ( Query tag m ->
    QList m (MultiTypes tag) ->
    QList m (MultiTypes tag)
  ) ->
  a ->
  m
buildMultiQ f = qGet qlist
  where
    qlist :: QList m (MultiTypes tag)
    qlist = f go $ buildQ @(MultiWalk tag) go
    go :: forall s. MultiWalk tag s => s -> m
    go = getSub @(SubTypes s) @(Containers s) qlist

type Walk tag m = forall t. MultiWalk tag t => t -> m t

buildMultiW ::
  forall tag m a.
  (MultiTag tag, MultiWalk tag a, Applicative m) =>
  ( Walk tag m ->
    FList m (MultiTypes tag) ->
    FList m (MultiTypes tag)
  ) ->
  a ->
  m a
buildMultiW f = fGet flist
  where
    flist :: FList m (MultiTypes tag)
    flist = f go $ buildF @(MultiWalk tag) go
    go :: forall s. MultiWalk tag s => s -> m s
    go = modSub @(SubTypes s) @(Containers s) flist

class All c ls => BuildQ c ls where
  buildQ :: (forall t. c t => t -> m) -> QList m ls

instance BuildQ c '[] where
  buildQ _ = QNil

instance (BuildQ c ls, c l) => BuildQ c (l : ls) where
  buildQ f = f :?: buildQ @c @ls f

class All c ls => BuildF c ls where
  buildF :: (forall t. c t => t -> m t) -> FList m ls

instance BuildF c '[] where
  buildF _ = FNil

instance (BuildF c ls, c l) => BuildF c (l : ls) where
  buildF f = f :.: buildF @c @ls f

(?>) :: QContains ls t => QList m ls -> (t -> m) -> QList m ls
(?>) = qSet

(.>) :: FContains ls t => FList m ls -> (t -> m t) -> FList m ls
(.>) = fSet
