{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.MultiWalk
  ( query,
    walk,
    walkM,
    walkSub,
    querySub,
    buildMultiW,
    buildMultiQ,
    (.>),
    (?>),
    Walk,
    Query,
    FList (..),
    QList (..),
    BuildF (..),
    BuildQ (..),
    MultiSub (..),
    MultiTag (..),
    MultiWalk
  )
where

import Control.Monad ((>=>))
import Control.MultiWalk.Contains
import Control.MultiWalk.HasSub
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.Kind (Type)

class
  ( BuildF (MultiWalk' tag) (MultiTypes tag),
    BuildQ (MultiWalk' tag) (MultiTypes tag)
  ) =>
  MultiTag tag
  where
  type MultiTypes tag :: [Type]
  type SubTag tag :: Type

class MultiSub stag t where
  type SubTypes stag t :: [SubSpec]
  type HasSubTag stag t :: Type
  type HasSubTag stag t = GSubTag

type MultiWalk tag t =
  ( All (TContains (MultiTypes tag)) (SubTypes (SubTag tag) t),
    QContains (MultiTypes tag) t,
    FContains (MultiTypes tag) t,
    HasSub (HasSubTag (SubTag tag) t) (SubTypes (SubTag tag) t) t
  )

class (MultiWalk tag t) => MultiWalk' tag t

instance (MultiWalk tag t) => MultiWalk' tag t

querySub :: forall tag t m. (Monoid m, MultiWalk tag t) => QList m (MultiTypes tag) -> t -> m
querySub = getSubWithQList @(HasSubTag (SubTag tag) t) @(SubTypes (SubTag tag) t)

walkSub :: forall tag t m. (Applicative m, MultiWalk tag t) => FList m (MultiTypes tag) -> t -> m t
walkSub = modSubWithFList @(HasSubTag (SubTag tag) t) @(SubTypes (SubTag tag) t)

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

walk ::
  forall tag t c.
  (MultiTag tag, MultiWalk tag c, MultiWalk tag t) =>
  (t -> t) ->
  c ->
  c
walk f = runIdentity . walkM @tag (Identity . f)

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
    qlist = f go $ buildQ @(MultiWalk' tag) go
    go :: forall s. MultiWalk tag s => s -> m
    go = querySub @tag qlist

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
    flist = f go $ buildF @(MultiWalk' tag) go
    go :: forall s. MultiWalk tag s => s -> m s
    go = walkSub @tag flist

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
