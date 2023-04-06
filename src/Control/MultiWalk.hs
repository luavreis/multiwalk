{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{- |
  Here is a full (albeit simple) example of a MultiWalk definition, for Pandoc:

  > data PTag
  >
  > instance MultiTag PTag where
  >   type
  >     MultiTypes PTag =
  >       '[ Block,
  >          Inline
  >        ]
  >
  > type DoubleList a = MatchWith [[a]] (Trav (Compose [] []) a)
  >
  > instance MultiSub PTag Block where
  >   type
  >     SubTypes PTag Block =
  >       '[ ToSpec (Trav [] Inline),
  >          ToSpec (DoubleList Inline),
  >          ToSpec (Trav [] Block),
  >          ToSpec (DoubleList Block),
  >          ToSpec
  >            ( Under
  >                [([Inline], [[Block]])]
  >                'NoSel
  >                (Under ([Inline], [[Block]]) 'NoSel (Trav [] Inline))
  >            ),
  >          ToSpec
  >            ( Under
  >                [([Inline], [[Block]])]
  >                'NoSel
  >                (Under ([Inline], [[Block]]) 'NoSel (DoubleList Block))
  >            )
  >        ]
  >
  > instance MultiSub PTag Inline where
  >   type
  >     SubTypes PTag Inline =
  >       '[ToSpec (Trav [] Inline), ToSpec (Trav [] Block)]
-}
module Control.MultiWalk (
  MultiTag (..),
  MultiSub (..),
  query,
  walk,
  walkM,
  Walk,
  Query,
  walkSub,
  querySub,
  buildMultiW,
  buildMultiQ,
  (.>),
  (?>),
  ToSpec,
  ToSpecSel,
  SelSpec (..),
  Trav,
  MatchWith,
  Under,
  MultiWalk,
  FList (..),
  QList (..),
  BuildF (..),
  BuildQ (..),
)
where

import Control.Monad ((>=>))
import Control.MultiWalk.Contains
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.Kind (Type)

{- | You should instantiate 'MultiTag' to a tag associated to the structure you
   are working with. The tag is mostly there to prevent orphan instances, since
   people are often working with structures from other packages (Pandoc AST,
   HTML, etc.)
-}
class
  ( BuildF (MultiWalk' tag) (MultiTypes tag)
  , BuildQ (MultiWalk' tag) (MultiTypes tag)
  ) =>
  MultiTag tag
  where
  -- | The types that will be used in the walks and queries; every type listed here
  --    should have a 'MultiSub' instance. (The compiler will complain about this.)
  type MultiTypes tag :: [Type]

class MultiSub tag t where
  -- | A list of substructure specifications for types that are substructures to
  -- this type; all types listed here should also be listed in the corresponding
  -- 'MultiTypes', but you can omit types from there that should not be regarded
  -- as subtypes.
  --
  -- Substructure specifications are special datakinds that you can generate
  -- using 'ToSpec' and 'ToSpecSel', and the combinators (eg. 'Under',
  -- 'MatchWith' and 'Trav').
  type SubTypes tag t :: [SubSpec]

  -- | If you want to write HasSub instances by hand (not that easy), you can
  -- put the associated HasSub tag here. Defaults to 'GSubTag' (which derives
  -- 'Generic' instances).
  type HasSubTag tag t :: Type

  type HasSubTag tag t = GSubTag

type MultiWalk tag t =
  ( AllMods (TContains (MultiTypes tag)) (SubTypes tag t)
  , QContains (MultiTypes tag) t
  , FContains (MultiTypes tag) t
  , HasSub (HasSubTag tag t) (SubTypes tag t) t
  )

class (MultiWalk tag t) => MultiWalk' tag t

instance (MultiWalk tag t) => MultiWalk' tag t

-- | Query (only) substructures by applying functions from 'QList'.
querySub :: forall tag t m. (Monoid m, MultiWalk tag t) => QList m (MultiTypes tag) -> t -> m
querySub = getSubWithQList @(HasSubTag tag t) @(SubTypes tag t)

-- | Modify (only) substructures by applying functions from 'FList'.
walkSub :: forall tag t m. (Applicative m, MultiWalk tag t) => FList m (MultiTypes tag) -> t -> m t
walkSub = modSubWithFList @(HasSubTag tag t) @(SubTypes tag t)

-- | Query a structure with a single query function (just like Pandoc.Walk).
query ::
  forall tag m t a.
  ( MultiTag tag
  , MultiWalk tag a
  , MultiWalk tag t
  , Monoid m
  ) =>
  (t -> m) ->
  a ->
  m
query f =
  buildMultiQ @tag $ \go l ->
    l ?> \x -> f x <> go x

-- | Modify a structure by walking with a single function (just like Pandoc.Walk).
walk ::
  forall tag t c.
  (MultiTag tag, MultiWalk tag c, MultiWalk tag t) =>
  (t -> t) ->
  c ->
  c
walk f = runIdentity . walkM @tag (Identity . f)

-- | Modify a structure by walking with a single function (just like Pandoc.Walk).
walkM ::
  forall tag a m t.
  ( Monad m
  , MultiTag tag
  , MultiWalk tag a
  , MultiWalk tag t
  ) =>
  (t -> m t) ->
  a ->
  m a
walkM f =
  buildMultiW @tag $ \go l ->
    l .> (f >=> go)

type Query tag m = forall t. MultiWalk tag t => t -> m

{- | Most general way to create a query. Create a query with multiple functions,
   targeting multiple types.

   First argument is a function that takes a query, an empty list of queries and
   should return a list of queries populated with the multiple query functions.

   By "tying a knot", the first argument you are supplied with is almost the
   result of 'buildMultiQ' itself, the only difference being that it only
   queries /substructures/ of the type. It's a responsability of each function
   in the 'QList' to apply this function to its argument in any desired way, as
   to continue recursing down the "type tree".

   You can add functions to the empty 'QList' via '?>'.

   > multi :: Block -> [Text]
   > multi = buildMultiQ @PTag $ \sub list ->
   >     list ?> blks sub
   >          ?> inls sub
   >   where
   >     blks _ (CodeBlock _ c) = [c]
   >     blks f x = f x
   >     inls _ (Code _ c) = [c]
   >     inls f x = f x
-}
buildMultiQ ::
  forall tag m.
  (MultiTag tag, Monoid m) =>
  ( Query tag m ->
    QList m (MultiTypes tag) ->
    -- \^ Empty query that you should modify.
    QList m (MultiTypes tag)
  ) ->
  Query tag m
buildMultiQ f = qGet qlist
  where
    qlist :: QList m (MultiTypes tag)
    qlist = f go $ buildQ @(MultiWalk' tag) go
    go :: forall s. MultiWalk tag s => s -> m
    go = querySub @tag qlist

type Walk tag m = forall t. MultiWalk tag t => t -> m t

{- | Most general way to create a walk. Create a walk with multiple functions,
   targeting multiple types.

   First argument is a function that takes a walk, an empty list of functions and
   should return a list of functions populated with the multiple walk functions.

   By "tying a knot", the first argument you are supplied with is almost the
   result of 'buildMultiW' itself, the only difference being that it only walks
   /substructures/ of the type. It's a responsability of each function in the
   'FList' to apply this function to its argument in any desired way, as to
   continue recursing down the "type tree".

   You can add functions to the empty 'FList' via '.>'.

   > multi :: Applicative m => Block -> m Block
   > multi = buildMultiW @PTag $ \sub list ->
   >     list .> blks sub
   >          .> inls sub
   >   where
   >     blks _ (CodeBlock _ c) = Para [Str c]
   >     blks f x = f x
   >     inls _ (Code _ c) = Str c
   >     inls f x = f x
-}
buildMultiW ::
  forall tag m.
  (MultiTag tag, Applicative m) =>
  ( Walk tag m ->
    FList m (MultiTypes tag) ->
    FList m (MultiTypes tag)
  ) ->
  Walk tag m
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

-- | Add a function to a 'QList'.
(?>) :: QContains ls t => QList m ls -> (t -> m) -> QList m ls
(?>) = qSet

-- | Add a function to a 'FList'.
(.>) :: FContains ls t => FList m ls -> (t -> m t) -> FList m ls
(.>) = fSet
