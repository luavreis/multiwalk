{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Control.MultiWalk.HasSub (
  HasSub (..),
  Spec (..),
  SubSpec (..),
  SelSpec (..),
  Carrier,
  ToSpec,
  ToSpecSel,
  All,
  AllMods,
  GSubTag,
) where

import Control.Applicative (liftA2)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import GHC.Generics
import GHC.TypeLits

data Spec
  = SpecList [SubSpec]
  | SpecLeaf
  | -- | Modifiers (used for customizing constraints)
    SpecSelf
      Type

data SubSpec
  = SubSpec
      SelSpec
      -- ^ Constructor and field selectors
      Type
      -- ^ Modifiers (used for customizing constraints)
      Type
      -- ^ Carrier type, should be equal to Carrier of type above (to be aligned
      -- with the target's generic subtypes)

type family Carrier ctag a :: Type

data SelSpec
  = NoSel
  | ConsSel Symbol
  | FieldSel Symbol
  | ConsFieldSel Symbol Symbol

type ToSpec tag (a :: Type) = 'SubSpec 'NoSel a (Carrier tag a)
type ToSpecSel tag (s :: SelSpec) (a :: Type) = 'SubSpec s a (Carrier tag a)

class HasSub ctag tag (ls :: Spec) t where
  modSub ::
    forall c m.
    (Applicative m, AllMods c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> Carrier ctag s -> m (Carrier ctag s)) ->
    t ->
    m t
  getSub ::
    forall c m.
    (Monoid m, AllMods c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> Carrier ctag s -> m) ->
    t ->
    m

instance (Carrier tag s ~ t) => HasSub tag ctag ('SpecSelf s) t where
  modSub _ f = f (Proxy @s)
  getSub _ f = f (Proxy @s)

instance HasSub tag ctag 'SpecLeaf t where
  modSub _ _ = pure
  getSub _ _ = mempty

data GSubTag

instance (Generic t, HasSub' ctag (l : ls) 'Nothing 'Nothing (Rep t)) => HasSub ctag GSubTag ('SpecList (l : ls)) t where
  modSub p f = fmap to . modSub' @ctag @(l : ls) @'Nothing @'Nothing p f . from
  getSub p f = getSub' @ctag @(l : ls) @'Nothing @'Nothing p f . from

-- Generic code

type family All (p :: k -> Constraint) (as :: [k]) :: Constraint where
  All p '[] = ()
  All p (a ': as) = (p a, All p as)

type family SpecMods (s :: SubSpec) :: Type where
  SpecMods ('SubSpec _ t _) = t

type family AllMods (p :: Type -> Constraint) (as :: Spec) :: Constraint where
  AllMods p ('SpecList ls) = AllMods' p ls
  AllMods p ('SpecSelf t) = p t
  AllMods p 'SpecLeaf = ()

type family AllMods' (p :: Type -> Constraint) (as :: [SubSpec]) :: Constraint where
  AllMods' p '[] = ()
  AllMods' p (a ': as) = (p (SpecMods a), AllMods' p as)

class HasSub' ctag (ls :: [SubSpec]) (cname :: Maybe Symbol) (sname :: Maybe Symbol) (t :: Type -> Type) where
  modSub' ::
    forall c m p.
    (Applicative m, AllMods' c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> Carrier ctag s -> m (Carrier ctag s)) ->
    t p ->
    m (t p)
  getSub' ::
    forall c m p.
    (Monoid m, AllMods' c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> Carrier ctag s -> m) ->
    t p ->
    m

instance
  Carrier ctag t1 ~ t2 =>
  HasSub' ctag ('SubSpec 'NoSel t1 t2 : ls) _a _b (K1 _c t2)
  where
  modSub' _ f (K1 x) = K1 <$> f (Proxy @t1) x
  getSub' _ f (K1 x) = f (Proxy @t1) x

instance
  Carrier ctag t1 ~ t2 =>
  HasSub' ctag ('SubSpec ('FieldSel s) t1 t2 : ls) _a ('Just s) (K1 _c t2)
  where
  modSub' _ f (K1 x) = K1 <$> f (Proxy @t1) x
  getSub' _ f (K1 x) = f (Proxy @t1) x

instance
  Carrier ctag t1 ~ t2 =>
  HasSub' ctag ('SubSpec ('ConsSel s) t1 t2 : ls) ('Just s) _b (K1 _c t2)
  where
  modSub' _ f (K1 x) = K1 <$> f (Proxy @t1) x
  getSub' _ f (K1 x) = f (Proxy @t1) x

instance
  Carrier ctag t1 ~ t2 =>
  HasSub' ctag ('SubSpec ('ConsFieldSel s1 s2) t1 t2 : ls) ('Just s1) ('Just s2) (K1 _c t2)
  where
  modSub' _ f (K1 x) = K1 <$> f (Proxy @t1) x
  getSub' _ f (K1 x) = f (Proxy @t1) x

instance {-# OVERLAPPABLE #-} HasSub' ctag ls a b (K1 j s) => HasSub' ctag (l : ls) a b (K1 j s) where
  modSub' = modSub' @ctag @ls @a @b
  getSub' = getSub' @ctag @ls @a @b

instance HasSub' ctag '[] _a _b (K1 _c _d) where
  modSub' _ _ = pure
  getSub' _ _ = mempty

instance
  ( HasSub' ctag s a 'Nothing x
  , HasSub' ctag s a 'Nothing y
  ) =>
  HasSub' ctag s a 'Nothing (x :*: y)
  where
  modSub' p f (x :*: y) = liftA2 (:*:) (modSub' @ctag @s @a @'Nothing p f x) (modSub' @ctag @s @a @'Nothing p f y)
  getSub' p f (x :*: y) = getSub' @ctag @s @a @'Nothing p f x <> getSub' @ctag @s @a @'Nothing p f y

instance HasSub' ctag _a _b _c U1 where
  modSub' _ _ = pure
  getSub' _ _ = mempty

instance
  ( HasSub' ctag s 'Nothing 'Nothing x
  , HasSub' ctag s 'Nothing 'Nothing y
  ) =>
  HasSub' ctag s 'Nothing 'Nothing (x :+: y)
  where
  modSub' p f (L1 x) = L1 <$> modSub' @ctag @s @'Nothing @'Nothing p f x
  modSub' p f (R1 x) = R1 <$> modSub' @ctag @s @'Nothing @'Nothing p f x
  getSub' p f (L1 x) = getSub' @ctag @s @'Nothing @'Nothing p f x
  getSub' p f (R1 x) = getSub' @ctag @s @'Nothing @'Nothing p f x

instance
  HasSub' ctag ls a s x =>
  HasSub' ctag ls a 'Nothing (S1 ('MetaSel s _a _b _c) x)
  where
  modSub' p f (M1 x) = M1 <$> modSub' @ctag @ls @a @s p f x
  getSub' p f (M1 x) = getSub' @ctag @ls @a @s p f x

instance
  HasSub' ctag ls ('Just s) 'Nothing x =>
  HasSub' ctag ls 'Nothing 'Nothing (C1 ('MetaCons s _a _b) x)
  where
  modSub' p f (M1 x) = M1 <$> modSub' @ctag @ls @('Just s) @'Nothing p f x
  getSub' p f (M1 x) = getSub' @ctag @ls @('Just s) @'Nothing p f x

instance
  HasSub' ctag ls 'Nothing 'Nothing x =>
  HasSub' ctag ls 'Nothing 'Nothing (D1 _a x)
  where
  modSub' p f (M1 x) = M1 <$> modSub' @ctag @ls @'Nothing @'Nothing p f x
  getSub' p f (M1 x) = getSub' @ctag @ls @'Nothing @'Nothing p f x
