{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Control.MultiWalk.HasSub where

import Control.Applicative (liftA2)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import GHC.Generics
import GHC.TypeLits

data SubSpec = SubSpec SelSpec Type Type

data SelSpec
  = NoSel
  | ConsSel Symbol
  | FieldSel Symbol
  | ConsFieldSel Symbol Symbol

type family SpecCarrier (t :: SubSpec) where
  SpecCarrier ('SubSpec _ a _) = a

class HasSub tag (ls :: [SubSpec]) t where
  modSub ::
    forall c m.
    (Applicative m, All c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> SpecCarrier s -> m (SpecCarrier s)) ->
    t ->
    m t
  getSub ::
    forall c m.
    (Monoid m, All c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> SpecCarrier s -> m) ->
    t ->
    m

instance HasSub tag '[] t where
  modSub _ _ = pure
  getSub _ _ = mempty

data GSubTag

instance (Generic t, HasSub' (l : ls) 'Nothing 'Nothing (Rep t)) => HasSub GSubTag (l : ls) t where
  modSub p f = fmap to . modSub' @(l : ls) @'Nothing @'Nothing p f . from
  getSub p f = getSub' @(l : ls) @'Nothing @'Nothing p f . from

-- Generic code

type family All (p :: k -> Constraint) (as :: [k]) :: Constraint where
  All p '[] = ()
  All p (a ': as) = (p a, All p as)

class HasSub' (ls :: [SubSpec]) (cname :: Maybe Symbol) (sname :: Maybe Symbol) (t :: Type -> Type) where
  modSub' ::
    forall c m p.
    (Applicative m, All c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> SpecCarrier s -> m (SpecCarrier s)) ->
    t p ->
    m (t p)
  getSub' ::
    forall c m p.
    (Monoid m, All c ls) =>
    Proxy c ->
    (forall s. c s => Proxy s -> SpecCarrier s -> m) ->
    t p ->
    m

instance HasSub' ('SubSpec 'NoSel t tt : ls) _a _b (K1 _c t) where
  modSub' _ f (K1 x) = K1 <$> f (Proxy @('SubSpec 'NoSel t tt)) x
  getSub' _ f (K1 x) = f (Proxy @('SubSpec 'NoSel t tt)) x

instance HasSub' ('SubSpec ('FieldSel s) t tt : ls) _a ('Just s) (K1 _c t) where
  modSub' _ f (K1 x) = K1 <$> f (Proxy @('SubSpec ('FieldSel s) t tt)) x
  getSub' _ f (K1 x) = f (Proxy @('SubSpec ('FieldSel s) t tt)) x

instance HasSub' ('SubSpec ('ConsSel s) t tt : ls) ('Just s) _b (K1 _c t) where
  modSub' _ f (K1 x) = K1 <$> f (Proxy @('SubSpec ('ConsSel s) t tt)) x
  getSub' _ f (K1 x) = f (Proxy @('SubSpec ('ConsSel s) t tt)) x

instance HasSub' ('SubSpec ('ConsFieldSel s1 s2) t tt : ls) ('Just s1) ('Just s2) (K1 _c t) where
  modSub' _ f (K1 x) = K1 <$> f (Proxy @('SubSpec ('ConsFieldSel s1 s2) t tt)) x
  getSub' _ f (K1 x) = f (Proxy @('SubSpec ('ConsFieldSel s1 s2) t tt)) x

instance {-# OVERLAPPABLE #-} HasSub' ls a b (K1 j s) => HasSub' (l : ls) a b (K1 j s) where
  modSub' = modSub' @ls @a @b
  getSub' = getSub' @ls @a @b

instance HasSub' '[] _a _b (K1 _c _d) where
  modSub' _ _ = pure
  getSub' _ _ = mempty

instance
  ( HasSub' s a 'Nothing x
  , HasSub' s a 'Nothing y
  ) =>
  HasSub' s a 'Nothing (x :*: y)
  where
  modSub' p f (x :*: y) = liftA2 (:*:) (modSub' @s @a @'Nothing p f x) (modSub' @s @a @'Nothing p f y)
  getSub' p f (x :*: y) = getSub' @s @a @'Nothing p f x <> getSub' @s @a @'Nothing p f y

instance HasSub' _a _b _c U1 where
  modSub' _ _ = pure
  getSub' _ _ = mempty

instance
  ( HasSub' s 'Nothing 'Nothing x
  , HasSub' s 'Nothing 'Nothing y
  ) =>
  HasSub' s 'Nothing 'Nothing (x :+: y)
  where
  modSub' p f (L1 x) = L1 <$> modSub' @s @'Nothing @'Nothing p f x
  modSub' p f (R1 x) = R1 <$> modSub' @s @'Nothing @'Nothing p f x
  getSub' p f (L1 x) = getSub' @s @'Nothing @'Nothing p f x
  getSub' p f (R1 x) = getSub' @s @'Nothing @'Nothing p f x

instance
  HasSub' ls a ('Just s) x =>
  HasSub' ls a 'Nothing (S1 ('MetaSel ('Just s) _a _b _c) x)
  where
  modSub' p f (M1 x) = M1 <$> modSub' @ls @a @('Just s) p f x
  getSub' p f (M1 x) = getSub' @ls @a @('Just s) p f x

instance
  HasSub' ls ('Just s) 'Nothing x =>
  HasSub' ls 'Nothing 'Nothing (C1 ('MetaCons s _a _b) x)
  where
  modSub' p f (M1 x) = M1 <$> modSub' @ls @('Just s) @'Nothing p f x
  getSub' p f (M1 x) = getSub' @ls @('Just s) @'Nothing p f x

instance
  HasSub' ls 'Nothing 'Nothing x =>
  HasSub' ls 'Nothing 'Nothing (D1 _a x)
  where
  modSub' p f (M1 x) = M1 <$> modSub' @ls @'Nothing @'Nothing p f x
  getSub' p f (M1 x) = getSub' @ls @'Nothing @'Nothing p f x
