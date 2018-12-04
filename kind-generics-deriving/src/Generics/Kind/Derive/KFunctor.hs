{-# language DataKinds              #-}
{-# language PolyKinds              #-}
{-# language GADTs                  #-}
{-# language RankNTypes             #-}
{-# language TypeOperators          #-}
{-# language MultiParamTypeClasses  #-}
{-# language FlexibleInstances      #-}
{-# language FlexibleContexts       #-}
{-# language QuantifiedConstraints  #-}
{-# language UndecidableInstances   #-}
{-# language ScopedTypeVariables    #-}
{-# language FunctionalDependencies #-}
{-# language TypeApplications       #-}
{-# language DefaultSignatures      #-}
{-# language AllowAmbiguousTypes    #-}
{-# language TypeFamilies           #-}
module Generics.Kind.Derive.KFunctor where

import Data.PolyKinded.Functor
import Data.Proxy

import Generics.Kind

kfmapDefault :: forall (f :: k) v as bs. (GenericK f as, GenericK f bs, GFunctor (RepK f) v as bs)
             => Mappings v as bs -> f :@@: as -> f :@@: bs
kfmapDefault v = toK @k @f @bs . gfmap v . fromK @k @f @as

fmapDefault :: forall (f :: * -> *) a b.
               (GenericK f (a ':&&: 'LoT0), GenericK f (b ':&&: 'LoT0),
                GFunctor (RepK f) '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0))
             => (a -> b) -> f a -> f b
fmapDefault f = kfmapDefault (f :^: M0 :: Mappings '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0))

class GFunctor (f :: LoT k -> *) (v :: Variances) (as :: LoT k) (bs :: LoT k) where
  gfmap :: Mappings v as bs -> f as -> f bs

instance GFunctor U1 v as bs where
  gfmap _ U1 = U1

instance GFunctor f v as bs => GFunctor (M1 i c f) v as bs where
  gfmap v (M1 x) = M1 (gfmap v x)

instance (GFunctor f v as bs, GFunctor g v as bs)
         => GFunctor (f :+: g) v as bs where
  gfmap v (L1 x) = L1 (gfmap v x)
  gfmap v (R1 x) = R1 (gfmap v x)

instance (GFunctor f v as bs, GFunctor g v as bs)
         => GFunctor (f :*: g) v as bs where
  gfmap v (x :*: y) = gfmap v x :*: gfmap v y

instance (Interpret c as => GFunctor f v as bs, {- Ty c as => -} Interpret c bs)
         => GFunctor (c :=>: f) v as bs where
  gfmap v (SuchThat x) = SuchThat (gfmap v x)

instance forall f v as bs.
         (forall (t :: *). GFunctor f ('Co ': v) (t ':&&: as) (t ':&&: bs))
         => GFunctor (Exists (*) f) v as bs where
  gfmap v (Exists (x :: f (t ':&&: x)))
    = Exists (gfmap ((id :^: v) :: Mappings ('Co ': v) (t ':&&: as) (t ':&&: bs)) x)

class GFunctorArg (t :: Atom d (*))
                  (v :: Variances) (intended :: Variance)
                  (as :: LoT d) (bs :: LoT d) where
  gfmapf :: Proxy t -> Proxy intended
         -> Mappings v as bs
         -> Mapping intended (Interpret t as) (Interpret t bs)

instance forall t v as bs. GFunctorArg t v 'Co as bs
         => GFunctor (Field t) v as bs where
  gfmap v (Field x) = Field (gfmapf (Proxy @t) (Proxy @'Co) v x)

instance GFunctorArg ('Kon t) v 'Co as bs where
  gfmapf _ _ _ = id
instance GFunctorArg ('Kon t) v 'Contra as bs where
  gfmapf _ _ _ = id

instance GFunctorArg ('Var 'VZ) (r ': v) r (a ':&&: as) (b ':&&: bs) where
  gfmapf _ _ (f :^: _) = f

instance forall vr pre v intended a as b bs.
         GFunctorArg ('Var vr) v intended as bs
         => GFunctorArg ('Var ('VS vr)) (pre ': v) intended (a ':&&: as) (b ':&&: bs) where
  gfmapf _ _ (_ :^: rest) = gfmapf (Proxy @('Var vr)) (Proxy @intended) rest

instance forall f x v v1 as bs.
         (KFunctor f '[v1] (Interpret x as ':&&: 'LoT0) (Interpret x bs ':&&: 'LoT0),
          GFunctorArg x v v1 as bs)
         => GFunctorArg (f :$: x) v 'Co as bs where
  gfmapf _ _ v = kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^: M0)

instance forall f x y v v1 v2 as bs.
         (KFunctor f '[v1, v2] (Interpret x as ':&&: Interpret y as ':&&: 'LoT0)
                               (Interpret x bs ':&&: Interpret y bs ':&&: 'LoT0),
          GFunctorArg x v v1 as bs, GFunctorArg y v v2 as bs)
         => GFunctorArg (f :$: x ':@: y) v 'Co as bs where
  gfmapf _ _ v = kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^:
                        gfmapf (Proxy @y) (Proxy @v2) v :^: M0)

instance forall f x y z v v1 v2 v3 as bs.
         (KFunctor f '[v1, v2, v3] (Interpret x as ':&&: Interpret y as ':&&: Interpret z as ':&&: 'LoT0)
                                   (Interpret x bs ':&&: Interpret y bs ':&&: Interpret z bs ':&&: 'LoT0),
          GFunctorArg x v v1 as bs, GFunctorArg y v v2 as bs, GFunctorArg z v v3 as bs)
         => GFunctorArg (f :$: x ':@: y ':@: z) v 'Co as bs where
  gfmapf _ _ v = kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^:
                        gfmapf (Proxy @y) (Proxy @v2) v :^:
                        gfmapf (Proxy @z) (Proxy @v3) v :^: M0)