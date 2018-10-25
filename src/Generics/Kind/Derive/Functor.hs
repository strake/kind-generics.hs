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
module Generics.Kind.Derive.Functor where

import Data.Proxy

import Generics.Kind

data Variance = Co | Contra | Fixed | Phantom
type Variances = [Variance]

data Mapping (v :: Variance) (a :: k) (b :: k) where
  CoM      :: (a -> b) -> Mapping Co      a b
  ContraM  :: (b -> a) -> Mapping Contra  a b
  FixedM   ::             Mapping Fixed   t t
  PhantomM ::             Mapping Phantom a b

infixr 5 :^:
data Mappings (v :: Variances) (x :: LoT k) (y :: LoT k) where
  M0    :: Mappings '[] LoT0 LoT0
  (:^:) :: Mapping v a b -> Mappings vs as bs
        -> Mappings (v ': vs) (a :&&: as) (b :&&: bs)

class KFunctor (f :: k) (v :: Variances) (as :: LoT k) (bs :: LoT k) | f -> v where
  kfmap :: Mappings v as bs -> f :@@: as -> f :@@: bs

  default
    kfmap :: (GenericK f as, GenericK f bs, GFunctor (RepK f) v as bs)
          => Mappings v as bs -> f :@@: as -> f :@@: bs
  kfmap v = toK @_ @f @bs . gfmap v . fromK @_ @f @as

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

instance (Ty c as => GFunctor f v as bs, Ty c bs)
         => GFunctor (c :=>: f) v as bs where
  gfmap v (C x) = C (gfmap v x)

instance (forall t. GFunctor f (Fixed ': v) (t :&&: as) (t :&&: bs))
         => GFunctor (E f) v as bs where
  gfmap v (E x) = E (gfmap (FixedM :^: v) x)

class GFunctorArg (t :: Atom d (*))
                  (v :: Variances) (intended :: Variance)
                  (as :: LoT d) (bs :: LoT d) where
  gfmapf :: Proxy t -> Proxy intended
         -> Mappings v as bs
         -> Mapping intended (Ty t as) (Ty t bs)

instance forall t v as bs. GFunctorArg t v Co as bs
         => GFunctor (F t) v as bs where
  gfmap v (F x) = case gfmapf (Proxy @t) (Proxy @Co) v of
                    CoM f -> F (f x)

instance GFunctorArg (Kon t) v Co as bs where
  gfmapf _ _ _ = CoM id
instance GFunctorArg (Kon t) v Contra as bs where
  gfmapf _ _ _ = ContraM id
instance GFunctorArg (Kon t) v Fixed as bs where
  gfmapf _ _ _ = FixedM

instance GFunctorArg (Var VZ) (Co ': v) Co (a :&&: as) (b :&&: bs) where
  gfmapf _ _ (CoM f :^: _) = CoM f
instance GFunctorArg (Var VZ) (Contra ': v) Contra (a :&&: as) (b :&&: bs) where
  gfmapf _ _ (ContraM f :^: _) = ContraM f
instance GFunctorArg (Var VZ) (Fixed ': v) Fixed (a :&&: as) (b :&&: bs) where
  gfmapf _ _ (FixedM :^: _) = FixedM

instance forall vr pre v intended a as b bs.
         GFunctorArg (Var vr) v intended as bs
         => GFunctorArg (Var (VS vr)) (pre ': v) intended (a :&&: as) (b :&&: bs) where
  gfmapf _ _ (_ :^: rest) = gfmapf (Proxy @(Var vr)) (Proxy @intended) rest

instance forall f x v v1 as bs.
         (KFunctor f '[v1] (Ty x as :&&: LoT0) (Ty x bs :&&: LoT0),
          GFunctorArg x v v1 as bs)
         => GFunctorArg (f :$: x) v Co as bs where
  gfmapf _ _ v = CoM (kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^: M0))

instance forall f x y v v1 v2 as bs.
         (KFunctor f '[v1, v2] (Ty x as :&&: Ty y as :&&: LoT0) (Ty x bs :&&: Ty y bs :&&: LoT0),
          GFunctorArg x v v1 as bs, GFunctorArg y v v2 as bs)
         => GFunctorArg (f :$: x :@: y) v Co as bs where
  gfmapf _ _ v = CoM ( kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^:
                              gfmapf (Proxy @y) (Proxy @v2) v :^: M0) )

{-
instance forall f x y z v v1 v2 v3 as bs.
         (KFunctor f '[v1, v2, v3], 
          GFunctorArg x v v1 as bs, GFunctorArg y v v2 as bs, GFunctorArg z v v3 as bs)
         => GFunctorArg (f :$: x :@: y :@: z) v Co as bs where
  gfmapf _ _ v = CoM ( unA0 . unArg . unArg . unArg .
                       kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^:
                              gfmapf (Proxy @y) (Proxy @v2) v :^:
                              gfmapf (Proxy @z) (Proxy @v3) v :^: M0) . 
                       Arg . Arg . Arg . A0 )
-}