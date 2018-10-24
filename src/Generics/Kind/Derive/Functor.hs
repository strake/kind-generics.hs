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

data Mappings (v :: Variances) (x :: LoT k) (y :: LoT k) where
  Map0 :: Mappings '[] LoT0 LoT0
  MapC :: Mapping v a b -> Mappings vs as bs
       -> Mappings (v ': vs) (a :&&: as) (b :&&: bs)

class KFunctor (f :: k) (v :: Variances) | f -> v where
  kfmap :: Mappings v as bs -> f :@@: as -> f :@@: bs

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
  gfmap v (E x) = E (gfmap (MapC FixedM v) x)

class GFunctorField (t :: Atom d (*)) (v :: Variances) (as :: LoT d) (bs :: LoT d) where
  gfmapf :: Proxy t -> Mappings v as bs -> Ty t as -> Ty t bs

class GFunctorHead (f :: Atom d k)
                   (vin :: Variances) (vout :: Variances) 
                   (as :: LoT d) (bs :: LoT d)
                   (rs :: LoT k) (ts :: LoT k) where
  gfmaph :: Proxy f
         -> Mappings vin as bs -> Mappings vout rs ts
         -> Ty f as :@@: rs -> Ty f bs :@@: ts

instance forall t v as bs. GFunctorField t v as bs
         => GFunctor (F t) v as bs where
  gfmap v (F x) = F (gfmapf (Proxy :: Proxy t) v x)

instance GFunctorField (Kon t) v as bs where
  gfmapf _ _ x = x

instance GFunctorField (Var VZ) (Co ': v) (a :&&: as) (b :&&: bs) where
  gfmapf _ (MapC (CoM f) _) x = f x

instance forall vr pre v a as b bs.
         GFunctorField (Var vr) v as bs
         => GFunctorField (Var (VS vr)) (pre ': v) (a :&&: as) (b :&&: bs) where
  gfmapf _ (MapC _ rest) x = gfmapf (Proxy :: Proxy (Var vr)) rest x

instance forall f x v as bs.
         ( GFunctorHead f v '[Co] as bs (Ty x as :&&: LoT0) (Ty x bs :&&: LoT0)
         , GFunctorField x v as bs )
         => GFunctorField (f :@: x) v as bs where
  gfmapf _ v x = unA0 $ unArg
               $ gfmaph (Proxy :: Proxy f) v (MapC (CoM (gfmapf (Proxy :: Proxy x) v)) Map0)
               $ Arg $ A0 x

instance forall f x v acc as bs rs ts.
         ( GFunctorHead f v (Co ': acc) as bs (Ty x as :&&: rs) (Ty x bs :&&: ts)
         , GFunctorField x v as bs )
         => GFunctorHead (f :@: x) v acc as bs rs ts where
  gfmaph _ v acc x = unArg
                   $ gfmaph (Proxy :: Proxy f) v (MapC (CoM (gfmapf (Proxy :: Proxy x) v)) acc)
                   $ Arg $ x

instance KFunctor f acc => GFunctorHead (Kon f) v acc as bs ts rs where
  gfmaph _ _ acc x = kfmap acc x

instance KFunctor (Ty (Var vr) os) acc => GFunctorHead (Var vr) v acc os os ts rs where
  gfmaph _ _ acc x = kfmap acc x