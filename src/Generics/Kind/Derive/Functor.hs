{-# language DataKinds             #-}
{-# language PolyKinds             #-}
{-# language GADTs                 #-}
{-# language RankNTypes            #-}
{-# language TypeOperators         #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language FlexibleContexts      #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances  #-}
module Generics.Kind.Derive.Functor where

import Generics.Kind

data Variance k where
  End     :: Variance (*)
  Co      :: Variance ks -> Variance (* -> ks)
  Contra  :: Variance ks -> Variance (* -> ks)
  Fixed   :: Variance ks -> Variance (k -> ks)
  Phantom :: Variance ks -> Variance (k -> ks)
  Higher  :: Variance k -> Variance ks -> Variance (k -> ks)

data Mappings (v :: Variance k) (x :: LoT k) (y :: LoT k) where
  EndM     :: Mappings End LoT0 LoT0
  CoM      :: (a -> b) -> Mappings vs as bs
           -> Mappings (Co      vs)  (a :&&: as) (b :&&: bs)
  ContraM  :: (b -> a) -> Mappings vs as bs
           -> Mappings (Contra  vs)  (a :&&: as) (b :&&: bs)
  FixedM   ::             Mappings vs as bs
           -> Mappings (Fixed   vs)  (t :&&: as) (t :&&: bs)
  PhantomM ::             Mappings vs as bs
           -> Mappings (Phantom vs)  (a :&&: as) (b :&&: bs)
  HigherM  :: (forall cs ds. Mappings v cs ds) -> Mappings vs as bs
           -> Mappings (Higher v vs) (a :&&: as) (b :&&: bs)

class GFunctor (f :: LoT k -> *) (v :: Variance k) (as :: LoT k) (bs :: LoT k) where
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

instance (forall t. GFunctor f (Fixed v) (t :&&: as) (t :&&: bs))
         => GFunctor (E f) v as bs where
  gfmap v (E x) = E (gfmap (FixedM v) x)