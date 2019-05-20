{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language DataKinds             #-}
{-# language PolyKinds             #-}
{-# language KindSignatures        #-}
{-# language ScopedTypeVariables   #-}
{-# language QuantifiedConstraints #-}
{-# language TypeOperators         #-}
{-# language UndecidableInstances  #-}
{-# language TypeApplications      #-}
{-# language TypeFamilies          #-}
{-# language FlexibleContexts      #-}
{-# language AllowAmbiguousTypes   #-}
{-# language ConstraintKinds       #-}
module Generics.Kind.Derive.FunctorOne where

import Data.Proxy
import Data.Kind
import Generics.Kind

fmapDefaultOne :: (GenericK f,
                   GenericK f,
                   GFunctorOne (RepK f),
                   Reqs (RepK f) a b)
                => (a -> b) -> f a -> f b
fmapDefaultOne f = toK . gfmapo f . fromK

class GFunctorOne (f :: LoT (* -> *) -> *) where
  type Reqs f a b :: Constraint
  gfmapo :: Reqs f a b => (a -> b) -> f (LoT1 a) -> f (LoT1 b)

gfmapo' :: forall a b f. (GFunctorOne f, Reqs f a b)
        => (a -> b) -> f (LoT1 a) -> f (LoT1 b)
gfmapo' = gfmapo


instance GFunctorOne U1 where
  type Reqs U1 a b = ()
  gfmapo _ U1 = U1

instance GFunctorOne f => GFunctorOne (M1 i c f) where
  type Reqs (M1 i c f) a b = Reqs f a b
  gfmapo v (M1 x) = M1 (gfmapo v x)

instance (GFunctorOne f, GFunctorOne g)
         => GFunctorOne (f :+: g) where
  type Reqs (f :+: g) a b = (Reqs f a b, Reqs g a b)
  gfmapo v (L1 x) = L1 (gfmapo v x)
  gfmapo v (R1 x) = R1 (gfmapo v x)

instance (GFunctorOne f, GFunctorOne g)
         => GFunctorOne (f :*: g) where
  type Reqs (f :*: g) a b = (Reqs f a b, Reqs g a b)
  gfmapo v (x :*: y) = gfmapo v x :*: gfmapo v y

instance GFunctorOne f => GFunctorOne (c :=>: f) where
  type Reqs (c :=>: f) a b = (Interpret c (LoT1 b), Reqs f a b)
  -- actually you want     = Interpret c (LoT1 a) => (Interpret c (LoT1 b), Reqs f a b)
  gfmapo v (SuchThat x) = SuchThat (gfmapo v x)

class GFunctorOneArg (t :: Atom (* -> *) (*)) where
  gfmapof :: Proxy t -> (a -> b)
          -> Interpret t (LoT1 a) -> Interpret t (LoT1 b)

instance GFunctorOneArg t => GFunctorOne (Field t) where
  type Reqs (Field t) a b = (() :: Constraint)
  gfmapo v (Field x) = Field (gfmapof (Proxy @t) v x)

-- A constant
instance GFunctorOneArg ('Kon t) where
  gfmapof _ _ x = x
-- The type variable itself
instance GFunctorOneArg Var0 where
  gfmapof _ f x = f x
-- Going through functor
instance forall f x.
         (Functor f, GFunctorOneArg x)
         => GFunctorOneArg (f :$: x) where
  gfmapof _ f x = fmap (gfmapof (Proxy @x) f) x