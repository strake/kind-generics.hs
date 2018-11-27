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
module Generics.Kind.Derive.FunctorOne where

import Data.Proxy
import Generics.Kind

type LoT1 a = a ':&&: LoT0

fmapDefaultOne :: (GenericK f (LoT1 a),
                   GenericK f (LoT1 b),
                   GFunctorOne (RepK f) a b)
                => (a -> b) -> f a -> f b
fmapDefaultOne f = toK . gfmapo f . fromK

class GFunctorOne (f :: LoT (* -> *) -> *) a b where
  gfmapo :: (a -> b) -> f (LoT1 a) -> f (LoT1 b)

gfmapo' :: forall a b f. (GFunctorOne f a b)
        => (a -> b) -> f (LoT1 a) -> f (LoT1 b)
gfmapo' = gfmapo

instance GFunctorOne U1 a b where
  gfmapo _ U1 = U1

instance GFunctorOne f a b => GFunctorOne (M1 i c f) a b where
  gfmapo v (M1 x) = M1 (gfmapo v x)

instance (GFunctorOne f a b, GFunctorOne g a b)
         => GFunctorOne (f :+: g) a b where
  gfmapo v (L1 x) = L1 (gfmapo v x)
  gfmapo v (R1 x) = R1 (gfmapo v x)

instance (GFunctorOne f a b, GFunctorOne g a b)
         => GFunctorOne (f :*: g) a b where
  gfmapo v (x :*: y) = gfmapo v x :*: gfmapo v y

instance (Ty c (LoT1 a) => GFunctorOne f a b, {- Ty c as => -} Ty c (LoT1 b))
         => GFunctorOne (c :=>: f) a b where
  gfmapo v (C x) = C (gfmapo v x)

class GFunctorOneArg (t :: Atom (* -> *) (*)) a b where
  gfmapof :: Proxy t -> (a -> b) -> Ty t (LoT1 a) -> Ty t (LoT1 b)

instance forall t a b. GFunctorOneArg t a b
         => GFunctorOne (F t) a b where
  gfmapo v (F x) = F (gfmapof (Proxy @t) v x)

-- A constant
instance GFunctorOneArg ('Kon t) a b where
  gfmapof _ _ x = x
-- The type variable itself
instance GFunctorOneArg V0 a b where
  gfmapof _ f x = f x
-- Going through functor
instance forall f x a b.
         (Functor f, GFunctorOneArg x a b)
         => GFunctorOneArg (f :$: x) a b where
  gfmapof _ f x = fmap (gfmapof (Proxy @x) f) x