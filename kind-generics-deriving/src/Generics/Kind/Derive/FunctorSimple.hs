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
module Generics.Kind.Derive.FunctorSimple where

import Data.Proxy
import Generics.Kind

fmapDefaultS :: (GenericS r f xs, GenericS t f ys,
                 GFunctorSimple (RepK f) xs ys)
              => (Last xs -> Last ys) -> r -> t
fmapDefaultS f = toS . gfmaps f . fromS

type family Last (xs :: LoT k) :: * where
  Last (x ':&&: LoT0) = x
  Last (x ':&&: xs)   = Last xs

class GFunctorSimple (f :: LoT k -> *) (xs :: LoT k) (ys :: LoT k) where
  gfmaps :: (Last xs -> Last ys) -> f xs -> f ys

gfmaps' :: forall xs ys f. (GFunctorSimple f xs ys)
        => (Last xs -> Last ys) -> f xs -> f ys
gfmaps' = gfmaps

instance GFunctorSimple U1 xs ys where
  gfmaps _ U1 = U1

instance GFunctorSimple f xs ys
         => GFunctorSimple (M1 i c f) xs ys where
  gfmaps v (M1 x) = M1 (gfmaps v x)

instance (GFunctorSimple f xs ys, GFunctorSimple g xs ys)
         => GFunctorSimple (f :+: g) xs ys where
  gfmaps v (L1 x) = L1 (gfmaps v x)
  gfmaps v (R1 x) = R1 (gfmaps v x)

instance (GFunctorSimple f xs ys, GFunctorSimple g xs ys)
         => GFunctorSimple (f :*: g) xs ys where
  gfmaps v (x :*: y) = gfmaps v x :*: gfmaps v y

instance (Ty c xs => GFunctorSimple f xs ys, {- Ty c as => -} Ty c ys)
         => GFunctorSimple (c :=>: f) xs ys where
  gfmaps v (C x) = C (gfmaps v x)

instance (forall t. GFunctorSimple f (t ':&&: x ':&&: xs) (t ':&&: y ':&&: ys))
         => GFunctorSimple (E f) (x ':&&: xs) (y ':&&: ys) where
  gfmaps v (E (x :: f (t ':&&: p ':&&: ps))) = E (gfmaps' @(t ':&&: _) @(t ':&&: _) v x)


class GFunctorSimpleArg (t :: Atom d (*)) (xs :: LoT d) (ys :: LoT d) where
  gfmapsf :: Proxy t -> Proxy xs -> Proxy ys
          -> (Last xs -> Last ys)
          -> Ty t xs -> Ty t ys

instance forall t xs ys. GFunctorSimpleArg t xs ys
         => GFunctorSimple (F t) xs ys where
  gfmaps v (F x) = F (gfmapsf (Proxy @t) (Proxy @xs) (Proxy @ys) v x)

instance GFunctorSimpleArg ('Kon t) xs ys where
  gfmapsf _ _ _ _ x = x

instance GFunctorSimpleArg ('Var 'VZ) (a ':&&: LoT0) (b ':&&: LoT0) where
  gfmapsf _ _ _ f x = f x
instance GFunctorSimpleArg ('Var 'VZ) (t ':&&: a ':&&: as) (t ':&&: b :&&: bs) where
  gfmapsf _ _ _ _ x = x
instance forall v t a as b bs. GFunctorSimpleArg ('Var v) (a ':&&: as) (b ':&&: bs)
         => GFunctorSimpleArg ('Var ('VS v)) (t ':&&: a ':&&: as) (t ':&&: b ':&&: bs) where
  gfmapsf _ _ _ f x = gfmapsf (Proxy @('Var v)) (Proxy @(a ':&&: as)) (Proxy @(b ':&&: bs)) f x

-- Going through functor
instance forall f x xs ys.
         (Functor f, GFunctorSimpleArg x xs ys)
         => GFunctorSimpleArg (f :$: x) xs ys where
  gfmapsf _ pxs pys f x = fmap (gfmapsf (Proxy @x) pxs pys f) x

instance forall f y x xs ys.
         (Functor (f (Ty y xs)), Ty y xs ~ Ty y ys,
          GFunctorSimpleArg x xs ys)
         => GFunctorSimpleArg (f :$: y :@: x) xs ys where
  gfmapsf _ pxs pys f x = fmap (gfmapsf (Proxy @x) pxs pys f) x

instance forall f y1 y2 x xs ys.
         (Functor (f (Ty y1 xs) (Ty y2 xs)),
          Ty y1 xs ~ Ty y1 ys, Ty y2 xs ~ Ty y2 ys,
          GFunctorSimpleArg x xs ys)
         => GFunctorSimpleArg (f :$: y1 :@: y2 :@: x) xs ys where
  gfmapsf _ pxs pys f x = fmap (gfmapsf (Proxy @x) pxs pys f) x