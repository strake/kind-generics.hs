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
module Generics.Kind.Derive.FunctorLast where

import Data.Proxy
import Generics.Kind

fmapDefaultLast :: (GenericS r f xs, GenericS t f ys,
                    GFunctorLast (RepK f) xs ys)
                => (Last xs -> Last ys) -> r -> t
fmapDefaultLast f = toS . gfmapl f . fromS

type family Last (xs :: LoT k) :: * where
  Last (x ':&&: LoT0) = x
  Last (x ':&&: xs)   = Last xs

class GFunctorLast (f :: LoT k -> *) (xs :: LoT k) (ys :: LoT k) where
  gfmapl :: (Last xs -> Last ys) -> f xs -> f ys

gfmapl' :: forall xs ys f. (GFunctorLast f xs ys)
        => (Last xs -> Last ys) -> f xs -> f ys
gfmapl' = gfmapl

instance GFunctorLast U1 xs ys where
  gfmapl _ U1 = U1

instance GFunctorLast f xs ys
         => GFunctorLast (M1 i c f) xs ys where
  gfmapl v (M1 x) = M1 (gfmapl v x)

instance (GFunctorLast f xs ys, GFunctorLast g xs ys)
         => GFunctorLast (f :+: g) xs ys where
  gfmapl v (L1 x) = L1 (gfmapl v x)
  gfmapl v (R1 x) = R1 (gfmapl v x)

instance (GFunctorLast f xs ys, GFunctorLast g xs ys)
         => GFunctorLast (f :*: g) xs ys where
  gfmapl v (x :*: y) = gfmapl v x :*: gfmapl v y

instance (Ty c xs => GFunctorLast f xs ys, {- Ty c as => -} Ty c ys)
         => GFunctorLast (c :=>: f) xs ys where
  gfmapl v (C x) = C (gfmapl v x)

instance (forall t. GFunctorLast f (t ':&&: x ':&&: xs) (t ':&&: y ':&&: ys))
         => GFunctorLast (E f) (x ':&&: xs) (y ':&&: ys) where
  gfmapl v (E (x :: f (t ':&&: p ':&&: ps))) = E (gfmapl' @(t ':&&: _) @(t ':&&: _) v x)


class GFunctorLastArg (t :: Atom d (*)) (xs :: LoT d) (ys :: LoT d) where
  gfmaplf :: Proxy t -> Proxy xs -> Proxy ys
          -> (Last xs -> Last ys)
          -> Ty t xs -> Ty t ys

instance forall t xs ys. GFunctorLastArg t xs ys
         => GFunctorLast (F t) xs ys where
  gfmapl v (F x) = F (gfmaplf (Proxy @t) (Proxy @xs) (Proxy @ys) v x)

instance GFunctorLastArg ('Kon t) xs ys where
  gfmaplf _ _ _ _ x = x

instance GFunctorLastArg ('Var 'VZ) (a ':&&: LoT0) (b ':&&: LoT0) where
  gfmaplf _ _ _ f x = f x
instance GFunctorLastArg ('Var 'VZ) (t ':&&: a ':&&: as) (t ':&&: b :&&: bs) where
  gfmaplf _ _ _ _ x = x
instance forall v t a as b bs. GFunctorLastArg ('Var v) (a ':&&: as) (b ':&&: bs)
         => GFunctorLastArg ('Var ('VS v)) (t ':&&: a ':&&: as) (t ':&&: b ':&&: bs) where
  gfmaplf _ _ _ f x = gfmaplf (Proxy @('Var v)) (Proxy @(a ':&&: as)) (Proxy @(b ':&&: bs)) f x

-- Going through functor
instance forall f x xs ys.
         (Functor f, GFunctorLastArg x xs ys)
         => GFunctorLastArg (f :$: x) xs ys where
  gfmaplf _ pxs pys f x = fmap (gfmaplf (Proxy @x) pxs pys f) x

instance forall f y x xs ys.
         (Functor (f (Ty y xs)), Ty y xs ~ Ty y ys,
          GFunctorLastArg x xs ys)
         => GFunctorLastArg (f :$: y :@: x) xs ys where
  gfmaplf _ pxs pys f x = fmap (gfmaplf (Proxy @x) pxs pys f) x

instance forall f y1 y2 x xs ys.
         (Functor (f (Ty y1 xs) (Ty y2 xs)),
          Ty y1 xs ~ Ty y1 ys, Ty y2 xs ~ Ty y2 ys,
          GFunctorLastArg x xs ys)
         => GFunctorLastArg (f :$: y1 :@: y2 :@: x) xs ys where
  gfmaplf _ pxs pys f x = fmap (gfmaplf (Proxy @x) pxs pys f) x