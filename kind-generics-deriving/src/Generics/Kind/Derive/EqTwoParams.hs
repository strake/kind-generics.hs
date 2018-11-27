{-# language DataKinds             #-}
{-# language PolyKinds             #-}
{-# language KindSignatures        #-}
{-# language MultiParamTypeClasses #-}
{-# language QuantifiedConstraints #-}
{-# language TypeOperators         #-}
{-# language FlexibleInstances     #-}
{-# language FlexibleContexts      #-}
{-# language UndecidableInstances  #-}
{-# language AllowAmbiguousTypes   #-}
{-# language ScopedTypeVariables   #-}
{-# language TypeFamilies          #-}
{-# language TypeApplications      #-}
module Generics.Kind.Derive.EqTwoParams where

import Generics.Kind
import GHC.TypeLits
import Type.Reflection

geq2' :: forall t. (GenericK t LoT0, GEq2 (RepK t) LoT0 LoT0)
      => t -> t -> Bool
geq2' x y = geq2 (fromK @_ @t @LoT0 x) (fromK @_ @t @LoT0 y)

class GEq2 (f :: LoT k -> *) (xs :: LoT k) (ys :: LoT k) where
  geq2 :: f xs -> f ys -> Bool

instance GEq2 U1 xs ys where
  geq2 U1 U1 = True

instance (GEq2 f xs ys) => GEq2 (M1 i c f) xs ys where
  geq2 (M1 x) (M1 y) = geq2 x y

instance (GEq2 f xs ys, GEq2 g xs ys) => GEq2 (f :+: g) xs ys where
  geq2 (L1 x) (L1 y) = geq2 x y
  geq2 (R1 x) (R1 y) = geq2 x y
  geq2 _      _      = False

instance (GEq2 f xs ys, GEq2 g xs ys) => GEq2 (f :*: g) xs ys where
  geq2 (x1 :*: x2) (y1 :*: y2) = geq2 x1 y1 && geq2 x2 y2

instance (xs ~ ys, Eq (Ty t xs)) => GEq2 (F t) xs ys where
  geq2 (F x) (F y) = x == y

instance ((Ty c xs, Ty c ys) => GEq2 f xs ys)
         => GEq2 (c :=>: f) xs ys where
  geq2 (C x) (C y) = geq2 x y

instance (forall x y. GEq2 f (x ':&&: xs) (y ':&&: ys))
         => GEq2 (E f) xs ys where
  geq2 (E x) (E y) = geq2 x y

instance (forall x y. GEq2 f (x ':&&: xs) (y ':&&: ys))
         => GEq2 (ERefl f) xs ys where
  geq2 (ERefl (x :: f (x :&&: xs))) (ERefl (y :: f (y :&&: ys)))
    = case eqTypeRep (typeRep @x) (typeRep @y) of
        Nothing    -> False
        Just HRefl -> geq2 x y