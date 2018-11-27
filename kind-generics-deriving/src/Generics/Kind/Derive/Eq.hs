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
module Generics.Kind.Derive.Eq where

import Generics.Kind
import GHC.TypeLits
import Type.Reflection

geq' :: forall t. (GenericK t LoT0, GEq (RepK t) LoT0)
     => t -> t -> Bool
geq' x y = geq (fromK @_ @t @LoT0 x) (fromK @_ @t @LoT0 y)

class GEq (f :: LoT k -> *) (tys :: LoT k) where
  geq :: f tys -> f tys -> Bool

instance GEq U1 tys where
  geq U1 U1 = True

instance (GEq f tys) => GEq (M1 i c f) tys where
  geq (M1 x) (M1 y) = geq x y

instance (GEq f tys, GEq g tys) => GEq (f :+: g) tys where
  geq (L1 x) (L1 y) = geq x y
  geq (R1 x) (R1 y) = geq x y
  geq _      _      = False

instance (GEq f tys, GEq g tys) => GEq (f :*: g) tys where
  geq (x1 :*: x2) (y1 :*: y2) = geq x1 y1 && geq x2 y2

instance (Eq (Ty t tys)) => GEq (F t) tys where
  geq (F x) (F y) = x == y

instance (Ty c tys => GEq f tys) => GEq (c :=>: f) tys where
  geq (C x) (C y) = geq x y

instance (forall t. (GEq f (t :&&: tys), Typeable t)) => GEq (E f) tys where
  geq (E (x :: f (t1 :&&: tys))) (E (y :: f (t2 :&&: tys)))
    = case eqTypeRep (typeRep @t1) (typeRep @t2) of
        Nothing    -> False
        Just HRefl -> geq x y