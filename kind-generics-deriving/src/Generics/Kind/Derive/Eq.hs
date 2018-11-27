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
{-# language ConstraintKinds       #-}
module Generics.Kind.Derive.Eq where

import Data.Kind
import Generics.Kind
import GHC.TypeLits
import Type.Reflection

geq' :: forall t. (GenericK t LoT0, GEq (RepK t), ReqsEq (RepK t) LoT0)
     => t -> t -> Bool
geq' x y = geq (fromK @_ @t @LoT0 x) (fromK @_ @t @LoT0 y)

class GEq (f :: LoT k -> *) where
  type ReqsEq f (tys :: LoT k) :: Constraint
  geq :: ReqsEq f tys => f tys -> f tys -> Bool

instance GEq U1 where
  type ReqsEq U1 tys = ()
  geq U1 U1 = True

instance GEq f => GEq (M1 i c f) where
  type ReqsEq (M1 i c f) tys = ReqsEq f tys
  geq (M1 x) (M1 y) = geq x y

instance (GEq f, GEq g) => GEq (f :+: g) where
  type ReqsEq (f :+: g) tys = (ReqsEq f tys, ReqsEq g tys)
  geq (L1 x) (L1 y) = geq x y
  geq (R1 x) (R1 y) = geq x y
  geq _      _      = False

instance (GEq f, GEq g) => GEq (f :*: g) where
  type ReqsEq (f :*: g) tys = (ReqsEq f tys, ReqsEq g tys)
  geq (x1 :*: x2) (y1 :*: y2) = geq x1 y1 && geq x2 y2

instance GEq (F t) where
  type ReqsEq (F t) tys = Eq (Ty t tys)
  geq (F x) (F y) = x == y

instance GEq f => GEq (c :=>: f) where
  type ReqsEq (c :=>: f) tys = ReqsEq f tys
  -- really we want          = Ty c tys => GEq f tys
  geq (C x) (C y) = geq x y

instance TypeError (Text "Existentials are not supported")
         => GEq (E f) where
  geq = undefined