{-# language TypeOperators         #-}
{-# language TypeFamilies          #-}
{-# language DataKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
module Generics.Kind.Examples where

import Data.Proxy
import GHC.Generics (from, to)

import Generics.Kind
import Generics.Kind.Derive.Functor

instance GenericK Maybe where
  type RepK Maybe = U1 :+: F V0

  fromK SLoT1 = fromKDefault
  toK   SLoT1 = toKDefault

instance KFunctor Maybe '[Co] (a :&&: LoT0) (b :&&: LoT0) where