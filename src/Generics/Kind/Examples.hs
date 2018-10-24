{-# language TypeOperators #-}
{-# language TypeFamilies  #-}
{-# language DataKinds     #-}
module Generics.Kind.Examples where

import Data.Proxy
import GHC.Generics (from, to)

import Generics.Kind

instance GenericK Maybe where
  type RepK Maybe = U1 :+: F V0

  fromK SLoT1 = fromKDefault
  toK   SLoT1 = toKDefault