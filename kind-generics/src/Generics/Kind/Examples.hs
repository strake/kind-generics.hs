{-# language TypeOperators         #-}
{-# language TypeFamilies          #-}
{-# language DataKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
module Generics.Kind.Examples where

import Data.PolyKinded.Functor

import Generics.Kind
import Generics.Kind.Derive.Functor

instance HeadOf (Maybe a) Maybe
instance GenericK Maybe (a ':&&: 'LoT0) where
  type RepK Maybe = U1 :+: F V0

instance KFunctor Maybe '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault