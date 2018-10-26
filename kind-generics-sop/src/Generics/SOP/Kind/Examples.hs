{-# language TypeOperators         #-}
{-# language TypeFamilies          #-}
{-# language DataKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
module Generics.SOP.Kind.Examples where

import Data.PolyKinded.Functor

import Generics.SOP.Kind
-- import Generics.Kind.Derive.Functor

instance HeadOf (Maybe a) Maybe
instance GenericK Maybe (a ':&&: 'LoT0) where
  type CodeK Maybe = '[ '[] :=>: '[], '[] :=>: '[V0] ]

{-
instance KFunctor Maybe '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault
-}