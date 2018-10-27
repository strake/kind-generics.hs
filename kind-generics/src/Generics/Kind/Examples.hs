{-# language TypeOperators         #-}
{-# language TypeFamilies          #-}
{-# language DataKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language GADTs                 #-}
module Generics.Kind.Examples where

import Data.PolyKinded.Functor

import Generics.Kind
import Generics.Kind.Derive.Functor

-- Obtained from Generic

instance HeadOf (Maybe a) Maybe
instance GenericK Maybe (a ':&&: 'LoT0) where
  type RepK Maybe = U1 :+: F V0

instance KFunctor Maybe '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault

-- Hand-written instance

data WeirdTree a where
  WeirdBranch :: WeirdTree a -> WeirdTree a -> WeirdTree a 
  WeirdLeaf   :: Show a => t -> a -> WeirdTree a

instance HeadOf (WeirdTree a) WeirdTree
instance GenericK WeirdTree (a ':&&: 'LoT0) where
  type RepK WeirdTree
    = F (WeirdTree :$: V0) :*: F (WeirdTree :$: V0)
      :+: E ((Show :$: V1) :=>: (F V0 :*: F V1))

  fromK (WeirdBranch l r) = L1 $         F l :*: F r
  fromK (WeirdLeaf   a x) = R1 $ E $ C $ F a :*: F x

  toK (L1 (F l :*: F r)) = WeirdBranch l r
  toK (R1 (E (C (F a :*: F x)))) = WeirdLeaf a x

instance Show b => KFunctor WeirdTree '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault