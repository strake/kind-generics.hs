{-# OPTIONS_GHC -fno-warn-orphans  #-}
{-# language TypeOperators         #-}
{-# language TypeFamilies          #-}
{-# language DataKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language GADTs                 #-}
{-# language DeriveGeneric         #-}
{-# language QuantifiedConstraints #-}
module Generics.Kind.Examples where

import Data.PolyKinded.Functor
import GHC.Generics (Generic)
import Type.Reflection

import Generics.Kind

-- Obtained from Generic

instance Split (Maybe a) Maybe (a ':&&: 'LoT0)
instance GenericK Maybe (a ':&&: 'LoT0) where
  type RepK Maybe = U1 :+: F V0

instance Split (Either a b) Either (a ':&&: b ':&&: LoT0)
instance GenericK Either (a ':&&: b ':&&: LoT0) where
  type RepK Either = F V0 :+: F V1

-- From the docs

data Tree a = Branch (Tree a) (Tree a) | Leaf a
            deriving Generic

instance Split (Tree a) Tree (a ':&&: 'LoT0)
instance GenericK Tree (a ':&&: 'LoT0) where
  type RepK Tree = F (Tree :$: V0) :*: F (Tree :$: V0) :+: F V0

-- Hand-written instance

data WeirdTree a where
  WeirdBranch :: WeirdTree a -> WeirdTree a -> WeirdTree a 
  WeirdLeaf   :: Show a => t -> a -> WeirdTree a

instance Split (WeirdTree a) WeirdTree (a ':&&: 'LoT0)
instance GenericK WeirdTree (a ':&&: 'LoT0) where
  type RepK WeirdTree
    = F (WeirdTree :$: V0) :*: F (WeirdTree :$: V0)
      :+: E ((Show :$: V1) :=>: (F V0 :*: F V1))

  fromK (WeirdBranch l r) = L1 $         F l :*: F r
  fromK (WeirdLeaf   a x) = R1 $ E $ C $ F a :*: F x

  toK (L1 (F l :*: F r)) = WeirdBranch l r
  toK (R1 (E (C (F a :*: F x)))) = WeirdLeaf a x

-- Hand-written instance with reflection

data WeirdTreeR a where
  WeirdBranchR :: WeirdTreeR a -> WeirdTreeR a -> WeirdTreeR a 
  WeirdLeafR   :: (Show a, Typeable t, Eq t) => t -> a -> WeirdTreeR a

instance Split (WeirdTreeR a) WeirdTreeR (a ':&&: 'LoT0)
instance GenericK WeirdTreeR (a ':&&: 'LoT0) where
  type RepK WeirdTreeR
    = F (WeirdTreeR :$: V0) :*: F (WeirdTreeR :$: V0)
      :+: ERefl ((Show :$: V1) :=>: ((Eq :$: V0) :=>: (F V0 :*: F V1)))

  fromK (WeirdBranchR l r) = L1 $                 F l :*: F r
  fromK (WeirdLeafR   a x) = R1 $ ERefl $ C $ C $ F a :*: F x

  toK (L1 (F l :*: F r)) = WeirdBranchR l r
  toK (R1 (ERefl (C (C (F a :*: F x))))) = WeirdLeafR a x