{-# OPTIONS_GHC -fno-warn-orphans  #-}
{-# language TypeOperators         #-}
{-# language TypeFamilies          #-}
{-# language DataKinds             #-}
{-# language PolyKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language GADTs                 #-}
{-# language DeriveGeneric         #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances  #-}
module Generics.Kind.Examples where

import Data.PolyKinded.Functor
import GHC.Generics (Generic)
import GHC.TypeLits
import Type.Reflection (Typeable)

import Generics.Kind

-- Obtained from Generic

instance GenericK Maybe (a ':&&: 'LoT0) where
  type RepK Maybe = U1 :+: F V0
instance GenericK (Maybe a) LoT0 where
  type RepK (Maybe a) = SubstRep (RepK Maybe) a
  fromK = fromRepK
  toK   = toRepK

instance GenericK Either (a ':&&: b ':&&: LoT0) where
  type RepK Either = F V0 :+: F V1
instance GenericK (Either a) (b ':&&: LoT0) where
  type RepK (Either a) = SubstRep (RepK Either) a
  fromK = fromRepK
  toK   = toRepK
instance GenericK (Either a b) LoT0 where
  type RepK (Either a b) = SubstRep (RepK (Either a)) b
  fromK = fromRepK
  toK   = toRepK

-- From the docs

data Tree a = Branch (Tree a) (Tree a) | Leaf a
            deriving Generic

instance GenericK Tree (a ':&&: 'LoT0) where
  type RepK Tree = F (Tree :$: V0) :*: F (Tree :$: V0) :+: F V0
instance GenericK (Tree a) LoT0 where
  type RepK (Tree a) = SubstRep (RepK Tree) a
  fromK = fromRepK
  toK   = toRepK

-- Data family

data family HappyFamily t
data instance HappyFamily (Maybe a) = HFM Bool
data instance HappyFamily [a]       = HFL a

instance GenericK HappyFamily (a ':&&: 'LoT0) where
  type RepK HappyFamily = TypeError (Text "Cannot describe this family uniformly")
  fromK = undefined
  toK   = undefined

instance GenericK (HappyFamily (Maybe a)) 'LoT0 where
  type RepK (HappyFamily (Maybe a)) = F (Kon Bool)
  fromK (HFM x) = F   x
  toK   (F   x) = HFM x

instance GenericK (HappyFamily [a]) 'LoT0 where
  type RepK (HappyFamily [a]) = F (Kon a)
  fromK (HFL x) = F   x
  toK   (F   x) = HFL x

-- Hand-written instance

data WeirdTree a where
  WeirdBranch :: WeirdTree a -> WeirdTree a -> WeirdTree a 
  WeirdLeaf   :: Show a => t -> a -> WeirdTree a

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
  WeirdLeafR   :: (Show a, Eq t, Typeable t) => t -> a -> WeirdTreeR a

instance GenericK WeirdTreeR (a ':&&: 'LoT0) where
  type RepK WeirdTreeR
    = F (WeirdTreeR :$: V0) :*: F (WeirdTreeR :$: V0)
      :+: E (((Show :$: V1) :&: (Eq :$: V0) :&: (Typeable :$: V0)) :=>: (F V0 :*: F V1))

  fromK (WeirdBranchR l r) = L1 $         F l :*: F r
  fromK (WeirdLeafR   a x) = R1 $ E $ C $ F a :*: F x

  toK (L1 (F l :*: F r)) = WeirdBranchR l r
  toK (R1 (E (C (F a :*: F x)))) = WeirdLeafR a x

instance GenericK (WeirdTreeR a) 'LoT0 where
  type RepK (WeirdTreeR a)
    = F (Kon (WeirdTreeR a)) :*: F (Kon (WeirdTreeR a))
    :+: E ((Kon (Show a) :&: (Eq :$: V0) :&: (Typeable :$: V0)) :=>: ((F V0 :*: F (Kon a))))

  fromK (WeirdBranchR l r) = L1 $         F l :*: F r
  fromK (WeirdLeafR   a x) = R1 $ E $ C $ F a :*: F x

  toK (L1 (F l :*: F r)) = WeirdBranchR l r
  toK (R1 (E (C (F a :*: F x)))) = WeirdLeafR a x

-- Weird-kinded types

data T (a :: k) where
  MkT :: forall (a :: *). Maybe a -> T a

instance GenericK (T :: k -> *) (a :&&: LoT0) where
  type RepK (T :: k -> *) =
    Kon (k ~ (*)) :=>: F (Maybe :$: ForceKind (V0 :: Atom (* -> *) *) (Atom (k -> *) *))

  fromK (MkT x) = C (F x)
  toK (C (F x)) = MkT x

data P k (a :: k) where
  P :: forall k (a :: k). P k a

instance GenericK (P k) ((a :: k) :&&: LoT0) where
  type RepK (P k) = U1
  fromK P  = U1
  toK   U1 = P

{- This does not work
instance GenericK P (k :&&: a :&&: LoT0) where
  type RepK P = KindOf V1 :~: V0 :=>: U1
-}

data P' j (a :: k) where
  P' :: forall k (a :: k). P' k a

instance GenericK (P' j) ((a :: k) :&&: LoT0) where
  type RepK (P' j) = (KindOf V0 :~: Kon j) :=>: U1
  fromK P' = C U1
  toK   (C U1) = P'

instance GenericK P' (j :&&: (a :: k) :&&: LoT0) where
  type RepK P' = (KindOf V1 :~: V0) :=>: U1
  fromK P' = C U1
  toK   (C U1) = P'
