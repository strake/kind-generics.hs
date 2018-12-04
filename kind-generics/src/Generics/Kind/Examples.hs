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
{-# language RankNTypes            #-}
{-# language UnboxedTuples         #-}
module Generics.Kind.Examples where

import Data.PolyKinded.Functor
import GHC.Generics (Generic)
import GHC.TypeLits
import Type.Reflection (Typeable)
import Data.Proxy

import Generics.Kind

-- Obtained from Generic

instance GenericK Maybe (a ':&&: 'LoT0) where
  type RepK Maybe = U1 :+: Field Var0
instance GenericK (Maybe a) LoT0 where
  type RepK (Maybe a) = SubstRep (RepK Maybe) a
  fromK = fromRepK
  toK   = toRepK

instance GenericK Either (a ':&&: b ':&&: LoT0) where
  type RepK Either = Field Var0 :+: Field Var1
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
  type RepK Tree = Field (Tree :$: Var0) :*: Field (Tree :$: Var0) :+: Field Var0
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
  type RepK (HappyFamily (Maybe a)) = Field (Kon Bool)
  fromK (HFM   x) = Field x
  toK   (Field x) = HFM   x

instance GenericK (HappyFamily [a]) 'LoT0 where
  type RepK (HappyFamily [a]) = Field (Kon a)
  fromK (HFL   x) = Field x
  toK   (Field x) = HFL   x

-- Hand-written instance

data WeirdTree a where
  WeirdBranch :: WeirdTree a -> WeirdTree a -> WeirdTree a 
  WeirdLeaf   :: Show a => t -> a -> WeirdTree a

instance GenericK WeirdTree (a ':&&: 'LoT0) where
  type RepK WeirdTree
    = Field (WeirdTree :$: Var0) :*: Field (WeirdTree :$: Var0)
      :+: Exists (*) ((Show :$: Var1) :=>: (Field Var0 :*: Field Var1))

  fromK (WeirdBranch l r) = L1 $                     Field l :*: Field r
  fromK (WeirdLeaf   a x) = R1 $ Exists $ SuchThat $ Field a :*: Field x

  toK (L1 (Field l :*: Field r)) = WeirdBranch l r
  toK (R1 (Exists (SuchThat (Field a :*: Field x)))) = WeirdLeaf a x

-- Hand-written instance with reflection

data WeirdTreeR a where
  WeirdBranchR :: WeirdTreeR a -> WeirdTreeR a -> WeirdTreeR a 
  WeirdLeafR   :: (Show a, Eq t, Typeable t) => t -> a -> WeirdTreeR a

instance GenericK WeirdTreeR (a ':&&: 'LoT0) where
  type RepK WeirdTreeR
    = Field (WeirdTreeR :$: Var0) :*: Field (WeirdTreeR :$: Var0)
      :+: Exists (*) (((Show :$: Var1) :&: (Eq :$: Var0) :&: (Typeable :$: Var0))
                      :=>: (Field Var0 :*: Field Var1))

  fromK (WeirdBranchR l r) = L1 $                     Field l :*: Field r
  fromK (WeirdLeafR   a x) = R1 $ Exists $ SuchThat $ Field a :*: Field x

  toK (L1 (Field l :*: Field r)) = WeirdBranchR l r
  toK (R1 (Exists (SuchThat (Field a :*: Field x)))) = WeirdLeafR a x

instance GenericK (WeirdTreeR a) 'LoT0 where
  type RepK (WeirdTreeR a)
    = Field (Kon (WeirdTreeR a)) :*: Field (Kon (WeirdTreeR a))
    :+: Exists (*) ((Kon (Show a) :&: (Eq :$: Var0) :&: (Typeable :$: Var0))
                    :=>: ((Field Var0 :*: Field (Kon a))))

  fromK (WeirdBranchR l r) = L1 $                     Field l :*: Field r
  fromK (WeirdLeafR   a x) = R1 $ Exists $ SuchThat $ Field a :*: Field x

  toK (L1 (Field l :*: Field r)) = WeirdBranchR l r
  toK (R1 (Exists (SuchThat (Field a :*: Field x)))) = WeirdLeafR a x

-- Weird-kinded types

data T (a :: k) where
  MkT :: forall (a :: *). Maybe a -> T a

{- GHC rewrites this to the following Core
data T (a :: k) =
  forall (a' :: Type). (k ~ Type, a ~~ a') => MkT (Maybe a') 
-}

instance GenericK (T :: k -> *) (a :&&: LoT0) where
  type RepK (T :: k -> *) =
    Exists (*) ((Kon (k ~ (*)) :&: (Var0 :~~: Var1)) :=>: Field (Maybe :$: Var0))
  fromK (MkT x) = Exists (SuchThat (Field x))
  toK (Exists (SuchThat (Field x))) = MkT x

data P k (a :: k) where
  P :: forall k (a :: k). P k a

instance GenericK (P k) ((a :: k) :&&: LoT0) where
  type RepK (P k) = U1
  fromK P  = U1
  toK   U1 = P

{- This does not work
instance GenericK P (k :&&: a :&&: LoT0) where
  type RepK P = KindOf Var1 :~: Var0 :=>: U1
-}

data P' j (a :: k) where
  P' :: forall k (a :: k). P' k a

instance GenericK (P' j :: k -> *) (a :&&: LoT0) where
  type RepK (P' j :: k -> *) = (Kon k :~: Kon j) :=>: U1
  fromK P' = SuchThat U1
  toK (SuchThat U1) = P'

instance GenericK (P' :: * -> k -> *) (j :&&: a :&&: LoT0) where
  type RepK (P' :: * -> k -> *) = (Kon k :~: Var0) :=>: U1
  fromK P' = SuchThat U1
  toK (SuchThat U1) = P'

-- Rank-N types

data Ranky = MkRanky (forall a. a -> a)

instance GenericK Ranky LoT0 where
  type RepK Ranky = Field (ForAll ((->) :$: Var0 :@: Var0))
  fromK (MkRanky x) = Field (ForAllI x)
  toK (Field (ForAllI x)) = MkRanky x

newtype Ranky2 b = MkRanky2 ((forall a. a -> a) -> b)

instance GenericK Ranky2 (b ':&&: LoT0) where
  type RepK Ranky2 = Field ((->) :$: ForAll ((->) :$: Var0 :@: Var0) :@: Var0)
  fromK (MkRanky2 f) = Field (\(ForAllI x) -> f x)
  toK (Field f) = MkRanky2 (\x -> f (ForAllI x))

data Shower a where
  MkShower :: (Show a => a -> String) -> Shower a

instance GenericK Shower (a ':&&: LoT0) where
  type RepK Shower = Field ((Show :$: Var0) :=>>: ((->) :$: Var0 :@: Kon String))
  fromK (MkShower f) = Field (SuchThatI f)
  toK (Field (SuchThatI f)) = MkShower f

-- Other representation types

data Unboxed1 = MkUnboxed1 (# Int, Int #)
{- -- We cannot write this
instance GenericK Unboxed1 'LoT0 where
  type RepK Unboxed1 = Field (Kon (# Int, Int #))
  -- fromK (MkUnboxed1 x) = Field x
  -- toK (Field x) = MkUnboxed1 x
  fromK = undefined
  toK   = undefined
-}