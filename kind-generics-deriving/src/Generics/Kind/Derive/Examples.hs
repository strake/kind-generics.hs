{-# OPTIONS_GHC -fno-warn-orphans  #-}
{-# language TypeOperators         #-}
{-# language DataKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
module Generics.Kind.Derive.Examples where

import Data.PolyKinded.Functor
import Data.Proxy
import Data.Traversable (foldMapDefault)
import GHC.Generics (Generic)
import Type.Reflection

import Generics.Kind
import Generics.Kind.Examples
import Generics.Kind.Derive.Eq
import Generics.Kind.Derive.EqTwoParams
import Generics.Kind.Derive.FunctorLast
import Generics.Kind.Derive.KFunctor
import Generics.Kind.Derive.Traversable

-- Maybe
instance KFunctor Maybe '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault

-- Tree
instance Eq a => Eq (Tree a) where
  (==) = geq2'
instance KFunctor Tree '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault
instance Functor Tree where
  -- fmap = fmapDefault
  -- fmap = fmapDefaultPos (Proxy :: Proxy VZ)
  fmap = fmapDefaultLast
instance Foldable Tree where
  foldMap = foldMapDefault
instance Traversable Tree where
  traverse = traverseDefault (Proxy :: Proxy VZ)

-- WeirdTree
instance Show b => KFunctor WeirdTree '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault

-- WeirdTree with reflected existentials
instance (Eq a) => Eq (WeirdTreeR a) where
  (==) = geq2'

{-
instance Show b => KFunctor WeirdTreeR '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault
instance Functor WeirdTreeR where
  fmap = fmap1DefaultS (Proxy :: Proxy VZ)
-}
