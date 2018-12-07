{-# OPTIONS_GHC -fno-warn-orphans  #-}
{-# language TypeOperators         #-}
{-# language DataKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language TypeApplications      #-}
{-# language ScopedTypeVariables   #-}
{-# language InstanceSigs          #-}
module Generics.Kind.Derive.Examples where

import Data.PolyKinded.Functor
import Data.Traversable (foldMapDefault)

import Generics.Kind
import Generics.Kind.Examples
import Generics.Kind.Derive.Eq
import Generics.Kind.Derive.EqTwoParams
import Generics.Kind.Derive.FunctorPosition
import Generics.Kind.Derive.FunctorOne
import Generics.Kind.Derive.KFunctor
import Generics.Kind.Derive.Traversable

-- Maybe
instance KFunctor Maybe '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault

-- Tree
instance Eq a => Eq (Tree a) where
  (==) = geq'
instance KFunctor Tree '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault
instance Functor Tree where
  -- fmap = fmapDefault
  fmap = fmapDefaultOne
instance Foldable Tree where
  foldMap = foldMapDefault
instance Traversable Tree where
  traverse = traverseDefault

fmapEither :: (a -> b) -> Either e a -> Either e b
fmapEither = fmapDefault'

-- WeirdTree
instance Show b => KFunctor WeirdTree '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault

-- WeirdTree with reflected existentials
-- instance (Eq a) => Eq (WeirdTreeR a) where
  -- (==) = geq'

instance Functor (SimpleIndex a) where
  fmap = fmapDefault
instance Foldable (SimpleIndex a) where
  foldMap = foldMapDefault
instance Traversable (SimpleIndex a) where
  traverse = traverseDefault