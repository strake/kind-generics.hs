{-# OPTIONS_GHC -fno-warn-orphans  #-}
{-# language TypeOperators         #-}
{-# language DataKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
module Generics.Kind.Derive.Examples where

import Data.PolyKinded.Functor
import Data.Proxy
import GHC.Generics (Generic)
import Type.Reflection

import Generics.Kind
import Generics.Kind.Examples
import Generics.Kind.Derive.Eq
import Generics.Kind.Derive.Functor
import Generics.Kind.Derive.KFunctor

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
  fmap = fmap1DefaultS (Proxy :: Proxy VZ)

-- WeirdTree
instance Show b => KFunctor WeirdTree '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault

-- WeirdTree with reflected existentials
instance (Eq a) => Eq (WeirdTreeR a) where
  (==) = geq'

{-
instance Show b => KFunctor WeirdTreeR '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault
-}