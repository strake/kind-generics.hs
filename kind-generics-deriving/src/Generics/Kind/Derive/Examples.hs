{-# OPTIONS_GHC -fno-warn-orphans  #-}
{-# language TypeOperators         #-}
{-# language DataKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language TypeApplications      #-}
{-# language ScopedTypeVariables   #-}
{-# language InstanceSigs          #-}
module Generics.Kind.Derive.Examples where

import Data.Aeson (ToJSON(..), FromJSON(..))
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
import Generics.Kind.Derive.Json

-- Maybe
instance KFunctor Maybe '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault

-- Tree
instance Eq a => Eq (Tree a) where
  (==) = geq'
instance ToJSON a => ToJSON (Tree a) where
  toJSON = gtoJSON'
instance FromJSON a => FromJSON (Tree a) where
  parseJSON = gfromJSON'
instance KFunctor Tree '[ 'Co ] (a ':&&: 'LoT0) (b ':&&: 'LoT0) where
  kfmap = kfmapDefault
instance Functor Tree where
  -- fmap = fmapDefault
  fmap = fmapDefaultOne
instance Foldable Tree where
  foldMap = foldMapDefault
instance Traversable Tree where
  traverse = traverseDefault

-- TTY (from https://gitlab.com/trupill/kind-generics/issues/3)
instance Eq (TTY m a) where
  (==) = geq'
instance ToJSON (TTY m a) where
  toJSON = gtoJSON'
{-
instance FromJSON (TTY m a) where
  parseJSON = gfromJSON'

Fails with:
• Couldn't match type ‘a’ with ‘()’ arising from a use of ‘gfromJSON'’
-}

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