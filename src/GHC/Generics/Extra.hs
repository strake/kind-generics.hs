{-# language KindSignatures  #-}
{-# language ConstraintKinds #-}
{-# language PolyKinds       #-}
{-# language GADTs           #-}
{-# language TypeOperators   #-}
module GHC.Generics.Extra (
  module GHC.Generics
, C1(..)
) where

import Data.Kind
import GHC.Generics

data (:=>:) (c :: Constraint) (f :: k -> *) (a :: k) where
  SuchThat :: c => f a -> (c :=>: f) a