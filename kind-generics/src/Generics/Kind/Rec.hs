{-# language DataKinds                 #-}
{-# language KindSignatures            #-}
{-# language PolyKinds                 #-}
{-# language TypeFamilies              #-}
{-# language GADTs                     #-}
{-# language ConstraintKinds           #-}
{-# language TypeOperators             #-}
{-# language StandaloneDeriving        #-}
{-# language FlexibleContexts          #-}
{-# language UndecidableInstances      #-}
{-# language MultiParamTypeClasses     #-}
{-# language FlexibleInstances         #-}
{-# language ExistentialQuantification #-}
{-# language DefaultSignatures         #-}
{-# language ScopedTypeVariables       #-}
{-# language TypeApplications          #-}
{-# language AllowAmbiguousTypes       #-}
{-# language QuantifiedConstraints     #-}
-- | Version of @kind-generics@ with explicit recursion.
--   Note that 'Atom' comes from the 'Atom.Rec' module!
module Generics.Kind.Rec (
  module Data.PolyKinded
, module Data.PolyKinded.Atom.Rec
  -- * Generic representation types
, (:+:)(..), (:*:)(..), V1, U1(..), M1(..)
, Field(..), (:=>:)(..), Exists(..)
  -- * Generic type classes
, GenericK(..)
) where

import Data.PolyKinded
import Data.PolyKinded.Atom.Rec
import Data.Kind
import GHC.Generics.Extra hiding ((:=>:), SuchThat)

newtype Field (t :: Atom r d (*)) (rx :: RecLoT r d) where
  Field :: { unField :: Interpret t rx } -> Field t rx
deriving instance Show (Interpret t rx) => Show (Field t rx)

data (:=>:) (c :: Atom r d Constraint) (f :: RecLoT r d -> *) (rx :: RecLoT r d) where
  SuchThat :: Interpret c rx => f rx -> (c :=>: f) rx
deriving instance (Interpret c rx => Show (f rx)) => Show ((c :=>: f) rx)

data Exists k (f :: RecLoT r (k -> d) -> *) (x :: RecLoT r d) where
  Exists :: forall (t :: k) r d (f :: RecLoT r (k -> d) -> *) (q :: r) (x :: LoT d)
          .{ unExists :: f '(q, t ':&&: x) } -> Exists k f '(q, x)
deriving instance (forall t. Show (f '(r, t ':&&: x))) => Show (Exists k f '(r, x))

-- THE TYPE CLASS

class GenericK (f :: k) (x :: LoT k) where
  type RepK f :: RecLoT k k -> *
  -- | Convert the data type to its representation.
  fromK :: f :@@: x -> RepK f '(f, x)
  -- | Convert from a representation to its corresponding data type.
  toK   :: RepK f '(f, x) -> f :@@: x