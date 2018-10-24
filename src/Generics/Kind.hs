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
module Generics.Kind (
  module Generics.Kind.Atom
, module Generics.Kind.ListOfTypes
, (:+:)(..), (:*:)(..), U1(..), M1(..)
, F(..), (:=>:)(..), E(..)
, GenericK(..), Conv(..)
, GenericS, fromK', toK'
, fromKDefault, toKDefault
) where

import Data.Proxy
import Data.Kind
import GHC.Generics.Extra hiding ((:=>:))
import qualified GHC.Generics.Extra as GG

import Generics.Kind.Atom
import Generics.Kind.ListOfTypes

newtype F (t :: Atom d (*)) (x :: LoT d) = F { unF :: Ty t x }
deriving instance Show (Ty t x) => Show (F t x)

data (:=>:) (c :: Atom d Constraint) (f :: LoT d -> *) (x :: LoT d) where
  C :: Ty c x => f x -> (c :=>: f) x

data E (f :: LoT (k -> d) -> *) (x :: LoT d) where
  E :: forall (t :: k) d (f :: LoT (k -> d) -> *) (x :: LoT d)
     . f (t :&&: x) -> E f x

-- THE TYPE CLASS

class GenericK (f :: k) where
  type RepK f :: LoT k -> *
  fromK :: SLoT x -> f :@@: x -> RepK f x
  toK   :: SLoT x -> RepK f x -> f :@@: x

type GenericS f t = (GenericK f, SForLoT (Split t f), t ~ Apply f (Split t f))

fromK' :: forall f t. GenericS f t
       => t -> RepK f (Split t f)
fromK' x = fromK slot (split @f x)

toK' :: forall f t. GenericS f t
     => RepK f (Split t f) -> t
toK' x = unsplit @f (toK slot x)

-- DEFAULT IMPLEMENTATIONS

fromKDefault :: (Generic (Apply f x), SForLoT x, Conv (Rep (Apply f x)) (RepK f) x)
             => f :@@: x -> RepK f x
fromKDefault = toKindGenerics . from . unravel

toKDefault :: (Generic (Apply f x), SForLoT x, Conv (Rep (Apply f x)) (RepK f) x)
           => RepK f x -> f :@@: x
toKDefault = ravel . to . toGhcGenerics

-- CONVERSION BETWEEN GHC.GENERICS AND KIND-GENERICS

class Conv (gg :: * -> *) (kg :: LoT d -> *) (tys :: LoT d) where
  toGhcGenerics  :: kg tys -> gg a
  toKindGenerics :: gg a -> kg tys

instance Conv U1 U1 tys where
  toGhcGenerics  U1 = U1
  toKindGenerics U1 = U1

instance (Conv f f' tys, Conv g g' tys) => Conv (f :+: g) (f' :+: g') tys where
  toGhcGenerics  (L1 x) = L1 (toGhcGenerics  x)
  toGhcGenerics  (R1 x) = R1 (toGhcGenerics  x)
  toKindGenerics (L1 x) = L1 (toKindGenerics x)
  toKindGenerics (R1 x) = R1 (toKindGenerics x)

instance (Conv f f' tys, Conv g g' tys) => Conv (f :*: g) (f' :*: g') tys where
  toGhcGenerics  (x :*: y) = toGhcGenerics  x :*: toGhcGenerics  y
  toKindGenerics (x :*: y) = toKindGenerics x :*: toKindGenerics y

instance (Conv f f' tys) => Conv (M1 i c f) f' {- (M1 i c f') -} tys where
  toGhcGenerics  x = M1 (toGhcGenerics  x)
  toKindGenerics (M1 x) = toKindGenerics x

instance (k ~ Ty t tys, Conv f f' tys)
         => Conv (k GG.:=>: f) (t :=>: f') tys where
  toGhcGenerics (C x) = SuchThat (toGhcGenerics x)
  toKindGenerics (SuchThat x) = C (toKindGenerics x)

instance (k ~ Ty t tys) => Conv (K1 p k) (F t) tys where
  toGhcGenerics  (F x)  = K1 x
  toKindGenerics (K1 x) = F x