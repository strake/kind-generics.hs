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
  module Data.PolyKinded
, module Data.PolyKinded.Atom
, (:+:)(..), (:*:)(..), U1(..), M1(..)
, F(..), (:=>:)(..), E(..)
, GenericK(..), Conv(..)
, GenericF, fromF, toF
, GenericN, fromN, toN
, GenericS, fromS, toS
) where

import Data.PolyKinded
import Data.PolyKinded.Atom
import Data.Kind
import GHC.Generics.Extra hiding ((:=>:))
import qualified GHC.Generics.Extra as GG

newtype F (t :: Atom d (*)) (x :: LoT d) = F { unF :: Ty t x }
deriving instance Show (Ty t x) => Show (F t x)

data (:=>:) (c :: Atom d Constraint) (f :: LoT d -> *) (x :: LoT d) where
  C :: Ty c x => f x -> (c :=>: f) x

data E (f :: LoT (k -> d) -> *) (x :: LoT d) where
  E :: forall (t :: k) d (f :: LoT (k -> d) -> *) (x :: LoT d)
     . f (t ':&&: x) -> E f x

-- THE TYPE CLASS

class GenericK (f :: k) (x :: LoT k) where
  type RepK f :: LoT k -> *
  
  fromK :: f :@@: x -> RepK f x
  default
    fromK :: (Generic (f :@@: x), Conv (Rep (f :@@: x)) (RepK f) x)
          => f :@@: x -> RepK f x
  fromK = toKindGenerics . from

  toK   :: RepK f x -> f :@@: x
  default
    toK :: (Generic (f :@@: x), Conv (Rep (f :@@: x)) (RepK f) x)
        => RepK f x -> f :@@: x
  toK = to . toGhcGenerics

type GenericF t f x = (GenericK f x, x ~ (SplitF t f), t ~ (f :@@: x))
fromF :: forall f t x. GenericF t f x => t -> RepK f x
fromF = fromK @_ @f
toF :: forall f t x. GenericF t f x => RepK f x -> t
toF = toK @_ @f

type GenericN n t f x = (GenericK f x, 'TyEnv f x ~ (SplitN n t), t ~ (f :@@: x))
fromN :: forall n t f x. GenericN n t f x => t -> RepK f x
fromN = fromK @_ @f
toN :: forall n t f x. GenericN n t f x => RepK f x -> t
toN = toK @_ @f

type GenericS t f x = (Split t f x, GenericK f x)
fromS :: forall t f x. GenericS t f x => t -> RepK f x
fromS = fromF @f
toS :: forall t f x. GenericS t f x => RepK f x -> t
toS = toF @f

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

instance {-# OVERLAPPABLE #-} (Conv f f' tys) => Conv (M1 i c f) f' tys where
  toGhcGenerics  x = M1 (toGhcGenerics  x)
  toKindGenerics (M1 x) = toKindGenerics x

instance {-# OVERLAPS #-} (Conv f f' tys) => Conv (M1 i c f) (M1 i c f') tys where
  toGhcGenerics  (M1 x) = M1 (toGhcGenerics  x)
  toKindGenerics (M1 x) = M1 (toKindGenerics x)

instance (k ~ Ty t tys, Conv f f' tys)
         => Conv (k GG.:=>: f) (t :=>: f') tys where
  toGhcGenerics (C x) = SuchThat (toGhcGenerics x)
  toKindGenerics (SuchThat x) = C (toKindGenerics x)

instance (k ~ Ty t tys) => Conv (K1 p k) (F t) tys where
  toGhcGenerics  (F x)  = K1 x
  toKindGenerics (K1 x) = F x