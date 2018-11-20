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
-- | Main module of @kind-generics@. Please refer to the @README@ file for documentation on how to use this package.
module Generics.Kind (
  module Data.PolyKinded
, module Data.PolyKinded.Atom
  -- * Generic representation types
, (:+:)(..), (:*:)(..), U1(..), M1(..)
, F(..), (:=>:)(..), E(..), ERefl(..)
  -- * Generic type classes
, GenericK(..)
, GenericF, fromF, toF
, GenericN, fromN, toN
, GenericS, fromS, toS
  -- * Bridging with "GHC.Generics"
, Conv(..)
) where

import Data.PolyKinded
import Data.PolyKinded.Atom
import Data.Kind
import GHC.Generics.Extra hiding ((:=>:))
import qualified GHC.Generics.Extra as GG
import Type.Reflection

-- | Fields: used to represent each of the (visible) arguments to a constructor.
-- Replaces the 'K1' type from "GHC.Generics". The type of the field is
-- represented by an 'Atom' from "Data.PolyKinded.Atom".
--
-- > instance GenericK [] (a :&&: LoT0) where
-- >   type RepK [] = F V0 :*: F ([] :$: V0)
newtype F (t :: Atom d (*)) (x :: LoT d) = F { unF :: Ty t x }
deriving instance Show (Ty t x) => Show (F t x)

-- | Constraints: used to represent constraints in a constructor.
-- Replaces the '(:=>:)' type from "GHC.Generics.Extra".
--
-- > data Showable a = Show a => a -> X a
-- >
-- > instance GenericK Showable (a :&&: LoT0) where
-- >   type RepK Showable = (Show :$: a) :=>: (F V0)
data (:=>:) (c :: Atom d Constraint) (f :: LoT d -> *) (x :: LoT d) where
  C :: Ty c x => f x -> (c :=>: f) x

-- | Existentials: a representation of the form @E f@ describes
-- a constructor whose inner type is represented by @f@, and where
-- the type variable at index 0, @V0@, is existentially quantified.
--
-- > data Exists where
-- >  E :: t -> Exists
-- >
-- > instance GenericK Exists LoT0 where
-- >   type RepK Exists = E (F V0)
data E (f :: LoT (k -> d) -> *) (x :: LoT d) where
  E :: forall (t :: k) d (f :: LoT (k -> d) -> *) (x :: LoT d)
     . f (t ':&&: x) -> E f x

-- | Existentials with reflection: similar to 'E',
--   but in addition we remember the type of the existential variable.
--
-- > data Exists where
-- >  E :: Typeable t => t -> Exists
-- >
-- > instance GenericK Exists LoT0 where
-- >   type RepK Exists = ERefl (F V0)
data ERefl (f :: LoT (k -> d) -> *) (x :: LoT d) where
  ERefl :: forall (t :: k) d (f :: LoT (k -> d) -> *) (x :: LoT d)
         . Typeable t => f (t ':&&: x) -> ERefl f x

-- THE TYPE CLASS

-- | Representable types of any kind. The definition of an instance must
-- mention the type constructor along with a list of types of the corresponding
-- length. For example:
--
-- > instance GenericK Int    LoT0
-- > instance GenericK []     (a :&&: LoT0)
-- > instance GenericK Either (a :&&: b :&&: LoT0)
class GenericK (f :: k) (x :: LoT k) where
  type RepK f :: LoT k -> *
  
  -- | Convert the data type to its representation.
  fromK :: f :@@: x -> RepK f x
  default
    fromK :: (Generic (f :@@: x), Conv (Rep (f :@@: x)) (RepK f) x)
          => f :@@: x -> RepK f x
  fromK = toKindGenerics . from

  -- | Convert from a representation to its corresponding data type.
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

-- | @GenericS t f x@ states that the ground type @t@ is split by
-- default as the constructor @f@ and a list of types @x$, and that
-- a 'GenericK' instance exists for that constructor.
--
-- This constraint provides an external interface similar to that
-- provided by 'Generic' in "GHC.Generics".
type GenericS t f x = (Split t f x, GenericK f x)
fromS :: forall t f x. GenericS t f x => t -> RepK f x
fromS = fromF @f
toS :: forall t f x. GenericS t f x => RepK f x -> t
toS = toF @f

-- CONVERSION BETWEEN GHC.GENERICS AND KIND-GENERICS

-- | Bridges a representation of a data type using the combinators
-- in "GHC.Generics" with a representation using this module.
-- You are never expected to manipulate this type class directly,
-- it is part of the deriving mechanism for 'GenericK'.
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