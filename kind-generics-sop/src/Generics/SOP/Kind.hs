{-# language DataKinds             #-}
{-# language GADTs                 #-}
{-# language PolyKinds             #-}
{-# language KindSignatures        #-}
{-# language TypeOperators         #-}
{-# language ConstraintKinds       #-}
{-# language TypeFamilies          #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language FlexibleContexts      #-}
{-# language QuantifiedConstraints #-}
{-# language UndecidableInstances  #-}
{-# language ScopedTypeVariables   #-}
{-# language TypeApplications      #-}
{-# language DefaultSignatures     #-}
{-# language AllowAmbiguousTypes   #-}
module Generics.SOP.Kind (
  module Data.PolyKinded
, module Data.PolyKinded.Atom
, DataType, Branch(..), Constraints, Fields
, AllFields, AllFieldsB, AllFieldsP
, NS(..), NB(..), NP(..), NA(..)
, RepK, GenericK(..)
, GenericS, fromS, toS
, GenericN, fromN, toN
, GenericO, fromO, toO
) where

import Data.Kind
import Data.PolyKinded hiding (Z, S)
import Data.PolyKinded.Atom
import Data.SOP
import GHC.Generics.Extra hiding ((:=>:))
import qualified GHC.Generics.Extra as GG

-- CODES

type DataType    d = [ Branch d ]
type Constraints d = [ Atom d Constraint ]
type Fields      d = [ Atom d (*) ]

data Branch (d :: k) where
  E      :: Branch (p -> d) -> Branch d
  (:=>:) :: Constraints d -> Fields d -> Branch d

class AllFields (c :: * -> Constraint) (d :: DataType k) (tys :: LoT k)
instance AllFields c '[] tys
instance AllFieldsB c b tys => AllFields c (b ': bs) tys

class AllFieldsB (c :: * -> Constraint) (d :: Branch k) (tys :: LoT k)
instance (forall t. AllFieldsB c b (t ':&&: tys)) => AllFieldsB c ('E b) tys
instance (Satisfies cs tys => AllFieldsP c fs tys) => AllFieldsB c (cs ':=>: fs) tys

class AllFieldsP (c :: * -> Constraint) (d :: Fields k) (tys :: LoT k)
instance AllFieldsP c '[] tys
instance (c (Ty f tys), AllFieldsP c fs tys) => AllFieldsP c (f ': fs) tys

-- INTERPRETATIONS

data NB (tys :: LoT d) (b :: Branch d) where
  E_ :: NB (t ':&&: tys) c -> NB tys ('E c)
  C_ :: Ty c tys => NB tys (cs ':=>: fs) -> NB tys ((c ': cs) ':=>: fs)
  F_ :: NP (NA tys) fs -> NB tys ('[] ':=>: fs)

data NA (tys :: LoT d) (f :: Atom d (*)) where
  A_ :: Ty f tys -> NA tys f

type RepK (d :: DataType k) (tys :: LoT k) = NS (NB tys) d

-- THE TYPE CLASS

class GenericK (f :: k) (x :: LoT k) where
  type CodeK f :: DataType k
  
  fromK :: f :@@: x -> RepK (CodeK f) x
  default
    fromK :: (Generic (f :@@: x), ConvSum (Rep (f :@@: x)) (CodeK f) x)
          => f :@@: x -> RepK (CodeK f) x
  fromK = toKindGenericsS . from

  toK   :: RepK (CodeK f) x -> f :@@: x
  default
    toK :: (Generic (f :@@: x), ConvSum (Rep (f :@@: x)) (CodeK f) x)
        => RepK (CodeK f) x -> f :@@: x
  toK = to . toGhcGenericsS

type GenericS t f x = (GenericK f x, x ~ (Split t f), t ~ (f :@@: x))
fromS :: forall f t x. GenericS t f x => t -> RepK (CodeK f) x
fromS = fromK @_ @f
toS :: forall f t x. GenericS t f x => RepK (CodeK f) x -> t
toS = toK @_ @f

type GenericN n t f x = (GenericK f x, 'TyEnv f x ~ (SplitAt n t), t ~ (f :@@: x))
fromN :: forall n t f x. GenericN n t f x => t -> RepK (CodeK f) x
fromN = fromK @_ @f
toN :: forall n t f x. GenericN n t f x => RepK (CodeK f) x -> t
toN = toK @_ @f

type GenericO t f x = (Break t f x, GenericK f x)
fromO :: forall f t x. GenericO t f x => t -> RepK (CodeK f) x
fromO = fromK @_ @f
toO :: forall f t x. GenericO t f x => RepK (CodeK f) x -> t
toO = toK @_ @f

-- CONVERSION

-- Sums

class ConvSum (gg :: * -> *) (kc :: DataType d) (tys :: LoT d) where
  toGhcGenericsS  :: RepK kc tys -> gg a
  toKindGenericsS :: gg a -> RepK kc tys

instance ConvSum f f' tys
         => ConvSum (M1 i c f) f' tys where
  toGhcGenericsS x = M1 (toGhcGenericsS x)
  toKindGenericsS (M1 x) = toKindGenericsS x

instance ConvConstructor (c GG.:=>: f) f' tys
         => ConvSum (c GG.:=>: f) '[ f' ] tys where
  toGhcGenericsS  (Z x) = toGhcGenericsC x
  toGhcGenericsS  (S _) = error "this should never happen!"
  toKindGenericsS x = Z (toKindGenericsC x)

instance ConvConstructor (f :*: gs) f' tys
         => ConvSum (f :*: gs) '[ f' ] tys where
  toGhcGenericsS  (Z x) = toGhcGenericsC x
  toGhcGenericsS  (S _) = error "this should never happen!"
  toKindGenericsS x = Z (toKindGenericsC x)

instance ConvConstructor U1 f' tys
         => ConvSum U1 '[ f' ] tys where
  toGhcGenericsS  (Z x) = toGhcGenericsC x
  toGhcGenericsS  (S _) = error "this should never happen!"
  toKindGenericsS x = Z (toKindGenericsC x)

instance ConvConstructor (K1 i k) f' tys
         => ConvSum (K1 i k) '[ f' ] tys where
  toGhcGenericsS  (Z x) = toGhcGenericsC x
  toGhcGenericsS  (S _) = error "this should never happen!"
  toKindGenericsS x = Z (toKindGenericsC x)

instance (ConvConstructor f f' tys, ConvSum gs gs' tys)
         => ConvSum (f :+: gs) (f' ': gs') tys where
  toGhcGenericsS  (Z x) = L1 (toGhcGenericsC x)
  toGhcGenericsS  (S x) = R1 (toGhcGenericsS x)
  toKindGenericsS (L1 x) = Z (toKindGenericsC x)
  toKindGenericsS (R1 x) = S (toKindGenericsS x)

-- Constructors

class ConvConstructor (gg :: * -> *) (kb :: Branch d) (tys :: LoT d) where
  toGhcGenericsC  :: NB tys kb -> gg a
  toKindGenericsC :: gg a -> NB tys kb

instance ConvConstructor f f' tys
         => ConvConstructor (M1 i c f) f' tys where
  toGhcGenericsC x = M1 (toGhcGenericsC x)
  toKindGenericsC (M1 x) = toKindGenericsC x

instance ConvProduct U1 f' tys
         => ConvConstructor U1 ('[] ':=>: f') tys where
  toGhcGenericsC  (F_ x) = toGhcGenericsP x
  toKindGenericsC x = F_ (toKindGenericsP x)

instance ConvProduct (K1 i k) f' tys
         => ConvConstructor (K1 i k) ('[] ':=>: f') tys where
  toGhcGenericsC  (F_ x) = toGhcGenericsP x
  toKindGenericsC x = F_ (toKindGenericsP x)

instance ConvProduct (f :*: gs) f' tys
         => ConvConstructor (f :*: gs) ('[] ':=>: f') tys where
  toGhcGenericsC  (F_ x) = toGhcGenericsP x
  toKindGenericsC x = F_ (toKindGenericsP x)

instance (c ~ (Ty c' tys), ConvConstructor f (cs ':=>: f') tys)
         => ConvConstructor (c GG.:=>: f) ((c' ': cs) ':=>: f') tys where
  toGhcGenericsC  (C_ x) = SuchThat (toGhcGenericsC x)
  toKindGenericsC (SuchThat x) = C_ (toKindGenericsC x)

-- Products

class ConvProduct (gg :: * -> *) (kp :: Fields d) (tys :: LoT d) where
  toGhcGenericsP  :: NP (NA tys) kp -> gg a
  toKindGenericsP :: gg a -> NP (NA tys) kp

instance ConvProduct f f' tys
         => ConvProduct (M1 i c f) f' tys where
  toGhcGenericsP x = M1 (toGhcGenericsP x)
  toKindGenericsP (M1 x) = toKindGenericsP x

instance ConvProduct U1 '[] tys where
  toGhcGenericsP  Nil = U1
  toKindGenericsP U1  = Nil

instance ConvAtom (K1 i k) f' tys
         => ConvProduct (K1 i k) '[ f' ] tys where
  toGhcGenericsP  (x :* Nil) = toGhcGenericsA x
  toKindGenericsP x = toKindGenericsA x :* Nil

instance (ConvAtom f f' tys, ConvProduct gs gs' tys)
         => ConvProduct (f :*: gs) (f' ': gs') tys where
  toGhcGenericsP  (x :*  y) = toGhcGenericsA  x :*: toGhcGenericsP  y
  toKindGenericsP (x :*: y) = toKindGenericsA x :*  toKindGenericsP y

-- Atoms

class ConvAtom (gg :: * -> *) (ka :: Atom d (*)) (tys :: LoT d) where
  toGhcGenericsA  :: NA tys ka -> gg a
  toKindGenericsA :: gg a -> NA tys ka

instance (k ~ (Ty t tys)) => ConvAtom (K1 i k) t tys where
  toGhcGenericsA  (A_ x) = K1 x
  toKindGenericsA (K1 x) = A_ x

instance ConvAtom f f' tys => ConvAtom (M1 i p f) f' tys where
  toGhcGenericsA x = M1 (toGhcGenericsA x)
  toKindGenericsA (M1 x) = toKindGenericsA x