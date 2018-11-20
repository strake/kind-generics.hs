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
, AllAtoms, AllAtomsB, AllAtomsP
, NS(..), NB(..), NP(..), NA(..)
, RepK, GenericK(..)
, GenericF, fromF, toF
, GenericN, fromN, toN
, GenericS, fromS, toS
) where

import Data.Kind
import Data.PolyKinded hiding (Z, S)
import Data.PolyKinded.Atom
import Data.SOP
import GHC.Generics.Extra hiding ((:=>:))
import qualified GHC.Generics.Extra as GG
import Type.Reflection (Typeable)

-- CODES

type DataType    d = [ Branch d ]
type Constraints d = [ Atom d Constraint ]
type Fields      d = [ Atom d (*) ]

data Branch (d :: k) where
  E      :: Branch (p -> d) -> Branch d
  ERefl  :: Branch (p -> d) -> Branch d
  (:=>:) :: Constraints d -> Fields d -> Branch d

-- CONSTRAINTS

type family AllFields (c :: * -> Constraint) (d :: DataType k) (tys :: LoT k) :: Constraint where
  AllFields c '[] tys = ()
  AllFields c (b ': bs) tys = (AllFieldsB c b tys, AllFields c bs tys)

type family AllFieldsB (c :: * -> Constraint) (d :: Branch k) (tys :: LoT k) :: Constraint where
  -- AllFieldsB c ('E b) tys = AllFieldsBForAll c b tys
  -- AllFieldsB c (cs ':=>: fs) tys = AllFieldsBImplies c cs fs tys
  AllFieldsB c (cs ':=>: fs) tys = AllFieldsP c fs tys

{-
class (forall t. AllFieldsB c b (t ':&&: tys))
      => AllFieldsBForAll (c :: * -> Constraint) (b :: Branch (p -> k)) (tys :: LoT k)
instance (forall t. AllFieldsB c b (t ':&&: tys)) => AllFieldsBForAll c b tys

class (Satisfies cs tys => AllFieldsP c fs tys)
      => AllFieldsBImplies (c :: * -> Constraint) (cs :: Constraints k) (fs :: Fields k) (tys :: LoT k)
instance (Satisfies cs tys => AllFieldsP c fs tys) => AllFieldsBImplies c cs fs tys
-}

type family AllFieldsP (c :: * -> Constraint) (d :: Fields k) (tys :: LoT k) :: Constraint where
  AllFieldsP c '[] tys = ()
  AllFieldsP c (f ': fs) tys = (c (Ty f tys), AllFieldsP c fs tys)

type family AllAtoms (c :: Atom k (*) -> Constraint) (d :: DataType k) :: Constraint where
  AllAtoms c '[] = ()
  AllAtoms c (b ': bs) = (AllAtomsB c b, AllAtoms c bs)

type family AllAtomsB (c :: Atom k (*) -> Constraint) (d :: Branch k) :: Constraint where
  -- Existentials and implications should be as above
  AllAtomsB c (cs ':=>: fs) = AllAtomsP c fs

type family AllAtomsP (c :: Atom k (*) -> Constraint) (d :: Fields k) :: Constraint where
  AllAtomsP c '[] = ()
  AllAtomsP c (f ': fs) = (c f, AllAtomsP c fs)

-- INTERPRETATIONS

data NB (tys :: LoT d) (b :: Branch d) where
  E_ :: NB (t ':&&: tys) c -> NB tys ('E c)
  ERefl_ :: Typeable t => NB (t ':&&: tys) c -> NB tys ('ERefl c)
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

type GenericF t f x = (GenericK f x, x ~ (SplitF t f), t ~ (f :@@: x))
fromF :: forall f t x. GenericF t f x => t -> RepK (CodeK f) x
fromF = fromK @_ @f
toF :: forall f t x. GenericF t f x => RepK (CodeK f) x -> t
toF = toK @_ @f

type GenericN n t f x = (GenericK f x, 'TyEnv f x ~ (SplitN n t), t ~ (f :@@: x))
fromN :: forall n t f x. GenericN n t f x => t -> RepK (CodeK f) x
fromN = fromK @_ @f
toN :: forall n t f x. GenericN n t f x => RepK (CodeK f) x -> t
toN = toK @_ @f

type GenericS t f x = (Split t f x, GenericK f x)
fromS :: forall f t x. GenericS t f x => t -> RepK (CodeK f) x
fromS = fromF @f
toS :: forall f t x. GenericS t f x => RepK (CodeK f) x -> t
toS = toF @f

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