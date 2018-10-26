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
module Generics.SOP.Kind where

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
  type RepK f :: DataType k
  
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

-- CONVERSION

-- Sums

class ConvSum (gg :: * -> *) (kc :: DataType d) (tys :: LoT d) where
  toGhcGenericsS  :: RepK kc tys -> gg a
  toKindGenericsS :: gg a -> RepK kc tys

instance {-# OVERLAPPABLE #-} ConvConstructor f f' tys
         => ConvSum f '[ f' ] tys where
  toGhcGenericsS  (Z x) = toGhcGenericsC x
  toGhcGenericsS  (S _) = error "this should never happen!"
  toKindGenericsS x = Z (toKindGenericsC x)

instance {-# OVERLAPS #-} (ConvConstructor f f' tys, ConvSum gs gs' tys)
         => ConvSum (f :+: gs) (f' ': gs') tys where
  toGhcGenericsS  (Z x) = L1 (toGhcGenericsC x)
  toGhcGenericsS  (S x) = R1 (toGhcGenericsS x)
  toKindGenericsS (L1 x) = Z (toKindGenericsC x)
  toKindGenericsS (R1 x) = S (toKindGenericsS x)

-- Constructors

class ConvConstructor (gg :: * -> *) (kb :: Branch d) (tys :: LoT d) where
  toGhcGenericsC  :: NB tys kb -> gg a
  toKindGenericsC :: gg a -> NB tys kb

instance {-# OVERLAPPABLE #-} ConvProduct f f' tys
         => ConvConstructor f ('[] ':=>: f') tys where
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

instance ConvProduct U1 '[] tys where
  toGhcGenericsP  Nil = U1
  toKindGenericsP U1  = Nil

instance (k ~ Ty f' tys, ConvProduct gs gs' tys)
         => ConvProduct ((K1 p k) :*: gs) (f' ': gs') tys where
  toGhcGenericsP  (A_ x :*  y) = K1 x :*: toGhcGenericsP  y
  toKindGenericsP (K1 x :*: y) = A_ x :*  toKindGenericsP y