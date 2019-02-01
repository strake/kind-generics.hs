{-# language DataKinds      #-}
{-# language PolyKinds      #-}
{-# language KindSignatures #-}
{-# language TypeOperators  #-}
{-# language RankNTypes     #-}
{-# language TypeFamilies   #-}
{-# language GADTs          #-}
{-# language InstanceSigs   #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language FlexibleContexts      #-}
{-# language AllowAmbiguousTypes   #-}
{-# language ScopedTypeVariables   #-}
{-# language TypeApplications      #-}
{-# language UndecidableInstances  #-}
{-# language ConstraintKinds       #-}
{-# language QuantifiedConstraints #-}
{-# language DefaultSignatures     #-}
module Generics.Kind.InductorSimpleGADTs where

import Generics.Kind
import Generics.Kind.Examples
import Data.Proxy
import GHC.Base (liftA2, Constraint)

instance Foldy Maybe c r (a :&&: LoT0)

class Trivial (a :: k) where
instance Trivial a where

data Vec (n :: Nat) a where
  VNil   ::                   Vec Z     a
  VCons  ::  a -> Vec n a ->  Vec (S n) a

instance GenericK Vec (n :&&: a :&&: LoT0) where
  type RepK Vec  =    (Var VZ :~: Kon Z) :=>: U1
               :+:  Exists Nat (  (Var (VS VZ) :~: (Kon S :@: Var VZ))
                                  :=>:  (    Field (Var (VS (VS VZ)))
                                        :*:  Field (Kon Vec :@: Var VZ :@: Var (VS (VS VZ)))))
  fromK VNil = L1 (SuchThat U1)
  fromK (VCons x xs) = R1 (Exists (SuchThat (Field x :*: Field xs)))
  toK (L1 (SuchThat U1)) = VNil
  toK (R1 (Exists (SuchThat (Field x :*: Field xs)))) = VCons x xs

data Koro n x = Koro { unKoro :: Int }
data Vec' n a = Vec' (Vec n a)
data List n a = List { unList :: [a] }

class (tys ~ (InterpretVar VZ tys :&&: InterpretVar (VS VZ) tys :&&: LoT0)) => TwoArgs tys where
instance TwoArgs (a :&&: b :&&: LoT0) where

instance (forall m. c (m :&&: a :&&: LoT0)) => Foldy Vec c List (n :&&: a :&&: LoT0)

data Algebra (t :: k) (c :: LoT k -> Constraint) (r :: k) where
  Alg :: Proxy x
      -> (forall tys. c tys => Algebra' t x tys)
      -> (forall tys. c tys => x :@@: tys -> r :@@: tys)
      -> Algebra t c r

alg :: forall t c r. (forall tys. c tys => Algebra' t r tys) -> Algebra t c r
alg recf = Alg (Proxy @r) recf id

foldAlgebra :: forall (t :: k) tys r c f.
               (c tys, forall p. Foldy t c p tys)
            => Algebra t c r -> t :@@: tys -> r :@@: tys
foldAlgebra (Alg (Proxy :: Proxy x) v r) x = r @tys (foldG @k @t @c @x @tys v x)

type Algebra' t r = AlgebraB t r (RepK t) (Result r)

newtype Result (r :: k) (tys :: LoT k) where
  Result :: { theResult :: r :@@: tys } -> Result r tys

data Drop (r :: LoT k -> *) (tys :: LoT (d -> k)) where
  Drop :: { unDrop :: r tys } -> Drop r (ty :&&: tys)

idAlgVec :: Algebra Vec TwoArgs Vec'
idAlgVec = alg $ IfImpliesK (Result (Vec' VNil)) :*: ForAllK (IfImpliesK (OneArg (\(Field x) -> OneArg (\(Field (Vec' xs)) -> Drop (Result (Vec' (VCons x xs))) ))))

toListAlg :: TwoArgs tys => Algebra' Vec List tys
toListAlg = IfImpliesK (Result (List [])) :*: ForAllK (IfImpliesK (OneArg (\(Field x) -> OneArg (\(Field (List xs)) -> Drop (Result (List (x : xs))) ))))

vecToList :: Vec n a -> [a]
vecToList v = unList $ foldG @_ @Vec @TwoArgs @_ @(LoT2 _ _) toListAlg v

class Foldy (t :: k) (c :: LoT k -> Constraint) (r :: k) (tys :: LoT k) where
  foldG :: c tys => (forall bop. c bop => Algebra' t r bop) -> t :@@: tys -> r :@@: tys
  default foldG :: (GenericK t tys, FoldB t c r (RepK t) (Result r) tys, c tys)
                => (forall bop. c bop => Algebra' t r bop) -> t :@@: tys -> r :@@: tys
  foldG a x = theResult $ foldB @k @k @t @c @r @(RepK t) @(Result r) @tys a a (fromK @k @t x)

class FoldB (t :: k) (c :: LoT k -> Constraint) (r :: k) 
            (f :: LoT l -> *) (result :: LoT l -> *)
            (tys :: LoT l) where
  type AlgebraB t r f result :: LoT l -> *
  foldB :: (forall bop. c bop => Algebra' t r bop)
        -> AlgebraB t r f result tys -> f tys -> result tys

instance ( FoldB t c r f result tys, FoldB t c r g result tys )
         => FoldB t c r (f :+: g) result tys where
  type AlgebraB t r (f :+: g) result = AlgebraB t r f result :*: AlgebraB t r g result
  foldB recf (fx :*: _) (L1 x) = foldB @_ @_ @t @c @r recf fx x
  foldB recf (_ :*: fy) (R1 y) = foldB @_ @_ @t @c @r recf fy y

newtype (:~>:) (f :: LoT k -> *) (g :: LoT k -> *) (tys :: LoT k) where
  OneArg :: (f tys -> g tys) -> (f :~>: g) tys

newtype ForAllK d (f :: LoT (d -> k) -> *) (tys :: LoT k) where
  ForAllK :: (forall (ty :: d). f (ty :&&: tys)) -> ForAllK d f tys

newtype IfImpliesK (c :: Atom k Constraint) (f :: LoT k -> *) (tys :: LoT k) where
  IfImpliesK :: (Interpret c tys => f tys) -> IfImpliesK c f tys

instance FoldB t c r U1 result tys where
  type AlgebraB t r U1 result = result
  foldB _ r U1 = r

instance ( FoldF t c r x (Igualicos x (ElReemplazador t r x)) tys, FoldB t c r y result tys )
         => FoldB t c r (Field x :*: y) result tys where
  type AlgebraB t r (Field x :*: y) result = Field (ElReemplazador t r x) :~>: AlgebraB t r y result
  foldB recf (OneArg f) (v :*: w)
    = foldB @_ @_ @t @c @r recf
            (f (foldF @_ @_ @t @c @r @x @(Igualicos x (ElReemplazador t r x)) recf v)) w

instance ( FoldF t c r x (Igualicos x (ElReemplazador t r x)) tys )
         => FoldB t c r (Field x) result tys where
  type AlgebraB t r (Field x) result = Field (ElReemplazador t r x) :~>: result
  foldB recf (OneArg f) v
    = f (foldF @_ @_ @t @c @r @x @(Igualicos x (ElReemplazador t r x)) recf v)

instance ( forall ty. FoldB t c r f (Drop result) (ty :&&: tys) )
         => FoldB t c r (Exists k f) result tys where
  type AlgebraB t r (Exists k f) result = ForAllK k (AlgebraB t r f (Drop result))
  foldB recf (ForAllK f) (Exists v)
    = unDrop $ foldB @_ @_ @t @c @r recf f v

instance ( Interpret d tys => FoldB t c r f result tys )
         => FoldB t c r (d :=>: f) result tys where
  type AlgebraB t r (d :=>: f) result = IfImpliesK d (AlgebraB t r f result)
  foldB recf (IfImpliesK f) (SuchThat v)
    = foldB @_ @_ @t @c @r recf f v

class FoldF (t :: k) (c :: LoT k -> Constraint) (r :: k) (x :: Atom l (*))
            (igualicos :: Bool) (tys :: LoT l) where
  foldF :: (forall bop. c bop => Algebra' t r bop)
        -> Field x tys -> Field (ElReemplazador t r x) tys
instance (x ~ ElReemplazador t r x) => FoldF t c r x 'True tys where
  foldF _ x = x

instance ( Foldy t c r (InterpretAll (Args x) tys)
         , Interpret x tys ~ (t :@@: InterpretAll (Args x) tys)
         , Interpret (ElReemplazador t r x) tys ~ (r :@@: (InterpretAll (Args x) tys))
         , c (InterpretAll (Args x) tys) )
         => FoldF t c r x 'False tys where
  foldF recf (Field x) = Field $ foldG @_ @t @c @r @(InterpretAll (Args x) tys) recf x

data Atoms (d :: *) (k :: *) where
  Atom0 :: Atoms d (*)
  AtomA :: Atom d k -> Atoms d ks -> Atoms d (k -> ks)

type family InterpretAll (xs :: Atoms k l) (tys :: LoT k) :: LoT l where
  InterpretAll Atom0 tys = LoT0
  InterpretAll (AtomA a as) tys = Interpret a tys :&&: InterpretAll as tys

type family Args (xs :: Atom d (*)) :: Atoms d l where
  Args (Kon t) = Atom0
  Args (Kon t :@: x) = AtomA x Atom0
  Args (Kon t :@: x :@: y) = AtomA x (AtomA y Atom0)

type family ElReemplazador (t :: l) (r :: l) (a :: Atom d k) :: Atom d k where
  ElReemplazador t r (Kon t) = Kon r
  ElReemplazador t r (Kon k) = Kon k
  ElReemplazador t r (Var v) = Var v
  ElReemplazador t r (f :@: x) = ElReemplazador t r f :@: ElReemplazador t r x
  ElReemplazador t r (c :&: d) = ElReemplazador t r c :&: ElReemplazador t r d
  ElReemplazador t r (ForAll x) = ForAll (ElReemplazador t r x)
  ElReemplazador t r (c :=>>: x) = ElReemplazador t r c :=>>: ElReemplazador t r x

type family Igualicos (a :: k) (b :: k) :: Bool where
  Igualicos a a = 'True
  Igualicos a b = 'False