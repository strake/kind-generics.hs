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

instance (forall m. c (m :&&: a :&&: LoT0)) => Foldy Vec c r (n :&&: a :&&: LoT0)

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

type Algebra' t r = AlgebraB t r (RepK t) Z

newtype Result (r :: k) (drop :: Nat) (tys :: LoT l) where
  Result :: { theResult :: r :@@: (Drop drop tys) } -> Result r drop tys

type family Drop (drop :: Nat) (tys :: LoT l) :: LoT k where
  Drop Z tys = tys
  Drop (S n)(ty :&&: tys) = Drop n tys

{-
data Drop (r :: LoT k -> *) (tys :: LoT (d -> k)) where
  Drop :: { unDrop :: r tys } -> Drop r (ty :&&: tys)
-}

idAlgVec :: Algebra Vec TwoArgs Vec
idAlgVec = alg $ IfImpliesK (Result VNil) :*: ForAllK (IfImpliesK (OneArg (\(Field x) -> OneArg (\(Field xs) -> Result (VCons x xs) ))))

toListAlg :: Algebra Vec TwoArgs List
toListAlg = alg $ IfImpliesK (Result (List [])) :*: ForAllK (IfImpliesK (OneArg (\(Field x) -> OneArg (\(Field (List xs)) -> Result (List (x : xs)) ))))

vecToList :: Vec n a -> [a]
vecToList v = unList $ foldAlgebra @_ @Vec @(LoT2 _ _) toListAlg v

class Foldy (t :: k) (c :: LoT k -> Constraint) (r :: k) (tys :: LoT k) where
  foldG :: c tys => (forall bop. c bop => Algebra' t r bop) -> t :@@: tys -> r :@@: tys
  default foldG :: (GenericK t tys, FoldB t c r (RepK t) Z tys, c tys)
                => (forall bop. c bop => Algebra' t r bop) -> t :@@: tys -> r :@@: tys
  foldG a x = theResult $ foldB @k @k @t @c @r @(RepK t) @Z @tys a a (fromK @k @t x)

class FoldB (t :: k) (c :: LoT k -> Constraint) (r :: k) 
            (f :: LoT l -> *) (drop :: Nat)
            (tys :: LoT l) where
  type AlgebraB t r f drop :: LoT l -> *
  foldB :: (forall bop. c bop => Algebra' t r bop)
        -> AlgebraB t r f drop tys -> f tys -> Result r drop tys

instance ( FoldB t c r f drop tys, FoldB t c r g drop tys )
         => FoldB t c r (f :+: g) drop tys where
  type AlgebraB t r (f :+: g) drop = AlgebraB t r f drop :*: AlgebraB t r g drop
  foldB recf (fx :*: _) (L1 x) = foldB @_ @_ @t @c @r recf fx x
  foldB recf (_ :*: fy) (R1 y) = foldB @_ @_ @t @c @r recf fy y

newtype (:~>:) (f :: LoT k -> *) (g :: LoT k -> *) (tys :: LoT k) where
  OneArg :: (f tys -> g tys) -> (f :~>: g) tys

newtype ForAllK d (f :: LoT (d -> k) -> *) (tys :: LoT k) where
  ForAllK :: (forall (ty :: d). f (ty :&&: tys)) -> ForAllK d f tys

newtype IfImpliesK (c :: Atom k Constraint) (f :: LoT k -> *) (tys :: LoT k) where
  IfImpliesK :: (Interpret c tys => f tys) -> IfImpliesK c f tys

instance FoldB t c r U1 drop tys where
  type AlgebraB t r U1 drop = Result r drop
  foldB _ r U1 = r

instance ( FoldF t c r x (ElEncontrador t x) tys, FoldB t c r y drop tys )
         => FoldB t c r (Field x :*: y) drop tys where
  type AlgebraB t r (Field x :*: y) drop = Field (ElReemplazador t r x) :~>: AlgebraB t r y drop
  foldB recf (OneArg f) (v :*: w)
    = foldB @_ @_ @t @c @r recf
            (f (foldF @_ @_ @t @c @r @x @(ElEncontrador t x) recf v)) w

instance ( FoldF t c r x (ElEncontrador t x) tys )
         => FoldB t c r (Field x) drop tys where
  type AlgebraB t r (Field x) drop = Field (ElReemplazador t r x) :~>: Result r drop
  foldB recf (OneArg f) v
    = f (foldF @_ @_ @t @c @r @x @(ElEncontrador t x) recf v)

instance ( forall ty. FoldB t c r f (S drop) (ty :&&: tys) )
         => FoldB t c r (Exists k f) drop tys where
  type AlgebraB t r (Exists k f) drop = ForAllK k (AlgebraB t r f (S drop))
  foldB recf (ForAllK f) (Exists v)
    = Result @r @drop @tys $ theResult $ foldB @_ @_ @t @c @r @f @(S drop) recf f v

instance ( Interpret d tys => FoldB t c r f drop tys )
         => FoldB t c r (d :=>: f) drop tys where
  type AlgebraB t r (d :=>: f) drop = IfImpliesK d (AlgebraB t r f drop)
  foldB recf (IfImpliesK f) (SuchThat v)
    = foldB @_ @_ @t @c @r recf f v

class FoldF (t :: k) (c :: LoT k -> Constraint) (r :: k) (x :: Atom l (*))
            (ande :: WhereIsIt) (tys :: LoT l) where
  foldF :: (forall bop. c bop => Algebra' t r bop)
        -> Field x tys -> Field (ElReemplazador t r x) tys
instance (x ~ ElReemplazador t r x) => FoldF t c r x 'NotFound tys where
  foldF _ x = x

instance ( Foldy t c r (InterpretAll (Args x) tys)
         , Interpret x tys ~ (t :@@: InterpretAll (Args x) tys)
         , Interpret (ElReemplazador t r x) tys ~ (r :@@: (InterpretAll (Args x) tys))
         , c (InterpretAll (Args x) tys) )
         => FoldF t c r x 'TopLevel tys where
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

{-
type family Igualicos (a :: k) (b :: k) :: Bool where
  Igualicos a a = 'True
  Igualicos a b = 'False
-}

data WhereIsIt = NotFound | TopLevel | SomewhereElse

type family ElEncontrador (t :: l) (a :: Atom d k) :: WhereIsIt where
  ElEncontrador t (Kon t)   = TopLevel
  ElEncontrador t (f :@: x) = MergeApp (ElEncontrador t f) (ElEncontrador t x)
  ElEncontrador t x = NotFound

type family MergeApp (fw :: WhereIsIt) (xw :: WhereIsIt) :: WhereIsIt where
  MergeApp TopLevel anything  = TopLevel
  MergeApp NotFound NotFound  = NotFound
  MergeApp some1    some2     = SomewhereElse