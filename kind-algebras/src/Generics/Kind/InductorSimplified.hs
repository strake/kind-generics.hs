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
{-# language UndecidableSuperClasses #-}
{-# language DefaultSignatures #-}
{-# language PatternSynonyms #-}
module Generics.Kind.InductorSimplified where

import Generics.Kind
import Generics.Kind.Examples
import Data.Proxy
import GHC.Base (liftA2, Constraint)

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

idAlgVec :: Algebra Vec TwoArgs Vec
idAlgVec = alg (When VNil, algForAll (When VCons))

toListAlg :: Algebra Vec TwoArgs List
toListAlg = alg (When (List []), algForAll (When $ \x (List xs) -> List (x:xs)))

vecToList :: Vec n a -> [a]
vecToList v = unList $ foldAlgebra @_ @Vec @(LoT2 _ _) toListAlg v

type AlgebraF t c r = forall bop. (c bop => Proxy bop -> AlgebraB t r (RepK t) Z bop)
type FoldK t c r tys = (GenericK t tys, FoldB t c r (RepK t) Z tys)

data Algebra (t :: k) (c :: LoT k -> Constraint) (r :: k) where
  Alg :: Proxy x
      -> AlgebraF t c x
      -> (forall tys. c tys => Proxy tys -> x :@@: tys -> r :@@: tys)
      -> Algebra t c r

alg :: forall t c r. (forall bop. (c bop => AlgebraB t r (RepK t) Z bop)) -> Algebra t c r
alg recf = Alg (Proxy :: Proxy r) (\(p :: Proxy tys) -> recf @tys) (\_ -> id)

upgrade :: (forall tys. d tys => c tys) => Algebra t c r -> Algebra t d r
upgrade (Alg px alg r) = Alg px alg r

foldAlgebra :: forall (t :: k) tys r c f.
               (c tys, forall p. Foldy t c p tys)
            => Algebra t c r -> t :@@: tys -> r :@@: tys
foldAlgebra (Alg (Proxy :: Proxy x) v r) x = r (Proxy :: Proxy tys) (foldG @k @t @c @x @tys v x)

class Foldy (t :: k) (c :: LoT k -> Constraint) (r :: k) (tys :: LoT k) where
  foldG :: c tys => (AlgebraF t c r) -> t :@@: tys -> r :@@: tys
  default foldG :: (GenericK t tys, FoldB t c r (RepK t) Z tys, c tys)
                => (AlgebraF t c r) -> t :@@: tys -> r :@@: tys
  foldG a x = foldB @_ @_ @t @c @r @(RepK t) @Z @tys a (a (Proxy :: Proxy tys)) (fromK @k @t x)

-- In the simple recursor, f has kind LoT k -> * (same as t)

type family Drop (drop :: Nat) (tys :: LoT l) :: LoT k where
  Drop Z tys = tys
  Drop (S n)(ty :&&: tys) = Drop n tys

class FoldB (t :: k) (c :: LoT k -> Constraint) (r :: k)
            (f :: LoT l -> *) (drop :: Nat) (tys :: LoT l) where
  type AlgebraB t r f drop tys :: *
  foldB :: (AlgebraF t c r)
        -> AlgebraB t r f drop tys -> f tys -> r :@@: (Drop drop tys)

type a :**: b = (a, b)
pattern a :**: b = (a, b)

instance ( FoldB t c r f drop tys, FoldB t c r g drop tys )
         => FoldB t c r (f :+: g) drop tys where
  type AlgebraB t r (f :+: g) drop tys = AlgebraB t r f drop tys :**: AlgebraB t r g drop tys
  foldB recf (fx :**: _) (L1 x) = foldB @_ @_ @t @c @r @f @drop @tys recf fx x
  foldB recf (_ :**: fy) (R1 y) = foldB @_ @_ @t @c @r @g @drop @tys recf fy y

instance FoldB t c r U1 drop tys where
  type AlgebraB t r U1 drop tys = r :@@: (Drop drop tys)
  foldB _ r U1 = r

instance ( FoldF t c r x (ElEncontrador t x) tys, FoldB t c r y drop tys )
         => FoldB t c r (Field x :*: y) drop tys where
  type AlgebraB t r (Field x :*: y) drop tys = AlgebraField t r x (ElEncontrador t x) tys -> AlgebraB t r y drop tys
  foldB recf f (Field v :*: w)
    = foldB @_ @_ @t @c @r @y @drop @tys recf
            (f (foldF @_ @_ @t @c @r @x @(ElEncontrador t x) @tys recf v)) w

instance ( FoldF t c r x (ElEncontrador t x) tys )
         => FoldB t c r (Field x) drop tys where
  type AlgebraB t r (Field x) drop tys = AlgebraField t r x (ElEncontrador t x) tys -> r :@@: (Drop drop tys)
  foldB recf f (Field v)
    = f (foldF @_ @_ @t @c @r @x @(ElEncontrador t x) @tys recf v)


newtype AlgForAll d (t :: k) (r :: k) (f :: LoT (d -> l) -> *) (drop :: Nat) (tys :: LoT l) where
  AlgForAll :: (forall (ty :: d). Proxy ty -> AlgebraB t r f (S drop) (ty :&&: tys)) -> AlgForAll d t r f drop tys

algForAll :: (forall (ty :: k). AlgebraB t r f (S drop) (ty :&&: tys)) -> AlgForAll k t r f drop tys
algForAll f = AlgForAll (\(p :: Proxy ty) -> f @ty)

newtype When (t :: k) (r :: k) (c :: Atom l Constraint) (f :: LoT l -> *) (drop :: Nat) (tys :: LoT l) where
  When :: (Interpret c tys => AlgebraB t r f drop tys) -> When t r c f drop tys

instance ( forall ty. FoldB t c r f (S drop) (ty :&&: tys) )
         => FoldB t c r (Exists k f) drop tys where
  type AlgebraB t r (Exists k f) drop tys = AlgForAll k t r f drop tys
  foldB recf (AlgForAll f) (Exists (v :: f (ty :&&: tys)))
    = foldB @_ @_ @t @c @r @f @(S drop) recf (f (Proxy :: Proxy ty)) v

instance ( Interpret d tys => FoldB t c r f drop tys )
         => FoldB t c r (d :=>: f) drop tys where
  type AlgebraB t r (d :=>: f) drop tys = When t r d f drop tys
  foldB recf (When f) (SuchThat v)
    = foldB @_ @_ @t @c @r @f @drop @tys recf f v

class FoldF (t :: k) (c :: LoT k -> Constraint) (r :: k)
            (x :: Atom l (*)) (loc :: WhereIsIt) (tys :: LoT l) where
  type AlgebraField t r x loc tys :: *
  foldF :: AlgebraF t c r
        -> Interpret x tys -> AlgebraField t r x loc tys

instance FoldF t c r x 'NotFound tys where
  type AlgebraField t r x 'NotFound tys = Interpret x tys
  foldF _ x = x

instance ( p ~ InterpretAll (Args x) tys
         , Interpret x tys ~ (t :@@: p)
         , Foldy t c r p
         , c p )
         => FoldF t c r x 'TopLevel tys where
  type AlgebraField t r x 'TopLevel tys = r :@@: (InterpretAll (Args x) tys)
  foldF recf x = foldG @_ @t @c @r @(InterpretAll (Args x) tys) recf x

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

data WhereIsIt = NotFound | TopLevel | SomewhereElse

type family ElEncontrador (t :: l) (a :: Atom d k) :: WhereIsIt where
  ElEncontrador t (Kon t)   = TopLevel
  ElEncontrador t (f :@: x) = MergeApp (ElEncontrador t f) (ElEncontrador t x)
  ElEncontrador t x = NotFound

type family MergeApp (fw :: WhereIsIt) (xw :: WhereIsIt) :: WhereIsIt where
  MergeApp TopLevel anything  = TopLevel
  MergeApp NotFound NotFound  = NotFound
  MergeApp some1    some2     = SomewhereElse