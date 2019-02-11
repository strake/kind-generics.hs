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
module Generics.Kind.RecursorConstraintsSimplified where

import Generics.Kind
import Generics.Kind.Examples
import Data.Proxy
import GHC.Base (liftA2, Constraint)

class Trivial (a :: k) where
instance Trivial a where

class (InterpretVar v tys ~ a) => (v :==: a) tys where
instance (InterpretVar v tys ~ a) => (v :==: a) tys where

class (tys ~ (InterpretVar VZ tys :&&: LoT0)) => OneArg tys where
instance OneArg (a :&&: LoT0) where

class (tys ~ (InterpretVar VZ tys :&&: InterpretVar (VS VZ) tys :&&: LoT0)) => TwoArgs tys where
instance TwoArgs (a :&&: b :&&: LoT0) where

instance Foldy Maybe c r (a :&&: LoT0)
instance Foldy Tree c r (a :&&: LoT0)

lengthAlg :: forall a. Num a => Algebra Maybe OneArg a
lengthAlg = alg $ 0 :**: \_ -> 1

{-
lengthAlg2 :: Algebra Maybe Trivial Integer
lengthAlg2 = Alg (Proxy @Integer) (Field 0  :*: OneArg (\_ -> Field 1)) id
-}

applyLength = foldAlgebra @_ @Maybe @(Int :&&: LoT0) lengthAlg (Just 2)

maybeAlg :: Algebra Maybe Trivial Bool
maybeAlg = alg $ False :**: \_ -> True

notMaybeAlg :: Algebra Maybe Trivial Bool
notMaybeAlg = not <$> maybeAlg

sumAlg :: forall a. Num a => Algebra Maybe ((~) (a :&&: LoT0)) a
sumAlg = alg $ 0 :**: \n -> n

avgAlg :: Fractional a => Algebra Maybe ((~) (a :&&: LoT0)) a
avgAlg = (/) <$> sumAlg <*> upgrade (fromInteger <$> lengthAlg)

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

instance (forall n. c (n :&&: b :&&: LoT0)) => Foldy Vec c r (a :&&: b :&&: LoT0) where

lengthAlgVec :: Algebra Vec Trivial Integer
lengthAlgVec = alg $ (When 1) :**: (algForAll $ When $ \_ n -> n + 1)

twiceLengthAlgVec :: Algebra Vec Trivial Integer
twiceLengthAlgVec = (+) <$> lengthAlgVec <*> lengthAlgVec

sumAlgVec :: Num a => Algebra Vec (VS VZ :==: a) a
sumAlgVec = alg $ (When 0) :**: (algForAll $ When $ \x n -> x + n)

applySumAlgVec :: Float
applySumAlgVec = foldAlgebra @_ @Vec @(LoT2 (S (S Z)) Float) avgAlgVec ((VCons 1 (VCons 2 VNil)) :: Vec (S (S Z)) Float)

avgAlgVec :: Fractional a => Algebra Vec (VS VZ :==: a) a
avgAlgVec = (/) <$> sumAlgVec <*> upgrade (fromInteger <$> lengthAlgVec)

type AlgebraF t c r = forall bop. (c bop => Proxy bop -> AlgebraB t r (RepK t) bop)
type FoldK t c r tys = (GenericK t tys, FoldB t c r (RepK t) tys)

data Algebra (t :: k) (c :: LoT k -> Constraint) (r :: *) where
  Alg :: Proxy x
      -> AlgebraF t c x
      -> (x -> r)
      -> Algebra t c r

alg :: (forall bop. (c bop => AlgebraB t r (RepK t) bop)) -> Algebra t c r
alg recf = Alg Proxy (\(p :: Proxy tys) -> recf @tys) id

upgrade :: (forall tys. d tys => c tys) => Algebra t c r -> Algebra t d r
upgrade (Alg px alg r) = Alg px alg r

foldAlgebra :: forall (t :: k) tys r c f.
               (c tys, forall p. Foldy t c p tys)
            => Algebra t c r -> t :@@: tys -> r
foldAlgebra (Alg (Proxy :: Proxy x) v r) x = r (foldG @k @t @c @x @tys v x)

class Foldy (t :: k) (c :: LoT k -> Constraint) (r :: *) (tys :: LoT k) where
  foldG :: c tys => (AlgebraF t c r) -> t :@@: tys -> r
  default foldG :: (GenericK t tys, FoldB t c r (RepK t) tys, c tys)
                => (AlgebraF t c r) -> t :@@: tys -> r
  foldG a x = foldB @_ @_ @t @c @r @(RepK t) @tys a (a (Proxy :: Proxy tys)) (fromK @k @t x)

-- In the simple recursor, f has kind LoT k -> * (same as t)

class FoldB (t :: k) (c :: LoT k -> Constraint) (r :: *)
            (f :: LoT l -> *) (tys :: LoT l) where
  type AlgebraB t r f tys :: *
  foldB :: (AlgebraF t c r)
        -> AlgebraB t r f tys -> f tys -> r
class UnitB (t :: k) (f :: LoT l -> *) (tys :: LoT l) where
  unitB :: AlgebraB t () f tys
class UnitB t f tys
      => TupleB (t :: k) (r :: *) (s :: *) 
                (f :: LoT l -> *) (tys :: LoT l) where
  tupleB :: AlgebraB t r f tys
         -> AlgebraB t s f tys
         -> AlgebraB t (r, s) f tys

type a :**: b = (a, b)
pattern a :**: b = (a, b)

instance ( FoldB t c r f tys, FoldB t c r g tys )
         => FoldB t c r (f :+: g) tys where
  type AlgebraB t r (f :+: g) tys = AlgebraB t r f tys :**: AlgebraB t r g tys
  foldB recf (fx :**: _) (L1 x) = foldB @_ @_ @t @c @r @f @tys recf fx x
  foldB recf (_ :**: fy) (R1 y) = foldB @_ @_ @t @c @r @g @tys recf fy y
instance ( UnitB t f tys, UnitB t g tys )
         => UnitB t (f :+: g) tys where
  unitB = unitB @_ @_ @t @f @tys :**: unitB @_ @_ @t @g @tys
instance ( TupleB t r s f tys, TupleB t r s g tys )
         => TupleB t r s (f :+: g) tys where
  tupleB (x :**: y) (a :**: b)
    = tupleB @_ @_ @t @r @s @f @tys x a :**: tupleB @_ @_ @t @r @s @g @tys y b 

newtype (:~>:) (f :: LoT k -> *) (g :: LoT k -> *) (tys :: LoT k) where
  OneArg :: (f tys -> g tys) -> (f :~>: g) tys

newtype ForAllK d (f :: LoT (d -> k) -> *) (tys :: LoT k) where
  ForAllK :: (forall (ty :: d). f (ty :&&: tys)) -> ForAllK d f tys

newtype IfImpliesK (c :: Atom k Constraint) (f :: LoT k -> *) (tys :: LoT k) where
  IfImpliesK :: (Interpret c tys => f tys) -> IfImpliesK c f tys

instance FoldB t c r U1 tys where
  type AlgebraB t r U1 tys = r
  foldB _ r U1 = r
instance UnitB t U1 tys where
  unitB = ()
instance TupleB t r s U1 tys where
  tupleB x a = (x, a)

instance ( FoldF t c r x (ElEncontrador t x) tys, FoldB t c r y tys )
         => FoldB t c r (Field x :*: y) tys where
  type AlgebraB t r (Field x :*: y) tys = AlgebraField t r x (ElEncontrador t x) tys -> AlgebraB t r y tys
  foldB recf f (Field v :*: w)
    = foldB @_ @_ @t @c @r @y @tys recf
            (f (foldF @_ @_ @t @c @r @x @(ElEncontrador t x) @tys recf v)) w
instance ( UnitB t y tys )
         => UnitB t (Field x :*: y) tys where
  unitB = \_ -> unitB @_ @_ @t @y @tys
instance ( TupleB t r s y tys
         , UntupleF t x r s (ElEncontrador t x) tys )
         => TupleB t r s (Field x :*: y) tys where
  tupleB x a
    = \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x @r @s 
                         @(ElEncontrador t x) @tys
                         v
        in tupleB @_ @_ @t @r @s @y @tys (x vx) (a va)

instance ( FoldF t c r x (ElEncontrador t x) tys )
         => FoldB t c r (Field x) tys where
  type AlgebraB t r (Field x) tys = AlgebraField t r x (ElEncontrador t x) tys -> r
  foldB recf f (Field v)
    = f (foldF @_ @_ @t @c @r @x @(ElEncontrador t x) @tys recf v)
instance UnitB t (Field x) tys where
  unitB = \_ -> ()
instance UntupleF t x r s (ElEncontrador t x) tys
         => TupleB t r s (Field x) tys where
  tupleB x a
    = \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x @r @s
                         @(ElEncontrador t x) @tys
                         v
        in (x vx, a va)


newtype AlgForAll d (t :: k) (r :: *) (f :: LoT (d -> l) -> *) (tys :: LoT l) where
  AlgForAll :: (forall (ty :: d). Proxy ty -> AlgebraB t r f (ty :&&: tys)) -> AlgForAll d t r f tys

algForAll :: (forall (ty :: k). AlgebraB t r f (ty :&&: tys)) -> AlgForAll k t r f tys
algForAll f = AlgForAll (\(p :: Proxy ty) -> f @ty)

newtype When (t :: k) (r :: *) (c :: Atom l Constraint) (f :: LoT l -> *) (tys :: LoT l) where
  When :: (Interpret c tys => AlgebraB t r f tys) -> When t r c f tys

instance ( forall ty. FoldB t c r f (ty :&&: tys) )
         => FoldB t c r (Exists k f) tys where
  type AlgebraB t r (Exists k f) tys = AlgForAll k t r f tys
  foldB recf (AlgForAll f) (Exists (v :: f (ty :&&: tys)))
    = foldB @_ @_ @t @c recf (f (Proxy :: Proxy ty)) v
instance ( forall ty. UnitB t f (ty :&&: tys) )
         => UnitB t (Exists k f) tys where
  unitB = AlgForAll $ \(p :: Proxy ty) -> unitB @_ @_ @t @f @(ty :&&: tys)
instance ( forall ty. TupleB t r s f (ty :&&: tys) )
         => TupleB t r s (Exists k f) tys where
  tupleB (AlgForAll x) (AlgForAll a)
    = AlgForAll $ \(p :: Proxy ty) -> tupleB @_ @_ @t @r @s @f @(ty :&&: tys) (x p) (a p)

instance ( Interpret d tys => FoldB t c r f tys )
         => FoldB t c r (d :=>: f) tys where
  type AlgebraB t r (d :=>: f) tys = When t r d f tys
  foldB recf (When f) (SuchThat v)
    = foldB @_ @_ @t @c recf f v
instance ( Interpret c tys => UnitB t f tys )
         => UnitB t (c :=>: f) tys where
  unitB = When (unitB @_ @_ @t @f @tys)
instance ( Interpret c tys => TupleB t r s f tys )
         => TupleB t r s (c :=>: f) tys where
  tupleB (When x) (When a)
    = When $ tupleB @_ @_ @t @r @s @f @tys x a

class FoldF (t :: k) (c :: LoT k -> Constraint) (r :: *)
            (x :: Atom l (*)) (loc :: WhereIsIt) (tys :: LoT l) where
  type AlgebraField t r x loc tys :: *
  foldF :: AlgebraF t c r
        -> Interpret x tys -> AlgebraField t r x loc tys
class UntupleF (t :: k) (x :: Atom l (*)) (r :: *) (s :: *) (loc :: WhereIsIt) (tys :: LoT l) where
  untupleF :: AlgebraField t (r, s) x loc tys
           -> (AlgebraField t r x loc tys, AlgebraField t s x loc tys)

instance FoldF t c r x 'NotFound tys where
  type AlgebraField t r x 'NotFound tys = Interpret x tys
  foldF _ x = x
instance UntupleF t x r s 'NotFound tys where
  untupleF x = (x, x)

instance ( p ~ InterpretAll (Args x) tys
         , Interpret x tys ~ (t :@@: p)
         , Foldy t c r p
         , c p )
         => FoldF t c r x 'TopLevel tys where
  type AlgebraField t r x 'TopLevel tys = r
  foldF recf x = foldG @_ @t @c @r @(InterpretAll (Args x) tys) recf x
instance UntupleF t x r s 'TopLevel tys where
  untupleF (a, b) = (a, b)

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

instance Functor (Algebra t c) where
  fmap f (Alg (Proxy :: Proxy x) v r) = Alg (Proxy @x) v (f . r)
instance (f ~ RepK t, forall tys. UnitB t f tys, forall r s tys. TupleB t r s f tys)
         => Applicative (Algebra t c) where
  pure x = Alg (Proxy @()) (\(Proxy :: Proxy tys) -> unitB @_ @_ @t @(RepK t) @tys) (\_ -> x)
  (Alg (px :: Proxy fx) fv fr) <*> (Alg (Proxy :: Proxy xx) xv xr)
         = Alg (Proxy @(fx, xx))
               (\(p :: Proxy tys) -> tupleB @_ @_ @t @fx @xx @(RepK t) @tys (fv p) (xv p))
               (\(f, x) -> fr f (xr x))
instance (Applicative (Algebra t c), Semigroup s)
         => Semigroup (Algebra t c s) where
  (<>) = liftA2 (<>)
instance (Applicative (Algebra t c), Monoid m)
         => Monoid (Algebra t c m) where
  mempty = pure mempty
instance (Applicative (Algebra t c), Num n)
         => Num (Algebra t c n) where
  fromInteger = pure . fromInteger
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  (-) = liftA2 (-)
instance (Applicative (Algebra t c), Fractional b)
         => Fractional (Algebra t c b) where
  fromRational = pure . fromRational
  recip = fmap recip
  (/) = liftA2 (/)
instance (Applicative (Algebra t c), Floating b)
         => Floating (Algebra t c b) where
  pi = pure pi
  exp = fmap exp
  sqrt = fmap sqrt
  log = fmap log
  sin = fmap sin
  tan = fmap tan
  cos = fmap cos
  asin = fmap asin
  atan = fmap atan
  acos = fmap acos
  sinh = fmap sinh
  tanh = fmap tanh
  cosh = fmap cosh
  asinh = fmap asinh
  atanh = fmap atanh
  acosh = fmap acosh
  (**) = liftA2 (**)
  logBase = liftA2 logBase