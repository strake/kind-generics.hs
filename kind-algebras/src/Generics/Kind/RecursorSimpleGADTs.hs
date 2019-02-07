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
module Generics.Kind.RecursorSimpleGADTs where

import Generics.Kind
import Generics.Kind.Examples
import Data.Proxy
import Unsafe.Coerce
import GHC.Base (liftA2, Constraint)
import qualified Control.Category as Cat
import qualified Control.Arrow as Arrow

data Algebra (t :: k) (r :: *) where
  Alg :: (forall tys. AlgebraB t x (RepK t) tys)
      -> (x -> r)
      -> Algebra t r

type AlgebraF t r = forall tys. AlgebraB t r (RepK t) tys

alg :: AlgebraF t r -> Algebra t r
alg recf = Alg recf id

instance Foldy Maybe r (a :&&: LoT0)

lengthAlg :: Algebra Maybe Int
lengthAlg = alg (Field 0  :*: OneArg (\_ -> Field 1))

applyLength = foldAlgebra @_ @Maybe @_ @_ @(Int :&&: LoT0) lengthAlg (Just 2)

maybeAlg :: Algebra Maybe Bool
maybeAlg = alg (Field False :*: OneArg (\_ -> Field True))

notMaybeAlg :: Algebra Maybe Bool
notMaybeAlg = not <$> maybeAlg

instance Foldy [] r (a :&&: LoT0)

lengthAlgList :: Algebra [] Int
lengthAlgList = alg (Field 1 :*: OneArg (\_ -> OneArg (\(Field n) -> Field(n+1))))

applyLengthList :: forall a. [a] -> Int
applyLengthList = foldAlgebra @_ @[] @_ @_ @(a :&&: LoT0) lengthAlgList

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

instance Foldy Vec r (a :&&: b :&&: LoT0)

lengthAlgVec :: Algebra Vec Int
lengthAlgVec = alg (IfImpliesK (Field 1) :*: ForAllK (IfImpliesK (OneArg (\_ -> OneArg (\(Field n) -> Field(n+1))))))

applyLengthVec :: forall n a. Vec n a -> Int
applyLengthVec = foldAlgebra @_ @Vec @_ @_ @(n :&&: a :&&: LoT0) lengthAlgVec

-- sumAlgVec :: Algebra Vec Int
-- sumAlgVec = alg (IfImpliesK (Field 0) :*: ForAllK (IfImpliesK (OneArg (\(Field n) -> OneArg (\(Field r) -> Field(n+r))))))

twiceLengthAlgVec :: Algebra Vec Int
twiceLengthAlgVec = (+) <$> lengthAlgVec <*> lengthAlgVec

type FoldK t r tys = (GenericK t tys, FoldB t r (RepK t) tys)

foldAlgebra :: forall k (t :: k) r f tys.
               (forall p. Foldy t p tys)
            => Algebra t r -> t :@@: tys -> r
foldAlgebra (Alg v (r :: x -> r)) x = r (foldG @k @t @x @tys v x)

-- In the simple recursor, f has kind LoT k -> * (same as t)

class Foldy (t :: k) (r :: *) (tys :: LoT k) where
  foldG :: AlgebraF t r -> t :@@: tys -> r
  default foldG :: (GenericK t tys, FoldB t r (RepK t) tys)
                => AlgebraF t r -> t :@@: tys -> r
  foldG a x = foldB @k @k @t @r @(RepK t) @tys a a (fromK @k @t x)

class FoldB (t :: k) (r :: *)
            (f :: LoT l -> *) (tys :: LoT l) where
  type AlgebraB t r f :: LoT l -> *
  foldB :: AlgebraF t r
        -> AlgebraB t r f tys -> f tys -> r
class UnitB (t :: k) (f :: LoT l -> *) (tys :: LoT l) where
  unitB :: AlgebraB t () f tys
class UnitB t f tys
      => TupleB (t :: k) (r :: *) (s :: *) 
                (f :: LoT l -> *) (tys :: LoT l) where
  tupleB :: AlgebraB t r f tys
         -> AlgebraB t s f tys
         -> AlgebraB t (r, s) f tys

instance ( FoldB t r f tys, FoldB t r g tys )
         => FoldB t r (f :+: g) tys where
  type AlgebraB t r (f :+: g) = AlgebraB t r f :*: AlgebraB t r g
  foldB recf (fx :*: _) (L1 x) = foldB @_ @_ @t recf fx x
  foldB recf (_ :*: fy) (R1 y) = foldB @_ @_ @t recf fy y
instance ( UnitB t f tys, UnitB t g tys )
         => UnitB t (f :+: g) tys where
  unitB = unitB @_ @_ @t @f :*: unitB @_ @_ @t @g
instance ( TupleB t r s f tys, TupleB t r s g tys )
         => TupleB t r s (f :+: g) tys where
  tupleB (x :*: y) (a :*: b)
    = tupleB @_ @_ @t @r @s @f x a :*: tupleB @_ @_ @t @r @s @g y b 

newtype (:~>:) (f :: LoT k -> *) (g :: LoT k -> *) (tys :: LoT k) where
  OneArg :: (f tys -> g tys) -> (f :~>: g) tys

newtype ForAllK d (f :: LoT (d -> k) -> *) (tys :: LoT k) where
  ForAllK :: (forall (ty :: d). f (ty :&&: tys)) -> ForAllK d f tys

newtype IfImpliesK (c :: Atom k Constraint) (f :: LoT k -> *) (tys :: LoT k) where
  IfImpliesK :: (Interpret c tys => f tys) -> IfImpliesK c f tys

instance FoldB t r U1 tys where
  type AlgebraB t r U1 = Field (Kon r)
  foldB _ (Field r) U1 = r
instance UnitB t U1 tys where
  unitB = Field ()
instance TupleB t r s U1 tys where
  tupleB (Field x) (Field a) = Field (x, a)

instance ( FoldF t r x (ElEncontrador t x) tys, FoldB t r y tys )
         => FoldB t r (Field x :*: y) tys where
  type AlgebraB t r (Field x :*: y) = Field (ElReemplazador t r x) :~>: AlgebraB t r y
  foldB recf (OneArg f) (v :*: w)
    = foldB @_ @_ @t recf
            (f (foldF @_ @_ @t @r @x @(ElEncontrador t x) recf v)) w
instance ( UnitB t y tys )
         => UnitB t (Field x :*: y) tys where
  unitB = OneArg (\_ -> unitB @_ @_ @t @y)
instance ( TupleB t r s y tys
         , UntupleF t x r s (ElEncontrador t x) tys )
         => TupleB t r s (Field x :*: y) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x @r @s 
                         @(ElEncontrador t x) @tys
                         v
        in tupleB @_ @_ @t @r @s @y (x vx) (a va)

instance ( FoldF t r x (ElEncontrador t x) tys )
         => FoldB t r (Field x) tys where
  type AlgebraB t r (Field x) = Field (ElReemplazador t r x) :~>: Field (Kon r)
  foldB recf (OneArg f) v
    = unField $ f (foldF @_ @_ @t @r @x @(ElEncontrador t x) recf v)
instance UnitB t (Field x) tys where
  unitB = OneArg (\_ -> Field ())
instance UntupleF t x r s (ElEncontrador t x) tys
         => TupleB t r s (Field x) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x @r @s
                         @(ElEncontrador t x) @tys
                         v
        in Field (unField $ x vx, unField $ a va)

instance ( forall ty. FoldB t r f (ty :&&: tys) )
         => FoldB t r (Exists k f) tys where
  type AlgebraB t r (Exists k f) = ForAllK k (AlgebraB t r f)
  foldB recf (ForAllK f) (Exists v)
    = foldB @_ @_ @t recf f v
instance ( forall ty. UnitB t f (ty :&&: tys) )
         => UnitB t (Exists k f) tys where
  unitB = ForAllK $ unitB @_ @_ @t @f
instance ( forall ty. TupleB t r s f (ty :&&: tys) )
         => TupleB t r s (Exists k f) tys where
  tupleB (ForAllK x) (ForAllK a)
    = ForAllK $ tupleB @_ @_ @t @r @s @f x a

instance ( Interpret c tys => FoldB t r f tys )
         => FoldB t r (c :=>: f) tys where
  type AlgebraB t r (c :=>: f) = IfImpliesK c (AlgebraB t r f)
  foldB recf (IfImpliesK f) (SuchThat v)
    = foldB @_ @_ @t recf f v
instance ( Interpret c tys => UnitB t f tys )
         => UnitB t (c :=>: f) tys where
  unitB = IfImpliesK (unitB @_ @_ @t @f)
instance ( Interpret c tys => TupleB t r s f tys )
         => TupleB t r s (c :=>: f) tys where
  tupleB (IfImpliesK x) (IfImpliesK a)
    = IfImpliesK $ tupleB @_ @_ @t @r @s @f x a

class FoldF (t :: k) (r :: *) (x :: Atom l (*))
            (ande :: WhereIsIt) (tys :: LoT l) where
  foldF :: AlgebraF t r
        -> Field x tys -> Field (ElReemplazador t r x) tys
class UntupleF (t :: k) (x :: Atom l (*)) (r :: *) (s :: *) (ande :: WhereIsIt) (tys :: LoT l) where
  untupleF :: Field (ElReemplazador t (r, s) x) tys
           -> (Field (ElReemplazador t r x) tys, Field (ElReemplazador t s x) tys)

instance (x ~ ElReemplazador t r x) => FoldF t r x 'NotFound tys where
  foldF _ x = x
instance ( ElReemplazador t r x ~ ElReemplazador t (r,s) x, ElReemplazador t s x ~ ElReemplazador t (r,s) x )
         => UntupleF t x r s 'NotFound tys where
  untupleF x = (x, x)

instance ( ElReemplazador t r x ~ Kon r
         , Foldy t r (InterpretAll (Args x) tys)
         , Interpret x tys ~ (t :@@: InterpretAll (Args x) tys)  )
         => FoldF t r x 'TopLevel tys where
  foldF recf (Field x) = Field $ foldG @_ @t @r @(InterpretAll (Args x) tys) recf x
instance UntupleF t (Kon t) r s 'TopLevel tys where
  untupleF (Field (a, b)) = (Field a, Field b)
instance UntupleF t (Kon t :@: a) r s 'TopLevel tys where
  untupleF (Field (a, b)) = (Field a, Field b)
instance UntupleF t (Kon t :@: a :@: b) r s 'TopLevel tys where
  untupleF (Field (a, b)) = (Field a, Field b)

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

type family ElReemplazador (t :: l) (r :: *) (a :: Atom d k) :: Atom d k where
  ElReemplazador t r (Kon t) = Kon r
  ElReemplazador t r (Kon t :@: x) = Kon r
  ElReemplazador t r (Kon t :@: x :@: y) = Kon r
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

instance Functor (Algebra t) where
  fmap f (Alg v r) = Alg v (f . r)
instance (f ~ RepK t, forall tys. UnitB t f tys, forall r s tys. TupleB t r s f tys)
         => Applicative (Algebra t) where
  pure x = Alg (unitB @_ @_ @t @(RepK t)) (\() -> x)
  (Alg fv (fr :: fx -> r -> s)) <*> (Alg xv (xr :: xx -> r))
         = Alg (tupleB @_ @_ @t @fx @xx @(RepK t) fv xv)
               (\(f, x) -> fr f (xr x))
instance (Applicative (Algebra t), Semigroup s)
         => Semigroup (Algebra t s) where
  (<>) = liftA2 (<>)
instance (Applicative (Algebra t), Monoid m)
         => Monoid (Algebra t m) where
  mempty = pure mempty
instance (Applicative (Algebra t), Num n)
         => Num (Algebra t n) where
  fromInteger = pure . fromInteger
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  (-) = liftA2 (-)
instance (Applicative (Algebra t), Fractional b)
         => Fractional (Algebra t b) where
  fromRational = pure . fromRational
  recip = fmap recip
  (/) = liftA2 (/)
instance (Applicative (Algebra t), Floating b)
         => Floating (Algebra t b) where
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

newtype AlgebraArr (t :: k) (a :: *) (b :: *) where
  AlgebraArr :: Algebra t (a -> b) -> AlgebraArr t a b

instance Applicative (Algebra t) => Cat.Category (AlgebraArr t) where
  (AlgebraArr f) . (AlgebraArr g) = AlgebraArr (liftA2 (.) f g)
  id = AlgebraArr $ pure id

instance Applicative (Algebra t) => Arrow.Arrow (AlgebraArr t) where
  arr f = AlgebraArr $ pure f
  first (AlgebraArr a) = AlgebraArr $ Arrow.first <$> a
  second (AlgebraArr a) = AlgebraArr $ Arrow.second <$> a
  AlgebraArr f *** AlgebraArr g = AlgebraArr $ (Arrow.***) <$> f <*> g
  AlgebraArr f &&& AlgebraArr g = AlgebraArr $ (Arrow.&&&) <$> f <*> g