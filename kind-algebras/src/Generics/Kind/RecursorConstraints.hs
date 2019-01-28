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
module Generics.Kind.RecursorConstraints where

import Generics.Kind
import Generics.Kind.Examples
import Data.Proxy
import Unsafe.Coerce
import GHC.Base (liftA2, Constraint)

infixr 5 :&&&:
data ConstraintsFor (t :: k) where
  NoMore :: ConstraintsFor (*)
  (:&&&:) :: (k -> Constraint) -> ConstraintsFor ks -> ConstraintsFor (k -> ks)

class Satisfies' cs tys => Zas (cs :: ConstraintsFor k) (tys :: LoT k) where
instance Satisfies' cs tys => Zas cs tys where

type family Satisfies' (cs ::ConstraintsFor k) (tys :: LoT k) :: Constraint where
  Satisfies' NoMore LoT0 = ()
  Satisfies' (c :&&&: cs) (ty :&&: tys) = (c ty, Satisfies' cs tys)

class Trivial (a :: k) where
instance Trivial a where

data Algebra (t :: k) (c :: LoT k -> Constraint) (r :: *) where
  Alg :: Proxy x
      -> (forall tys. c tys => Algebra' t x tys)
      -> (x -> r)
      -> Algebra t c r

upgrade :: (forall tys. d tys => c tys) => Algebra t c r -> Algebra t d r
upgrade (Alg px alg r) = Alg px alg r

class (c x, d x) => Both c d x where
instance (c x, d x) => Both c d x where

algebra1 :: forall t c x r. Proxy x
         -> (forall a. c (a :&&: LoT0) => Algebra' t x (a :&&: LoT0))
         -> (x -> r)
         -> Algebra t (Both SForLoT c) r
algebra1 p alg r = Alg p algebra1' r
  where
    algebra1' :: forall tys. (SForLoT tys, c tys) => Algebra' t x tys
    algebra1' = case slot @_ @tys of
                  SLoTA _ SLoT0 -> alg

algebra2 :: forall t c x r. Proxy x
         -> (forall a b. c (a :&&: b :&&: LoT0) => Algebra' t x (a :&&: b :&&: LoT0))
         -> (x -> r)
         -> Algebra t (Both SForLoT c) r
algebra2 p alg r = Alg p algebra2' r
  where
    algebra2' :: forall tys. (SForLoT tys, c tys) => Algebra' t x tys
    algebra2' = case slot @_ @tys of
                  SLoTA _ (SLoTA _ SLoT0) -> alg

lengthAlg :: forall a. Num a => Algebra Maybe Trivial a
lengthAlg = Alg (Proxy @a) (Field 0  :*: OneArg (\_ -> Field 1)) id

applyLength = foldAlgebra @_ @Maybe @_ @_ @_ @(Int :&&: LoT0) lengthAlg (Just 2)

maybeAlg :: Algebra Maybe Trivial Bool
maybeAlg = Alg (Proxy @Bool) (Field False :*: OneArg (\_ -> Field True)) id

notMaybeAlg :: Algebra Maybe Trivial Bool
notMaybeAlg = not <$> maybeAlg

sumAlg :: forall a. Num a => Algebra Maybe (Both SForLoT (Zas (((~) a) :&&&: NoMore))) a
sumAlg = algebra1 (Proxy @a) sumAlg' id
  where sumAlg' :: Algebra' Maybe a (a :&&: LoT0)
        sumAlg' = Field 0 :*: OneArg (\(Field n) -> Field n)

avgAlg :: forall a. Fractional a => Algebra Maybe (Both SForLoT (Zas (((~) a) :&&&: NoMore))) a
avgAlg = (/) <$> sumAlg <*> upgrade lengthAlg

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

lengthAlgVec :: Algebra Vec Trivial Int
lengthAlgVec = Alg (Proxy @Int) (IfImpliesK (Field 1) :*: ForAllK (IfImpliesK (OneArg (\_ -> OneArg (\(Field n) -> Field(n+1)))))) id

twiceLengthAlgVec :: Algebra Vec Trivial Int
twiceLengthAlgVec = (+) <$> lengthAlgVec <*> lengthAlgVec

sumAlgVec :: forall a. Num a => Algebra Vec (Both SForLoT (Zas (Trivial :&&&: ((~) a) :&&&: NoMore))) a
sumAlgVec = algebra2 (Proxy @a) sumAlg' id
  where sumAlg' :: forall n. Algebra' Vec a (n :&&: a :&&: LoT0)
        sumAlg' = (IfImpliesK $ Field 0)
                  :*: (ForAllK $ IfImpliesK $
                       OneArg $ \(Field x) ->
                       OneArg $ \(Field n) -> Field (x + n))

type Algebra' t r tys = AlgebraB t r (RepK t) tys
type FoldK t c r tys = (GenericK t tys, FoldB t c r (RepK t) tys)

foldAlgebra :: forall k (t :: k) c r f tys.
               (GenericK t tys, f ~ RepK t, forall p. FoldB t c p f tys, c tys)
            => Algebra t c r -> t :@@: tys -> r
foldAlgebra (Alg (Proxy :: Proxy x) v r) x = r (foldG @k @t @c @x @tys v x)

foldG :: forall k (t :: k) c r tys. (FoldK t c r tys, c tys)
      => (forall bop. c bop => Algebra' t r bop)
      -> t :@@: tys -> r
foldG alg x = foldB @_ @_ @t @c @r @(RepK t) @tys alg alg (fromK @k @t x)

-- In the simple recursor, f has kind LoT k -> * (same as t)

class FoldB (t :: k) (c :: LoT k -> Constraint) (r :: *)
            (f :: LoT l -> *) (tys :: LoT l) where
  type AlgebraB t r f :: LoT l -> *
  foldB :: (forall bop. c bop => Algebra' t r bop)
        -> AlgebraB t r f tys -> f tys -> r
class UnitB (t :: k) (f :: LoT l -> *) (tys :: LoT l) where
  unitB :: AlgebraB t () f tys
class UnitB t f tys
      => TupleB (t :: k) (r :: *) (s :: *) 
                (f :: LoT l -> *) (tys :: LoT l) where
  tupleB :: AlgebraB t r f tys
         -> AlgebraB t s f tys
         -> AlgebraB t (r, s) f tys

instance ( FoldB t c r f tys, FoldB t c r g tys )
         => FoldB t c r (f :+: g) tys where
  type AlgebraB t r (f :+: g) = AlgebraB t r f :*: AlgebraB t r g
  foldB recf (fx :*: _) (L1 x) = foldB @_ @_ @t @c recf fx x
  foldB recf (_ :*: fy) (R1 y) = foldB @_ @_ @t @c recf fy y
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

instance FoldB t c r U1 tys where
  type AlgebraB t r U1 = Field (Kon r)
  foldB _ (Field r) U1 = r
instance UnitB t U1 tys where
  unitB = Field ()
instance TupleB t r s U1 tys where
  tupleB (Field x) (Field a) = Field (x, a)

instance ( FoldF t c r x (Igualicos x (ElReemplazador t r x)) tys, FoldB t c r y tys )
         => FoldB t c r (Field x :*: y) tys where
  type AlgebraB t r (Field x :*: y) = Field (ElReemplazador t r x) :~>: AlgebraB t r y
  foldB recf (OneArg f) (v :*: w)
    = foldB @_ @_ @t @c recf
            (f (foldF @_ @_ @t @c @r @x @(Igualicos x (ElReemplazador t r x)) recf v)) w
instance ( UnitB t y tys )
         => UnitB t (Field x :*: y) tys where
  unitB = OneArg (\_ -> unitB @_ @_ @t @y)
instance ( TupleB t r s y tys
         , UntupleF t x r s (Igualicos x (ElReemplazador t () x)) tys )
         => TupleB t r s (Field x :*: y) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x @r @s 
                         @(Igualicos x (ElReemplazador t () x)) @tys
                         v
        in tupleB @_ @_ @t @r @s @y (x vx) (a va)

instance ( FoldF t c r x (Igualicos x (ElReemplazador t r x)) tys )
         => FoldB t c r (Field x) tys where
  type AlgebraB t r (Field x) = Field (ElReemplazador t r x) :~>: Field (Kon r)
  foldB recf (OneArg f) v
    = unField $ f (foldF @_ @_ @t @c @r @x @(Igualicos x (ElReemplazador t r x)) recf v)
instance UnitB t (Field x) tys where
  unitB = OneArg (\_ -> Field ())
instance UntupleF t x r s (Igualicos x (ElReemplazador t () x)) tys
         => TupleB t r s (Field x) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x @r @s
                         @(Igualicos x (ElReemplazador t () x)) @tys
                         v
        in Field (unField $ x vx, unField $ a va)

instance ( forall ty. FoldB t c r f (ty :&&: tys) )
         => FoldB t c r (Exists k f) tys where
  type AlgebraB t r (Exists k f) = ForAllK k (AlgebraB t r f)
  foldB recf (ForAllK f) (Exists v)
    = foldB @_ @_ @t @c recf f v
instance ( forall ty. UnitB t f (ty :&&: tys) )
         => UnitB t (Exists k f) tys where
  unitB = ForAllK $ unitB @_ @_ @t @f
instance ( forall ty. TupleB t r s f (ty :&&: tys) )
         => TupleB t r s (Exists k f) tys where
  tupleB (ForAllK x) (ForAllK a)
    = ForAllK $ tupleB @_ @_ @t @r @s @f x a

instance ( Interpret d tys => FoldB t c r f tys )
         => FoldB t c r (d :=>: f) tys where
  type AlgebraB t r (d :=>: f) = IfImpliesK d (AlgebraB t r f)
  foldB recf (IfImpliesK f) (SuchThat v)
    = foldB @_ @_ @t @c recf f v
instance ( Interpret c tys => UnitB t f tys )
         => UnitB t (c :=>: f) tys where
  unitB = IfImpliesK (unitB @_ @_ @t @f)
instance ( Interpret c tys => TupleB t r s f tys )
         => TupleB t r s (c :=>: f) tys where
  tupleB (IfImpliesK x) (IfImpliesK a)
    = IfImpliesK $ tupleB @_ @_ @t @r @s @f x a

class FoldF (t :: k) (c :: LoT k -> Constraint) (r :: *) (x :: Atom l (*))
            (igualicos :: Bool) (tys :: LoT l) where
  foldF :: (forall bop. c bop => Algebra' t r bop)
        -> Field x tys -> Field (ElReemplazador t r x) tys
class UntupleF (t :: k) (x :: Atom l (*)) (r :: *) (s :: *) (igualicos :: Bool) (tys :: LoT l) where
  untupleF :: Field (ElReemplazador t (r, s) x) tys
           -> (Field (ElReemplazador t r x) tys, Field (ElReemplazador t s x) tys)

instance (x ~ ElReemplazador t r x) => FoldF t c r x 'True tys where
  foldF _ x = x
instance ( ElReemplazador t r x ~ ElReemplazador t (r,s) x, ElReemplazador t s x ~ ElReemplazador t (r,s) x )
         => UntupleF t x r s 'True tys where
  untupleF x = (x, x)

instance ( FoldK t c r LoT0, c LoT0 )
         => FoldF t c r (Kon t) 'False LoT0 where
  foldF recf (Field x) = Field $ foldG @_ @t @c @r @LoT0 recf x
-- For now we do not allow weird recursion
instance ( FoldK t c r (LoT1 (Interpret a (LoT1 x)))
         , a ~ ElReemplazador t r a
         , c (LoT1 (Interpret a (LoT1 x))) )
         => FoldF t c r (Kon t :@: a) 'False (LoT1 x) where
  foldF recf (Field x) = Field $ foldG @_ @t @c @r @(LoT1 (Interpret a (LoT1 x))) recf x
instance ( FoldK t c r (LoT2 (Interpret a (LoT2 x y)) (Interpret b (LoT2 x y)))
         , a ~ ElReemplazador t r a, b ~ ElReemplazador t r b
         , c (LoT2 (Interpret a (LoT2 x y)) (Interpret b (LoT2 x y))) )
         => FoldF t c r (Kon t :@: a :@: b) 'False (LoT2 x y) where
  foldF recf (Field x) = Field $ foldG @_ @t @c @r @(LoT2 (Interpret a (LoT2 x y)) (Interpret b (LoT2 x y))) recf x

instance UntupleF t (Kon t) r s 'False tys where
  untupleF (Field (a, b)) = (Field a, Field b)
instance UntupleF t (Kon t :@: a) r s 'False tys where
  untupleF (Field (a, b)) = (Field a, Field b)
instance UntupleF t (Kon t :@: a :@: b) r s 'False tys where
  untupleF (Field (a, b)) = (Field a, Field b)

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

type family Igualicos (a :: k) (b :: k) :: Bool where
  Igualicos a a = 'True
  Igualicos a b = 'False

instance Functor (Algebra t c) where
  fmap f (Alg (Proxy :: Proxy x) v r) = Alg (Proxy @x) v (f . r)
instance (f ~ RepK t, forall tys. UnitB t f tys, forall r s tys. TupleB t r s f tys)
         => Applicative (Algebra t c) where
  pure x = Alg (Proxy @()) (unitB @_ @_ @t @(RepK t)) (\_ -> x)
  (Alg (px :: Proxy fx) fv fr) <*> (Alg (Proxy :: Proxy xx) xv xr)
         = Alg (Proxy @(fx, xx))
               (tupleB @_ @_ @t @fx @xx @(RepK t) fv xv)
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