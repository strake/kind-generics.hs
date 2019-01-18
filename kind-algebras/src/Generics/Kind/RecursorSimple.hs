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
module Generics.Kind.RecursorSimple where

import Generics.Kind
import Generics.Kind.Examples
import Data.Proxy
import Unsafe.Coerce
import GHC.Base (liftA2, Constraint)

data Algebra (t :: k) (r :: *) where
  Alg :: Proxy x
      -> (forall tys. Algebra' t x tys)
      -> (x -> r)
      -> Algebra t r

lengthAlg :: Algebra Maybe Int
lengthAlg = Alg (Proxy @Int) (Field 0  :*: OneArg (\_ -> Field 1)) id

applyLength = foldAlgebra @_ @Maybe @_ @_ @(Int :&&: LoT0) lengthAlg (Just 2)

{-
maybeAlg :: AlgebraConst Maybe Trivial Bool
maybeAlg = AlgebraConst $ Alg Proxy (Const False :*: (OneArg (\_ -> Const True))) id
-}
{-
sumMaybeAlg :: Algebra Maybe (ConstraintFirst Num) DataFirst
sumMaybeAlg = Alg (DataFirst 0 :*: (OneArg (\(Field n) -> DataFirst n))) id
-}

{-
instance forall t c. Functor (AlgebraConst t c) where
  fmap :: forall a b. (a -> b) -> AlgebraConst t c a -> AlgebraConst t c b
  fmap f (AlgebraConst (Alg (Proxy :: Proxy x) v r))
    = AlgebraConst $ Alg (Proxy @x) v (Const . f . unConst . r)
instance forall f t c. (f ~ RepK t, forall tys. UnitDT t f tys, forall r s tys. TupleDT t r s f tys)
         => Applicative (AlgebraConst t c) where
  pure :: forall a. a -> AlgebraConst t c a
  pure x = AlgebraConst $ Alg (Proxy @(Const ()))
                              (unitDT @_ @t @(RepK t))
                              (\(_ :: Const () lys) -> Const x)
  (<*>) :: forall a b. AlgebraConst t c (a -> b) -> AlgebraConst t c a -> AlgebraConst t c b
  (AlgebraConst (Alg (px :: Proxy fx) fv fr)) <*> (AlgebraConst (Alg (Proxy :: Proxy xx) xv xr))
         = AlgebraConst
         $ Alg (Proxy @(fx :*: xx))
               (tupleDT @_ @t @fx @xx @(RepK t) fv xv)
               (\(f :*: x) -> Const (unConst (fr f) $ unConst (xr x)))
instance (Applicative (AlgebraConst t c), Semigroup s)
         => Semigroup (AlgebraConst t c s) where
  (<>) = liftA2 (<>)
instance (Applicative (AlgebraConst t c), Monoid m)
         => Monoid (AlgebraConst t c m) where
  mempty = pure mempty
instance (Applicative (AlgebraConst t c), Num n)
         => Num (AlgebraConst t c n) where
  fromInteger = pure . fromInteger
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  (+) = liftA2 (+)
  (*) = liftA2 (*)
  (-) = liftA2 (-)
instance (Applicative (AlgebraConst t c), Fractional b)
         => Fractional (AlgebraConst t c b) where
  fromRational = pure . fromRational
  recip = fmap recip
  (/) = liftA2 (/)
instance (Applicative (AlgebraConst t c), Floating b)
         => Floating (AlgebraConst t c b) where
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
-}

type Algebra' t r tys = AlgebraDT t r (RepK t) tys
type FoldK t r tys = (GenericK t tys, FoldDT t r (RepK t) tys)

foldAlgebra :: forall k (t :: k) r f tys.
               (GenericK t tys, f ~ RepK t, forall p. FoldDT t p f tys)
            => Algebra t r -> t :@@: tys -> r
foldAlgebra (Alg (Proxy :: Proxy x) v r) x = r (foldG @k @t @x @tys v x)

foldG :: forall k (t :: k) r tys. (FoldK t r tys)
      => (forall bop. Algebra' t r bop)
      -> t :@@: tys -> r
foldG alg x = foldDT @_ @t @r @(RepK t) @tys alg alg (fromK @k @t x)

class FoldDT (t :: k) (r :: *) (f :: LoT k -> *) (tys :: LoT k) where
  type AlgebraDT t r f :: LoT k -> *
  foldDT :: (forall bop. Algebra' t r bop)
         -> AlgebraDT t r f tys -> f tys -> r
class UnitDT (t :: k) (f :: LoT k -> *) (tys :: LoT k) where
  unitDT :: AlgebraDT t () f tys
class UnitDT t f tys
      => TupleDT (t :: k) (r :: *) (s :: *) (f :: LoT k -> *) (tys :: LoT k) where
  tupleDT :: AlgebraDT t r f tys
          -> AlgebraDT t s f tys
          -> AlgebraDT t (r, s) f tys

instance forall t r f g tys. 
         ( FoldB t r f tys, FoldDT t r g tys )
         => FoldDT t r (f :+: g) tys where
  type AlgebraDT t r (f :+: g) = AlgebraB t r f :*: AlgebraDT t r g
  foldDT recf (fx :*: _) (L1 x) = foldB  @_ @t @r @f @tys recf fx x
  foldDT recf (_ :*: fy) (R1 y) = foldDT @_ @t @r @g @tys recf fy y
instance forall t f g tys.
         ( UnitB t f tys, UnitDT t g tys )
         => UnitDT t (f :+: g) tys where
  unitDT = unitB @_ @t @f @tys :*: unitDT @_ @t @g @tys
instance forall t r s f g tys.
         ( TupleB t r s f tys, TupleDT t r s g tys )
         => TupleDT t r s (f :+: g) tys where
  tupleDT (x :*: y) (a :*: b)
    = tupleB @_ @t @r @s @f @tys x a :*: tupleDT @_ @t @r @s @g @tys y b 

-- Fallback, copied to remove ovelapping
instance forall t r tys. FoldDT t r U1 tys where
  type AlgebraDT t r U1 = AlgebraB t r U1
  foldDT recf x = foldB @_ @t @r @U1 @tys recf x
instance forall t tys. UnitDT t U1 tys where
  unitDT = unitB @_ @t @U1 @tys
instance forall t r s tys. TupleDT t r s U1 tys where
  tupleDT x a = tupleB @_ @t @r @s @U1 @tys x a

instance forall t r x tys. 
         FoldB t r (Field x) tys
         => FoldDT t r (Field x) tys where
  type AlgebraDT t r (Field x) = AlgebraB t r (Field x)
  foldDT recf x = foldB @_ @t @r @(Field x) @tys recf x
instance forall t x tys.
         UnitB t (Field x) tys
         => UnitDT t (Field x) tys where
  unitDT = unitB @_ @t @(Field x) @tys
instance forall t r s x tys.
         TupleB t r s (Field x) tys
         => TupleDT t r s(Field x) tys where
  tupleDT x a = tupleB @_ @t @r @s @(Field x) @tys x a

instance forall t r x y tys. 
         FoldB t r (Field x :*: y) tys
         => FoldDT t r (Field x :*: y) tys where
  type AlgebraDT t r (Field x :*: y) = AlgebraB t r (Field x :*: y)
  foldDT recf x = foldB @_ @t @r @(Field x :*: y) @tys recf x
instance forall t x y tys.
         UnitB t (Field x :*: y) tys
         => UnitDT t (Field x :*: y) tys where
  unitDT = unitB @_ @t @(Field x :*: y) @tys
instance forall t r s x y tys.
         TupleB t r s (Field x :*: y) tys
         => TupleDT t r s (Field x :*: y) tys where
  tupleDT x a = tupleB @_ @t @r @s @(Field x :*: y) @tys x a

class FoldB (t :: k) (r :: *)
            (f :: LoT k -> *) (tys :: LoT k) where
  type AlgebraB t r f :: LoT k -> *
  foldB :: (forall bop. Algebra' t r bop)
        -> AlgebraB t r f tys -> f tys -> r
class UnitB (t :: k) (f :: LoT k -> *) (tys :: LoT k) where
  unitB :: AlgebraB t () f tys
class UnitB t f tys
      => TupleB (t :: k) (r :: *) (s :: *) 
                (f :: LoT k -> *) (tys :: LoT k) where
  tupleB :: AlgebraB t r f tys
         -> AlgebraB t s f tys
         -> AlgebraB t (r, s) f tys

newtype (:~>:) (f :: LoT k -> *) (g :: LoT k -> *) (tys :: LoT k) where
  OneArg :: (f tys -> g tys) -> (f :~>: g) tys

instance FoldB t r U1 tys where
  type AlgebraB t r U1 = Field (Kon r)
  foldB _ (Field r) U1 = r
instance UnitB t U1 tys where
  unitB = Field ()
instance TupleB t r s U1 tys where
  tupleB (Field x) (Field a) = Field (x, a)

instance forall t r x y tys. 
         ( FoldF t r x (Igualicos x (ElReemplazador t r x)) tys, FoldB t r y tys )
         => FoldB t r (Field x :*: y) tys where
  type AlgebraB t r (Field x :*: y) = Field (ElReemplazador t r x) :~>: AlgebraB t r y
  foldB recf (OneArg f) (v :*: w)
    = foldB @_ @t @r @y recf
            (f (foldF @_ @t @r @x @(Igualicos x (ElReemplazador t r x)) @tys recf v)) w
instance forall t x y tys. ( UnitB t y tys )
         => UnitB t (Field x :*: y) tys where
  unitB = OneArg (\_ -> unitB @_ @t @y @tys)
instance forall t r s x y tys.
         ( TupleB t r s y tys
         , UntupleF t x (Igualicos x (ElReemplazador t () x)) tys )
         => TupleB t r s (Field x :*: y) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @t @x 
                         @(Igualicos x (ElReemplazador t () x)) @tys
                         @r @s v
        in tupleB @_ @t @r  @s @y @tys (x vx) (a va)

instance forall t r x tys. 
         ( FoldF t r x (Igualicos x (ElReemplazador t r x)) tys )
         => FoldB t r (Field x) tys where
  type AlgebraB t r (Field x) = Field (ElReemplazador t r x) :~>: Field (Kon r)
  foldB recf (OneArg f) v
    = unField $ f (foldF @_ @t @r @x @(Igualicos x (ElReemplazador t r x)) @tys recf v)
instance forall t x tys. UnitB t (Field x) tys where
  unitB = OneArg (\_ -> Field ())
instance forall t r s x tys.
         UntupleF t x (Igualicos x (ElReemplazador t () x)) tys
         => TupleB t r s (Field x) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @t @x 
                         @(Igualicos x (ElReemplazador t () x)) @tys
                         @r @s v
        in Field (unField $ x vx, unField $ a va)

class FoldF (t :: k) (r :: *) (x :: Atom k (*))
            (igualicos :: Bool) (tys :: LoT k) where
  foldF :: (forall bop. Algebra' t r bop)
        -> Field x tys -> Field (ElReemplazador t r x) tys
class UntupleF (t :: k) (x :: Atom k (*)) (igualicos :: Bool) (tys :: LoT k) where
  untupleF :: Field (ElReemplazador t (r, s) x) tys
           -> (Field (ElReemplazador t r x) tys, Field (ElReemplazador t s x) tys)

instance (x ~ ElReemplazador t r x) => FoldF t r x 'True tys where
  foldF _ x = x
instance ( forall l. x ~ ElReemplazador t l x )
         => UntupleF t x 'True tys where
  untupleF x = (unsafeCoerce x, unsafeCoerce x)

instance ( FoldK t r LoT0, c LoT0 )
         => FoldF t r (Kon t) 'False LoT0 where
  foldF recf (Field x) = Field $ foldG @_ @t @r @LoT0 recf x
-- For now we do not allow weird recursion
instance ( FoldK t r (LoT1 (Interpret a (LoT1 x)))
         , a ~ ElReemplazador t r a )
         => FoldF t r (Kon t :@: a) 'False (LoT1 x) where
  foldF recf (Field x) = Field $ foldG @_ @t @r @(LoT1 (Interpret a (LoT1 x))) recf x
instance ( FoldK t r (LoT2 (Interpret a (LoT2 x y)) (Interpret b (LoT2 x y)))
         , a ~ ElReemplazador t r a, b ~ ElReemplazador t r b )
         => FoldF t r (Kon t :@: a :@: b) 'False (LoT2 x y) where
  foldF recf (Field x) = Field $ foldG @_ @t @r @(LoT2 (Interpret a (LoT2 x y)) (Interpret b (LoT2 x y))) recf x

instance UntupleF t (Kon t) 'False LoT0 where
  untupleF (Field (a, b)) = (Field a, Field b)
instance ( forall l. a ~ ElReemplazador t l a )
         => UntupleF t (Kon t :@: a) 'False (LoT1 x) where
  untupleF (Field (a, b)) = (Field a, Field b)
instance ( forall l. a ~ ElReemplazador t l a, forall l. b ~ ElReemplazador t l b )
         => UntupleF t (Kon t :@: a :@: b) 'False (LoT2 x y) where
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