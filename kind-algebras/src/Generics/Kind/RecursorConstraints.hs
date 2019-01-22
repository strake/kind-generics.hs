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
module Generics.Kind.RecursorConstraints where

import Generics.Kind
import Generics.Kind.Examples
import Data.Proxy
import Unsafe.Coerce
import GHC.Base (liftA2, Constraint)

newtype Const x tys = Const { unConst :: x }

data Algebra (t :: k) (c :: LoT k -> Constraint) (r :: *) where
  Alg :: Proxy x
      -> (forall tys. c tys => Algebra' t x tys)
      -> (x -> r)
      -> Algebra t c r

class Trivial tys where
instance Trivial tys where

class ConstraintFirst (c :: p -> Constraint) (tys :: LoT k) where
instance (c a, tys ~ (a :&&: as)) => ConstraintFirst c tys where

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
type FoldK t c r tys = (GenericK t tys, FoldDT t c r (RepK t) tys)

foldAlgebra :: forall k (t :: k) c r f tys.
               (GenericK t tys, f ~ RepK t, forall p. FoldDT t c p f tys, c tys)
            => Algebra t c r -> t :@@: tys -> r
foldAlgebra (Alg (Proxy :: Proxy x) v r) x = r (foldG @k @t @c @x @tys v x)

foldG :: forall k (t :: k) c r tys. (FoldK t c r tys, c tys)
      => (forall bop. c bop => Algebra' t r bop)
      -> t :@@: tys -> r
foldG alg x = foldDT @_ @t @c @r @(RepK t) @tys alg alg (fromK @k @t x)

class FoldDT (t :: k) (c :: LoT k -> Constraint)
             (r :: *) (f :: LoT k -> *) (tys :: LoT k) where
  type AlgebraDT t r f :: LoT k -> *
  foldDT :: (forall bop. c bop => Algebra' t r bop)
         -> AlgebraDT t r f tys -> f tys -> r
class UnitDT (t :: k) (f :: LoT k -> *) (tys :: LoT k) where
  unitDT :: AlgebraDT t () f tys
class UnitDT t f tys
      => TupleDT (t :: k) (r :: *) (s :: *) (f :: LoT k -> *) (tys :: LoT k) where
  tupleDT :: AlgebraDT t r f tys
          -> AlgebraDT t s f tys
          -> AlgebraDT t (r, s) f tys

instance forall t c r f g tys. 
         ( FoldB t c r r f tys, FoldDT t c r g tys )
         => FoldDT t c r (f :+: g) tys where
  type AlgebraDT t r (f :+: g) = AlgebraB t r r f :*: AlgebraDT t r g
  foldDT recf (fx :*: _) (L1 x) = foldB  @_ @_ @t @c @r @r @f @tys recf fx x
  foldDT recf (_ :*: fy) (R1 y) = foldDT @_ @t @c @r @g @tys recf fy y
instance forall t f g tys.
         ( UnitB t f tys, UnitDT t g tys )
         => UnitDT t (f :+: g) tys where
  unitDT = unitB @_ @_ @t @f @tys :*: unitDT @_ @t @g @tys
instance forall t r s f g tys.
         ( TupleB t r r s s f tys, TupleDT t r s g tys )
         => TupleDT t r s (f :+: g) tys where
  tupleDT (x :*: y) (a :*: b)
    = tupleB @_ @_ @t @r @r @s @s @f @tys x a :*: tupleDT @_ @t @r @s @g @tys y b 

-- Fallback, copied to remove ovelapping
instance forall t c r tys. FoldDT t c r U1 tys where
  type AlgebraDT t r U1 = AlgebraB t r r U1
  foldDT recf x = foldB @_ @_ @t @c @r @r @U1 @tys recf x
instance forall t tys. UnitDT t U1 tys where
  unitDT = unitB @_ @_ @t @U1 @tys
instance forall t r s tys. TupleDT t r s U1 tys where
  tupleDT x a = tupleB @_ @_ @t @r @r @s @s @U1 @tys x a

instance forall t c r x tys. 
         FoldB t c r r (Field x) tys
         => FoldDT t c r (Field x) tys where
  type AlgebraDT t r (Field x) = AlgebraB t r r (Field x)
  foldDT recf x = foldB @_ @_ @t @c @r @r @(Field x) @tys recf x
instance forall t x tys.
         UnitB t (Field x) tys
         => UnitDT t (Field x) tys where
  unitDT = unitB @_ @_ @t @(Field x) @tys
instance forall t r s x tys.
         TupleB t r r s s (Field x) tys
         => TupleDT t r s(Field x) tys where
  tupleDT x a = tupleB @_ @_ @t @r @r @s @s @(Field x) @tys x a

instance forall t c r x y tys. 
         FoldB t c r r (Field x :*: y) tys
         => FoldDT t c r (Field x :*: y) tys where
  type AlgebraDT t r (Field x :*: y) = AlgebraB t r r (Field x :*: y)
  foldDT recf x = foldB @_ @_ @t @c @r @r @(Field x :*: y) @tys recf x
instance forall t x y tys.
         UnitB t (Field x :*: y) tys
         => UnitDT t (Field x :*: y) tys where
  unitDT = unitB @_ @_ @t @(Field x :*: y) @tys
instance forall t r s x y tys.
         TupleB t r r s s (Field x :*: y) tys
         => TupleDT t r s (Field x :*: y) tys where
  tupleDT x a = tupleB @_ @_ @t @r @r @s @s @(Field x :*: y) @tys x a

class FoldB (t :: l) (c :: LoT l -> Constraint)
            (r :: *) (newr :: *)
            (f :: LoT k -> *) (tys :: LoT k) where
  type AlgebraB t r newr f :: LoT k -> *
  foldB :: (forall bop. c bop => Algebra' t r bop)
        -> AlgebraB t r newr f tys -> f tys -> newr
class UnitB (t :: l) (f :: LoT k -> *) (tys :: LoT k) where
  unitB :: AlgebraB t () () f tys
class UnitB t f tys
      => TupleB (t :: l) (r :: *) (newr :: *)
                         (s :: *) (news :: *)
                         (f :: LoT k -> *) (tys :: LoT k) where
  tupleB :: AlgebraB t r newr f tys
         -> AlgebraB t s news f tys
         -> AlgebraB t (r, s) (newr, news) f tys

newtype (:~>:) (f :: LoT k -> *) (g :: LoT k -> *) (tys :: LoT k) where
  OneArg :: (f tys -> g tys) -> (f :~>: g) tys

instance FoldB t c r newr U1 tys where
  type AlgebraB t r newr U1 = Field (Kon newr)
  foldB _ (Field r) U1 = r
instance UnitB t U1 tys where
  unitB = Field ()
instance TupleB t r newr s news U1 tys where
  tupleB (Field x) (Field a) = Field (x, a)

instance forall t c r newr x y tys. 
         ( FoldF t c r x (Igualicos x (ElReemplazador t r x)) tys, FoldB t c r newr y tys )
         => FoldB t c r newr (Field x :*: y) tys where
  type AlgebraB t r newr (Field x :*: y) = Field (ElReemplazador t r x) :~>: AlgebraB t r newr y
  foldB recf (OneArg f) (v :*: w)
    = foldB @_ @_ @t @c @r @newr @y recf
            (f (foldF @_ @_ @t @c @r @x @(Igualicos x (ElReemplazador t r x)) @tys recf v)) w
instance forall t x y tys. ( UnitB t y tys )
         => UnitB t (Field x :*: y) tys where
  unitB = OneArg (\_ -> unitB @_ @_ @t @y @tys)
instance forall t r newr s news x y tys.
         ( TupleB t r newr s news y tys
         , UntupleF t x (Igualicos x (ElReemplazador t () x)) tys )
         => TupleB t r newr s news (Field x :*: y) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x 
                         @(Igualicos x (ElReemplazador t () x)) @tys
                         @r @s v
        in tupleB @_ @_ @t @r @newr @s @news @y @tys (x vx) (a va)

instance forall t c r newr x tys. 
         ( FoldF t c r x (Igualicos x (ElReemplazador t r x)) tys )
         => FoldB t c r newr (Field x) tys where
  type AlgebraB t r newr (Field x) = Field (ElReemplazador t r x) :~>: Field (Kon newr)
  foldB recf (OneArg f) v
    = unField $ f (foldF @_ @_ @t @c @r @x @(Igualicos x (ElReemplazador t r x)) @tys recf v)
instance forall t x tys. UnitB t (Field x) tys where
  unitB = OneArg (\_ -> Field ())
instance forall t r newr s news x tys.
         UntupleF t x (Igualicos x (ElReemplazador t () x)) tys
         => TupleB t r newr s news (Field x) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x 
                         @(Igualicos x (ElReemplazador t () x)) @tys
                         @r @s v
        in Field (unField $ x vx, unField $ a va)

class FoldF (t :: l) (c :: LoT l -> Constraint) 
            (r :: *) (x :: Atom k (*))
            (igualicos :: Bool) (tys :: LoT k) where
  foldF :: (forall bop. c bop => Algebra' t r bop)
        -> Field x tys -> Field (ElReemplazador t r x) tys
class UntupleF (t :: l) (x :: Atom k (*)) (igualicos :: Bool) (tys :: LoT k) where
  untupleF :: Field (ElReemplazador t (r, s) x) tys
           -> (Field (ElReemplazador t r x) tys, Field (ElReemplazador t s x) tys)

instance (x ~ ElReemplazador t r x) => FoldF t c r x 'True tys where
  foldF _ x = x
instance ( forall l. x ~ ElReemplazador t l x )
         => UntupleF t x 'True tys where
  untupleF x = (unsafeCoerce x, unsafeCoerce x)

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