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
module Generics.Kind.Inductor where

import Generics.Kind
import Generics.Kind.Examples
import Data.Proxy
import Unsafe.Coerce
import GHC.Base (liftA2, Constraint)

newtype Const x tys = Const { unConst :: x }
newtype AlgebraConst (t :: k) (c :: ConstraintsFor k) (r :: *)
  = AlgebraConst { unAC :: Algebra t c (Const r) }

infixr 5 :&&&:
data ConstraintsFor (t :: k) where
  Trivial :: ConstraintsFor ks
  (:&&&:) :: (k -> Constraint) -> ConstraintsFor ks -> ConstraintsFor (k -> ks)

type family TysSatisfy (c :: ConstraintsFor k) (tys :: LoT k) :: Constraint where
  TysSatisfy Trivial lot = ()
  TysSatisfy (c :&&&: cs) (t :&&: ts) = (c t, TysSatisfy cs ts)

data DataFirst (tys :: LoT k) where
  DataFirst :: { unDataFirst :: a } -> DataFirst (a :&&: as)

maybeAlg :: AlgebraConst Maybe Trivial Bool
maybeAlg = AlgebraConst $ Alg Proxy (Const False :*: (OneArg (\_ -> Const True))) id

sumMaybeAlg :: Algebra Maybe (Num :&&&: Trivial) DataFirst
sumMaybeAlg = Alg (Proxy @DataFirst) (nothingCase :*: OneArg justCase) id
  where nothingCase :: forall (tys :: LoT (* -> *)).
                       (TysSatisfy (Num :&&&: Trivial) tys, SForLoT tys) => DataFirst tys
        nothingCase = case slot @_ @tys of
                        SLoTA _ SLoT0 -> DataFirst (fromInteger 0)
        justCase :: forall (tys :: LoT (* -> *)).
                    (TysSatisfy (Num :&&&: Trivial) tys, SForLoT tys)
                 => Field Var0 tys -> DataFirst tys
        justCase n = case slot @_ @tys of
                       SLoTA _ SLoT0 -> case n of
                         Field m -> DataFirst m


sumTreeAlg :: Algebra Tree (Num :&&&: Trivial) DataFirst
sumTreeAlg = Alg (Proxy @DataFirst) (branchCase :*: leafCase) id
  where branchCase :: forall (tys :: LoT (* -> *)).
                      (TysSatisfy (Num :&&&: Trivial) tys, SForLoT tys)
                      => (Field (DataFirst :$: ((:&&:) :$: Var0 :@: Kon LoT0)) :~>:
                          Field (DataFirst :$: ((:&&:) :$: Var0 :@: Kon LoT0)) :~>:
                          DataFirst) tys
        branchCase = case slot @_ @tys of
                        SLoTA (_ :: Proxy me) SLoT0 ->
                          OneArg $ \(Field (DataFirst l)) ->
                            OneArg $ \(Field (DataFirst r)) ->
                              DataFirst @me @LoT0 (l + r)
        leafCase :: forall (tys :: LoT (* -> *)).
                    (TysSatisfy (Num :&&&: Trivial) tys, SForLoT tys)
                    => (Field Var0 :~>: DataFirst) tys
        leafCase = case slot @_ @tys of
                     SLoTA (_ :: Proxy me) SLoT0 ->
                       OneArg $ \(Field n) -> DataFirst n

foldAlgebraConst
  :: forall k (t :: k) c r f tys.
     (GenericK t, f ~ RepK t, forall p. FoldDT t c p f tys, TysSatisfy c tys, SForLoT tys)
     => AlgebraConst t c r -> t :@@: tys -> r
foldAlgebraConst (AlgebraConst alg) = unConst . foldAlgebra @_ @t @c @(Const r) @_ @tys alg

foldAlgebraFirst
  :: forall k (t :: * -> k) c r f a as.
     (GenericK t, f ~ RepK t, forall p. FoldDT t c p f (a :&&: as), TysSatisfy c (a :&&: as), SForLoT as)
     => Algebra t c DataFirst -> t a :@@: as -> a
foldAlgebraFirst alg = unDataFirst . foldAlgebra @_ @t @c @DataFirst @_ @(a :&&: as) alg

foldAlgebraFirst0
  :: forall (t :: * -> *) c a r f.
     ( GenericK t, f ~ RepK t, forall p. FoldDT t (c :&&&: Trivial) p f (a :&&: LoT0), c a )
     => Algebra t (c :&&&: Trivial) DataFirst -> t a -> a
foldAlgebraFirst0 alg = unDataFirst . foldAlgebra @_ @t @(c :&&&: Trivial) @DataFirst @_ @(a :&&: LoT0) alg

-- you would like to have
-- fmapG :: (forall tys. TySatisfy c tys => f tys -> g tys) -> Algebra t c f -> Algebra t c g
-- tupleG :: Algebra t c f -> Algebra t d f -> Algebra t (Combine c d) (f :*: g)
-- 

coolFmap :: (forall tys. TysSatisfy c tys => f tys -> g tys) -> Algebra t c f -> Algebra t c g
coolFmap f (Alg (Proxy :: Proxy x) v r) = Alg (Proxy @x) v (f . r)

instance Functor (AlgebraConst t c) where
  fmap :: forall a b. (a -> b) -> AlgebraConst t c a -> AlgebraConst t c b
  fmap f (AlgebraConst (Alg (Proxy :: Proxy x) v r))
    = AlgebraConst $ Alg (Proxy @x) v (Const . f . unConst . r)
instance (f ~ RepK t, forall tys. UnitDT t f tys, forall r s tys. TupleDT t r s f tys)
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

data Algebra (t :: k) (c :: ConstraintsFor k) (r :: LoT k -> *) where
  Alg :: Proxy x
      -> (forall tys. (TysSatisfy c tys, SForLoT tys) => Algebra' t x tys)
      -> (forall tys. (TysSatisfy c tys, SForLoT tys) => x tys -> r tys)
      -> Algebra t c r

type Algebra' t r tys = AlgebraDT t r (RepK t) tys
type FoldK t c r tys = (GenericK t, FoldDT t c r (RepK t) tys)

foldAlgebra :: forall k (t :: k) c r f tys.
               ( GenericK t, f ~ RepK t, forall p. FoldDT t c p f tys
               , TysSatisfy c tys, SForLoT tys )
            => Algebra t c r -> t :@@: tys -> r tys
foldAlgebra (Alg (Proxy :: Proxy x) v r) x = r (foldG @k @t @c @x @tys v x)

foldG :: forall k (t :: k) c r tys. (FoldK t c r tys, TysSatisfy c tys, SForLoT tys)
      => (forall bop. (TysSatisfy c bop, SForLoT bop) => Algebra' t r bop)
      -> t :@@: tys -> r tys
foldG alg x = foldDT @_ @t @c @r @(RepK t) @tys alg alg (fromK @k @t x)

class FoldDT (t :: k) (c :: ConstraintsFor k)
             (r :: LoT k -> *) (f :: LoT k -> *) (tys :: LoT k) where
  type AlgebraDT t r f :: LoT k -> *
  foldDT :: (forall bop. (TysSatisfy c bop, SForLoT bop) => Algebra' t r bop)
         -> AlgebraDT t r f tys -> f tys -> r tys
class UnitDT (t :: k) (f :: LoT k -> *) (tys :: LoT k) where
  unitDT :: AlgebraDT t (Const ()) f tys
class UnitDT t f tys
      => TupleDT (t :: k) (r :: LoT k -> *) (s :: LoT k -> *) (f :: LoT k -> *) (tys :: LoT k) where
  tupleDT :: AlgebraDT t r f tys
          -> AlgebraDT t s f tys
          -> AlgebraDT t (r :*: s) f tys

instance ( FoldB t c r r f tys, FoldDT t c r g tys )
         => FoldDT t c r (f :+: g) tys where
  type AlgebraDT t r (f :+: g) = AlgebraB t r r f :*: AlgebraDT t r g
  foldDT recf (fx :*: _) (L1 x) = foldB  @_ @_ @t @c @r @r @f @tys recf fx x
  foldDT recf (_ :*: fy) (R1 y) = foldDT @_ @t @c @r @g @tys recf fy y
instance ( UnitB t f tys, UnitDT t g tys )
         => UnitDT t (f :+: g) tys where
  unitDT = unitB @_ @_ @t @f @tys :*: unitDT @_ @t @g @tys
instance ( TupleB t r r s s f tys, TupleDT t r s g tys )
         => TupleDT t r s (f :+: g) tys where
  tupleDT (x :*: y) (a :*: b)
    = tupleB @_ @_ @t @r @r @s @s @f @tys x a :*: tupleDT @_ @t @r @s @g @tys y b 

-- Fallback, copied to remove ovelapping
instance FoldDT t c r U1 tys where
  type AlgebraDT t r U1 = AlgebraB t r r U1
  foldDT recf x = foldB @_ @_ @t @c @r @r @U1 @tys recf x
instance UnitDT t U1 tys where
  unitDT = unitB @_ @_ @t @U1 @tys
instance TupleDT t r s U1 tys where
  tupleDT x a = tupleB @_ @_ @t @r @r @s @s @U1 @tys x a

instance FoldB t c r r (Field x) tys
         => FoldDT t c r (Field x) tys where
  type AlgebraDT t r (Field x) = AlgebraB t r r (Field x)
  foldDT recf x = foldB @_ @_ @t @c @r @r @(Field x) @tys recf x
instance UnitB t (Field x) tys
         => UnitDT t (Field x) tys where
  unitDT = unitB @_ @_ @t @(Field x) @tys
instance TupleB t r r s s (Field x) tys
         => TupleDT t r s(Field x) tys where
  tupleDT x a = tupleB @_ @_ @t @r @r @s @s @(Field x) @tys x a

instance FoldB t c r r (Field x :*: y) tys
         => FoldDT t c r (Field x :*: y) tys where
  type AlgebraDT t r (Field x :*: y) = AlgebraB t r r (Field x :*: y)
  foldDT recf x = foldB @_ @_ @t @c @r @r @(Field x :*: y) @tys recf x
instance UnitB t (Field x :*: y) tys
         => UnitDT t (Field x :*: y) tys where
  unitDT = unitB @_ @_ @t @(Field x :*: y) @tys
instance TupleB t r r s s (Field x :*: y) tys
         => TupleDT t r s (Field x :*: y) tys where
  tupleDT x a = tupleB @_ @_ @t @r @r @s @s @(Field x :*: y) @tys x a

class FoldB (t :: l) (c :: ConstraintsFor l)
            (r :: LoT l -> *) (newr :: LoT k -> *)
            (f :: LoT k -> *) (tys :: LoT k) where
  type AlgebraB t r newr f :: LoT k -> *
  foldB :: (forall bop. (TysSatisfy c bop, SForLoT bop) => Algebra' t r bop)
        -> AlgebraB t r newr f tys -> f tys -> newr tys
class UnitB (t :: l) (f :: LoT k -> *) (tys :: LoT k) where
  unitB :: AlgebraB t (Const ()) (Const ()) f tys
class UnitB t f tys
      => TupleB (t :: l) (r :: LoT l -> *) (newr :: LoT k -> *)
                         (s :: LoT l -> *) (news :: LoT k -> *)
                         (f :: LoT k -> *) (tys :: LoT k) where
  tupleB :: AlgebraB t r newr f tys
         -> AlgebraB t s news f tys
         -> AlgebraB t (r :*: s) (newr :*: news) f tys

infixr 5 :~>:
newtype (:~>:) (f :: LoT k -> *) (g :: LoT k -> *) (tys :: LoT k) where
  OneArg :: (f tys -> g tys) -> (f :~>: g) tys

instance FoldB t c r newr U1 tys where
  type AlgebraB t r newr U1 = newr
  foldB _ r U1 = r
instance UnitB t U1 tys where
  unitB = Const ()
instance TupleB t r newr s news U1 tys where
  tupleB x a = x :*: a

instance ( FoldF t c r x (Igualicos x (ElReemplazador t r x)) tys, FoldB t c r newr y tys )
         => FoldB t c r newr (Field x :*: y) tys where
  type AlgebraB t r newr (Field x :*: y) = Field (ElReemplazador t r x) :~>: AlgebraB t r newr y
  foldB recf (OneArg f) (v :*: w)
    = foldB @_ @_ @t @c @r @newr @y recf
            (f (foldF @_ @_ @t @c @r @x @(Igualicos x (ElReemplazador t r x)) @tys recf v)) w
instance ( UnitB t y tys )
         => UnitB t (Field x :*: y) tys where
  unitB = OneArg (\_ -> unitB @_ @_ @t @y @tys)
instance ( TupleB t r newr s news y tys
         , UntupleF t x (Igualicos x (ElReemplazador t (Const ()) x)) tys )
         => TupleB t r newr s news (Field x :*: y) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x 
                         @(Igualicos x (ElReemplazador t (Const ()) x)) @tys
                         @r @s v
        in tupleB @_ @_ @t @r @newr @s @news @y @tys (x vx) (a va)

instance ( FoldF t c r x (Igualicos x (ElReemplazador t r x)) tys )
         => FoldB t c r newr (Field x) tys where
  type AlgebraB t r newr (Field x) = Field (ElReemplazador t r x) :~>: newr
  foldB recf (OneArg f) v
    = f (foldF @_ @_ @t @c @r @x @(Igualicos x (ElReemplazador t r x)) @tys recf v)
instance UnitB t (Field x) tys where
  unitB = OneArg (\_ -> Const ())
instance UntupleF t x (Igualicos x (ElReemplazador t (Const ()) x)) tys
         => TupleB t r newr s news (Field x) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x 
                         @(Igualicos x (ElReemplazador t (Const ()) x)) @tys
                         @r @s v
        in x vx :*: a va

class FoldF (t :: l) (c :: ConstraintsFor l) 
            (r :: LoT l -> *) (x :: Atom k (*))
            (igualicos :: Bool) (tys :: LoT k) where
  foldF :: (forall bop. (TysSatisfy c bop, SForLoT bop) => Algebra' t r bop)
        -> Field x tys -> Field (ElReemplazador t r x) tys
class UntupleF (t :: l) (x :: Atom k (*)) (igualicos :: Bool) (tys :: LoT k) where
  untupleF :: Field (ElReemplazador t (r :*: s) x) tys
           -> (Field (ElReemplazador t r x) tys, Field (ElReemplazador t s x) tys)

instance (x ~ ElReemplazador t r x) => FoldF t c r x 'True tys where
  foldF _ x = x
instance ( forall l. x ~ ElReemplazador t l x )
         => UntupleF t x 'True tys where
  untupleF x = (unsafeCoerce x, unsafeCoerce x)

instance ( FoldK t c r LoT0, TysSatisfy c LoT0 )
         => FoldF t c r (Kon t) 'False LoT0 where
  foldF recf (Field x) = Field $ foldG @_ @t @c @r @LoT0 recf x
-- For now we do not allow weird recursion
instance ( FoldK t c r (LoT1 (Interpret a (LoT1 x)))
         , a ~ ElReemplazador t r a
         , TysSatisfy c (LoT1 (Interpret a (LoT1 x))) )
         => FoldF t c r (Kon t :@: a) 'False (LoT1 x) where
  foldF recf (Field x) = Field $ foldG @_ @t @c @r @(LoT1 (Interpret a (LoT1 x))) recf x
instance ( FoldK t c r (LoT2 (Interpret a (LoT2 x y)) (Interpret b (LoT2 x y)))
         , a ~ ElReemplazador t r a, b ~ ElReemplazador t r b
         , TysSatisfy c (LoT2 (Interpret a (LoT2 x y)) (Interpret b (LoT2 x y))) )
         => FoldF t c r (Kon t :@: a :@: b) 'False (LoT2 x y) where
  foldF recf (Field x) = Field $ foldG @_ @t @c @r @(LoT2 (Interpret a (LoT2 x y)) (Interpret b (LoT2 x y))) recf x

instance UntupleF t (Kon t) 'False LoT0 where
  untupleF (Field (a :*: b)) = (Field a, Field b)
instance ( forall l. a ~ ElReemplazador t (Const l) a )
         => UntupleF t (Kon t :@: a) 'False (LoT1 x) where
  untupleF (Field (a :*: b)) = (Field a, Field b)
instance ( forall l. a ~ ElReemplazador t (Const l) a, forall l. b ~ ElReemplazador t (Const l) b )
         => UntupleF t (Kon t :@: a :@: b) 'False (LoT2 x y) where
  untupleF (Field (a :*: b)) = (Field a, Field b)

type family ElReemplazador (t :: l) (r :: LoT l -> *) (a :: Atom d k) :: Atom d k where
  ElReemplazador t r (Kon t) = Kon r :@: Kon LoT0
  ElReemplazador t r (Kon t :@: x) = Kon r :@: ((:&&:) :$: x :@: Kon LoT0)
  ElReemplazador t r (Kon t :@: x :@: y) = Kon r :@: ((:&&:) :$: x :@: ((:&&:) :$: y :@: Kon LoT0))
  -- ElReemplazador t r (Kon t :@: x :@: y :@: z) = Kon r :@: x :@: y :@: z
  -- ElReemplazador t r (Kon t :@: x :@: y :@: z :@: u) = Kon r :@: x :@: y :@: z :@: u
  ElReemplazador t r (Kon k) = Kon k
  ElReemplazador t r (Var v) = Var v
  ElReemplazador t r (f :@: x) = ElReemplazador t r f :@: ElReemplazador t r x
  ElReemplazador t r (c :&: d) = ElReemplazador t r c :&: ElReemplazador t r d
  ElReemplazador t r (ForAll x) = ForAll (ElReemplazador t r x)
  ElReemplazador t r (c :=>>: x) = ElReemplazador t r c :=>>: ElReemplazador t r x

type family Igualicos (a :: k) (b :: k) :: Bool where
  Igualicos a a = 'True
  Igualicos a b = 'False