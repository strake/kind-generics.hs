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
module Generics.Kind.Algebras where

import Generics.Kind
import Generics.Kind.Examples
import Data.Proxy
import Unsafe.Coerce
import GHC.Base (liftA2)

newtype Const x tys = Const { unConst :: x }
newtype AlgebraConst (t :: k) (r :: *) = AlgebraConst { unAC :: Algebra t (Const r) }

maybeAlg :: AlgebraConst Maybe Bool
maybeAlg = AlgebraConst $ Alg (Const False :*: (OneArg (\_ -> Const True))) id

foldAlgebraConst
  :: forall k (t :: k) r f tys.
     (GenericK t tys, f ~ RepK t, forall p. FoldDT t p f tys)
     => AlgebraConst t r -> t :@@: tys -> r
foldAlgebraConst (AlgebraConst alg) = unConst . foldAlgebra @_ @t @(Const r) @_ @tys alg

instance Functor (AlgebraConst t) where
  fmap f (AlgebraConst (Alg v r)) = AlgebraConst $ Alg v (Const . f . unConst . r)
instance forall f t. (f ~ RepK t, forall tys. UnitDT t f tys, forall r s tys. TupleDT t r s f tys)
         => Applicative (AlgebraConst t) where
  pure x = AlgebraConst $ Alg (unitDT @_ @t @(RepK t))
                              (\(_ :: Const () lys) -> Const x)
  (<*>) :: forall a b. AlgebraConst t (a -> b) -> AlgebraConst t a -> AlgebraConst t b
  (AlgebraConst (Alg fv (fr :: forall tys. fx tys -> Const (a -> b) tys)))
    <*> (AlgebraConst (Alg xv (xr :: forall tys. xx tys -> Const a tys)))
         = AlgebraConst
         $ Alg @t @(fx :*: xx)
               (tupleDT @_ @t @fx @xx @(RepK t) fv xv)
               (\(f :*: x) -> Const (unConst (fr f) $ unConst (xr x)))

data Algebra (t :: k) (r :: LoT k -> *) where
  Alg :: (forall tys. Algebra' t x tys) -> (forall tys. x tys -> r tys) -> Algebra t r

type Algebra' t r tys = AlgebraDT t r (RepK t) tys
type FoldK t r tys = (GenericK t tys, FoldDT t r (RepK t) tys)

foldAlgebra :: forall k (t :: k) r f tys.
               (GenericK t tys, f ~ RepK t, forall p. FoldDT t p f tys)
            => Algebra t r -> t :@@: tys -> r tys
foldAlgebra (Alg v (r :: x tys -> r tys)) x = r (foldG @k @t @x @tys v x)

foldG :: forall k (t :: k) r tys. (FoldK t r tys)
      => (forall bop. Algebra' t r bop)
      -> t :@@: tys -> r tys
foldG alg x = foldDT @_ @t @r @(RepK t) @tys alg alg (fromK @k @t x)

class FoldDT (t :: k) (r :: LoT k -> *) (f :: LoT k -> *) (tys :: LoT k) where
  type AlgebraDT t r f :: LoT k -> *
  foldDT :: (forall bop. Algebra' t r bop)
         -> AlgebraDT t r f tys -> f tys -> r tys
class UnitDT (t :: k) (f :: LoT k -> *) (tys :: LoT k) where
  unitDT :: AlgebraDT t (Const ()) f tys
class UnitDT t f tys
      => TupleDT (t :: k) (r :: LoT k -> *) (s :: LoT k -> *) (f :: LoT k -> *) (tys :: LoT k) where
  tupleDT :: AlgebraDT t r f tys
          -> AlgebraDT t s f tys
          -> AlgebraDT t (r :*: s) f tys

instance forall t r f g tys. 
         ( FoldB t r r f tys, FoldDT t r g tys )
         => FoldDT t r (f :+: g) tys where
  type AlgebraDT t r (f :+: g) = AlgebraB t r r f :*: AlgebraDT t r g
  foldDT recf (fx :*: _) (L1 x) = foldB  @_ @_ @t @r @r @f @tys recf fx x
  foldDT recf (_ :*: fy) (R1 y) = foldDT @_ @t @r @g @tys recf fy y
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
instance forall t r tys. FoldDT t r U1 tys where
  type AlgebraDT t r U1 = AlgebraB t r r U1
  foldDT recf x = foldB @_ @_ @t @r @r @U1 @tys recf x
instance forall t tys. UnitDT t U1 tys where
  unitDT = unitB @_ @_ @t @U1 @tys
instance forall t r s tys. TupleDT t r s U1 tys where
  tupleDT x a = tupleB @_ @_ @t @r @r @s @s @U1 @tys x a

instance forall t r x tys. 
         FoldB t r r (Field x) tys
         => FoldDT t r (Field x) tys where
  type AlgebraDT t r (Field x) = AlgebraB t r r (Field x)
  foldDT recf x = foldB @_ @_ @t @r @r @(Field x) @tys recf x
instance forall t x tys.
         UnitB t (Field x) tys
         => UnitDT t (Field x) tys where
  unitDT = unitB @_ @_ @t @(Field x) @tys
instance forall t r s x tys.
         TupleB t r r s s (Field x) tys
         => TupleDT t r s(Field x) tys where
  tupleDT x a = tupleB @_ @_ @t @r @r @s @s @(Field x) @tys x a

instance forall t r x y tys. 
         FoldB t r r (Field x :*: y) tys
         => FoldDT t r (Field x :*: y) tys where
  type AlgebraDT t r (Field x :*: y) = AlgebraB t r r (Field x :*: y)
  foldDT recf x = foldB @_ @_ @t @r @r @(Field x :*: y) @tys recf x
instance forall t x y tys.
         UnitB t (Field x :*: y) tys
         => UnitDT t (Field x :*: y) tys where
  unitDT = unitB @_ @_ @t @(Field x :*: y) @tys
instance forall t r s x y tys.
         TupleB t r r s s (Field x :*: y) tys
         => TupleDT t r s (Field x :*: y) tys where
  tupleDT x a = tupleB @_ @_ @t @r @r @s @s @(Field x :*: y) @tys x a

class FoldB (t :: l) (r :: LoT l -> *) (newr :: LoT k -> *)
                     (f :: LoT k -> *) (tys :: LoT k) where
  type AlgebraB t r newr f :: LoT k -> *
  foldB :: (forall bop. Algebra' t r bop)
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

newtype (:~>:) (f :: LoT k -> *) (g :: LoT k -> *) (tys :: LoT k) where
  OneArg :: (f tys -> g tys) -> (f :~>: g) tys

instance FoldB t r newr U1 tys where
  type AlgebraB t r newr U1 = newr
  foldB _ r U1 = r
instance UnitB t U1 tys where
  unitB = Const ()
instance TupleB t r newr s news U1 tys where
  tupleB x a = x :*: a

instance forall t r newr x y tys. 
         ( FoldF t r x (Igualicos x (ElReemplazador t r x)) tys, FoldB t r newr y tys )
         => FoldB t r newr (Field x :*: y) tys where
  type AlgebraB t r newr (Field x :*: y) = Field (ElReemplazador t r x) :~>: AlgebraB t r newr y
  foldB recf (OneArg f) (v :*: w)
    = foldB @_ @_ @t @r @newr @y recf
            (f (foldF @_ @_ @t @r @x @(Igualicos x (ElReemplazador t r x)) @tys recf v)) w
instance forall t x y tys. ( UnitB t y tys )
         => UnitB t (Field x :*: y) tys where
  unitB = OneArg (\_ -> unitB @_ @_ @t @y @tys)
instance forall t r newr s news x y tys.
         ( TupleB t r newr s news y tys
         , UntupleF t x (Igualicos x (ElReemplazador t (Const ()) x)) tys )
         => TupleB t r newr s news (Field x :*: y) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x 
                         @(Igualicos x (ElReemplazador t (Const ()) x)) @tys
                         @r @s v
        in tupleB @_ @_ @t @r @newr @s @news @y @tys (x vx) (a va)

instance forall t r newr x tys. 
         ( FoldF t r x (Igualicos x (ElReemplazador t r x)) tys )
         => FoldB t r newr (Field x) tys where
  type AlgebraB t r newr (Field x) = Field (ElReemplazador t r x) :~>: newr
  foldB recf (OneArg f) v
    = f (foldF @_ @_ @t @r @x @(Igualicos x (ElReemplazador t r x)) @tys recf v)
instance forall t x tys. UnitB t (Field x) tys where
  unitB = OneArg (\_ -> Const ())
instance forall t r newr s news x tys.
         UntupleF t x (Igualicos x (ElReemplazador t (Const ()) x)) tys
         => TupleB t r newr s news (Field x) tys where
  tupleB (OneArg x) (OneArg a)
    = OneArg $ \v ->
        let (vx, va)
              = untupleF @_ @_ @t @x 
                         @(Igualicos x (ElReemplazador t (Const ()) x)) @tys
                         @r @s v
        in x vx :*: a va

class FoldF (t :: l) (r :: LoT l -> *) (x :: Atom k (*)) (igualicos :: Bool) (tys :: LoT k) where
  foldF :: (forall bop. Algebra' t r bop)
        -> Field x tys -> Field (ElReemplazador t r x) tys
class UntupleF (t :: l) (x :: Atom k (*)) (igualicos :: Bool) (tys :: LoT k) where
  untupleF :: Field (ElReemplazador t (r :*: s) x) tys
           -> (Field (ElReemplazador t r x) tys, Field (ElReemplazador t s x) tys)

instance (x ~ ElReemplazador t r x) => FoldF t r x 'True tys where
  foldF _ x = x

instance ( forall l. x ~ ElReemplazador t l x )
         => UntupleF t x 'True tys where
  untupleF x = (unsafeCoerce x, unsafeCoerce x)

instance ( FoldK t r LoT0 )
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

{-
instance ApplF t (Kon t) 'False LoT0 where
  untupleF (Field (Const (a, b))) = (Field (Const a), Field (Const b))
instance ( forall l. a ~ ElReemplazador t (Const l) a )
         => ApplF t (Kon t :@: a) 'False (LoT1 x) where
  untupleF (Field (Const (a, b))) = (Field (Const a), Field (Const b))
instance ( forall l. a ~ ElReemplazador t (Const l) a, forall l. b ~ ElReemplazador t (Const l) b )
         => ApplF t (Kon t :@: a :@: b) 'False (LoT2 x y) where
  untupleF (Field (Const (a, b))) = (Field (Const a), Field (Const b))
-}

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