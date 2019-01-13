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

maybeAlg' :: Algebra' Maybe Bool tys
maybeAlg' = Field False :*: (OneArg (\_ -> Field True))

maybeAlg :: Algebra Maybe Bool
maybeAlg = Alg (Field False :*: (OneArg (\_ -> Field True))) id

data Algebra (t :: k) (r :: *) where
  Alg :: (forall tys. Algebra' t x tys) -> (x -> r) -> Algebra t r

instance Functor (Algebra t) where
  fmap f (Alg v r) = Alg v (f . r)

type Algebra' t r tys = AlgebraDT t r (RepK t) tys
type FoldK t r tys = (GenericK t tys, FoldDT t r (RepK t) tys)

foldAlgebra :: forall k (t :: k) r f tys.
               (GenericK t tys, f ~ RepK t, forall p. FoldDT t p f tys)
            => Algebra t r -> t :@@: tys -> r
foldAlgebra (Alg v (r :: x -> r)) x = r (foldG @k @t @x @tys v x)

foldG :: forall k (t :: k) r tys. (FoldK t r tys)
      => (forall bop. Algebra' t r bop)
      -> t :@@: tys -> r
foldG alg x = foldDT @_ @t @r @(RepK t) @tys alg alg (fromK @k @t x)

class FoldDT (t :: k) (r :: *) (f :: LoT k -> *) (tys :: LoT k) where
  type AlgebraDT t r f :: LoT k -> *
  foldDT :: (forall bop. Algebra' t r bop)
         -> AlgebraDT t r f tys -> f tys -> r

instance forall t r f g tys. 
         ( FoldB t r f tys, FoldDT t r g tys )
         => FoldDT t r (f :+: g) tys where
  type AlgebraDT t r (f :+: g) = AlgebraB t r f :*: AlgebraDT t r g
  foldDT recf (fx :*: _) (L1 x) = foldB  @_ @_ @t @r @f @tys recf fx x
  foldDT recf (_ :*: fy) (R1 y) = foldDT @_ @t @r @g @tys recf fy y

-- Fallback, copied to remove ovelapping
instance forall t r tys. FoldDT t r U1 tys where
  type AlgebraDT t r U1 = AlgebraB t r U1
  foldDT recf x = foldB @_ @_ @t @r @U1 @tys recf x

instance forall t r x tys. 
         FoldB t r (Field x) tys
         => FoldDT t r (Field x) tys where
  type AlgebraDT t r (Field x) = AlgebraB t r (Field x)
  foldDT recf x = foldB @_ @_ @t @r @(Field x) @tys recf x

instance forall t r x y tys. 
         FoldB t r (Field x :*: y) tys
         => FoldDT t r (Field x :*: y) tys where
  type AlgebraDT t r (Field x :*: y) = AlgebraB t r (Field x :*: y)
  foldDT recf x = foldB @_ @_ @t @r @(Field x :*: y) @tys recf x

class FoldB (t :: l) (r :: *) (f :: LoT k -> *) (tys :: LoT k) where
  type AlgebraB t r f :: LoT k -> *
  foldB :: (forall bop. Algebra' t r bop)
        -> AlgebraB t r f tys -> f tys -> r

newtype (:~>:) (f :: LoT k -> *) (g :: LoT k -> *) (tys :: LoT k) where
  OneArg :: (f tys -> g tys) -> (f :~>: g) tys

instance FoldB t r U1 tys where
  type AlgebraB t r U1 = Field (Kon r)
  foldB _ (Field r) U1 = r

instance forall t r x y tys. 
         ( FoldF t r x (Igualicos x (ElReemplazador t r x)) tys, FoldB t r y tys )
         => FoldB t r (Field x :*: y) tys where
  type AlgebraB t r (Field x :*: y) = Field (ElReemplazador t r x) :~>: AlgebraB t r y
  foldB recf (OneArg f) (v :*: w)
    = foldB @_ @_ @t @r @y recf
            (f (foldF @_ @_ @t @r @x @(Igualicos x (ElReemplazador t r x)) @tys recf v)) w

instance forall t r x tys. 
         ( FoldF t r x (Igualicos x (ElReemplazador t r x)) tys )
         => FoldB t r (Field x) tys where
  type AlgebraB t r (Field x) = Field (ElReemplazador t r x) :~>: Field (Kon r)
  foldB recf (OneArg f) v
    = unField $ f (foldF @_ @_ @t @r @x @(Igualicos x (ElReemplazador t r x)) @tys recf v)

class FoldF (t :: l) (r :: *) (x :: Atom k (*)) (igualicos :: Bool) (tys :: LoT k) where
  foldF :: (forall bop. Algebra' t r bop)
        -> Field x tys -> Field (ElReemplazador t r x) tys

instance (x ~ ElReemplazador t r x) => FoldF t r x 'True tys where
  foldF _ x = x

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

type family ElReemplazador (t :: l) (r :: *) (a :: Atom d k) :: Atom d k where
  ElReemplazador t r (Kon t) = Kon r
  ElReemplazador t r (Kon t :@: x) = Kon r
  ElReemplazador t r (Kon t :@: x :@: y) = Kon r
  ElReemplazador t r (Kon t :@: x :@: y :@: z) = Kon r
  ElReemplazador t r (Kon t :@: x :@: y :@: z :@: u) = Kon r
  ElReemplazador t r (Kon k) = Kon k
  ElReemplazador t r (Var v) = Var v
  ElReemplazador t r (f :@: x) = ElReemplazador t r f :@: ElReemplazador t r x
  ElReemplazador t r (c :&: d) = ElReemplazador t r c :&: ElReemplazador t r d
  ElReemplazador t r (ForAll x) = ForAll (ElReemplazador t r x)
  ElReemplazador t r (c :=>>: x) = ElReemplazador t r c :=>>: ElReemplazador t r x

type family Igualicos (a :: k) (b :: k) :: Bool where
  Igualicos a a = 'True
  Igualicos a b = 'False