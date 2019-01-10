{-# language DataKinds      #-}
{-# language TypeFamilies   #-}
{-# language PolyKinds      #-}
{-# language KindSignatures #-}
{-# language TypeOperators  #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language AllowAmbiguousTypes   #-}
{-# language ScopedTypeVariables   #-}
{-# language TypeApplications      #-}
{-# language UndecidableInstances  #-}
module Generics.Kind.Algebras where

import Data.PolyKinded.Atom
import Generics.Kind
import Data.Proxy

{-
-- Replace appearances of `t` by `r`
type family FoldAtom (r :: *) (t :: l) (a :: Atom d k) :: Atom d k where
  FoldAtom r t (Var v)     = Var v
  FoldAtom r t (c :&: d)   = FoldAtom r t c :&: FoldAtom r t d
  FoldAtom r t (ForAll s)  = ForAll (FoldAtom r t s)
  FoldAtom r t (c :=>>: s) = FoldAtom r t c :=>>: FoldAtom r t s
  -- Match with the searched one
  FoldAtom r t (Kon t) = Kon r
  FoldAtom r t (Kon t :@: x) = Kon r
  FoldAtom r t (Kon t :@: x :@: y) = Kon r
  FoldAtom r t (Kon t :@: x :@: y :@: z) = Kon r
  FoldAtom r t (Kon t :@: x :@: y :@: z :@: u) = Kon r
  FoldAtom r t (Kon t :@: x :@: y :@: z :@: u :@: v) = Kon r
  -- Otherwise, keep going
  FoldAtom r t (Kon k)   = Kon k
  FoldAtom r t (f :@: x) = FoldAtom r t f :@: FoldAtom r t x

type family FoldConstructor' (r :: *) (t :: l) (c :: LoT k -> *) :: Atom k (*) where
  FoldConstructor r t (M1 i p x) = FoldConstructor' r t x
  FoldConstructor r t U1 = Kon r
  FoldConstructor r t (Field x) = (->) :$: FoldAtom r t x :@: Kon r
  FoldConstructor r t (Field x :*: y) = (->) :$: FoldAtom r t x :@: FoldConstructor' r t y

type family FoldConstructor (r :: *) (t :: l) (c :: LoT k -> *) :: LoT k -> * where
  FoldConstructor r t (M1 i p x)   = FoldConstructor r t x
  FoldConstructor r t (c :=>: s)   = c :=>: FoldConstructor r t s
  FoldConstructor r t (Exists k s) = Exists k (FoldConstructor r t s)
  FoldConstructor r t other        = Field (FoldConstructor' r t other)

type family FoldDataType (r :: *) (t :: l) (c :: LoT k -> *) :: LoT k -> * where
  FoldDataType r t (M1 i p x) = FoldDataType r t x
  FoldDataType r t (x :+: xs) = FoldConstructor r t x :*: FoldDataType r t xs
  FoldDataType r t other      = FoldConstructor r t other
-}

class FoldDataType (r :: *) (t :: l) (c :: LoT k -> *) where
  type Algebra r t c :: LoT k -> *
  foldDT :: Algebra r t c tys -> c tys -> r

class FoldConstructor (r :: *) (t :: l) (c :: LoT k -> *) where
  type AlgebraC r t c :: LoT k -> *
  foldC :: AlgebraC r t c tys -> c tys -> r

class FoldConstructor' (r :: *) (t :: l) (c :: LoT k -> *) where
  type AlgebraC' r t c :: Atom k (*)
  foldC' :: Field (AlgebraC' r t c) tys -> c tys -> r

instance forall r t c i p. FoldDataType r t c
         => FoldDataType r t (M1 i p c) where
  type Algebra r t (M1 i p c) = Algebra r t c
  foldDT f (M1 x) = foldDT @_ @_ @r @t @c f x

instance forall r t x y. (FoldConstructor r t x, FoldDataType r t y)
         => FoldDataType r t (x :+: y) where
  type Algebra r t (x :+: y) = AlgebraC r t x :*: Algebra r t y
  foldDT (f :*: _) (L1 x) = foldC  @_ @_ @r @t @x f x
  foldDT (_ :*: g) (R1 y) = foldDT @_ @_ @r @t @y g y

-- Rest of cases, fall back

instance forall r t. FoldConstructor r t U1
         => FoldDataType r t U1 where
  type Algebra r t U1 = AlgebraC r t U1
  foldDT f x = foldC @_ @_ @r @t @U1 f x

instance forall r t c s. FoldConstructor r t (c :=>: s)
         => FoldDataType r t (c :=>: s) where
  type Algebra r t (c :=>: s) = AlgebraC r t (c :=>: s)
  foldDT f x = foldC @_ @_ @r @t @(c :=>: s) f x

{-
foldG :: Proxy t -> FoldDataType r t p tys -> p tys -> r
foldG p f (M1 x) = foldG p f x
  where foldC :: Proxy t -> FoldConstructor r t p tys -> p tys -> r
        foldC = undefined
-}