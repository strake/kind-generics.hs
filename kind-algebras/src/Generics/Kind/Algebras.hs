{-# language DataKinds      #-}
{-# language TypeFamilies   #-}
{-# language PolyKinds      #-}
{-# language KindSignatures #-}
{-# language TypeOperators  #-}
{-# language GADTs          #-}
{-# language RankNTypes     #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language AllowAmbiguousTypes   #-}
{-# language ScopedTypeVariables   #-}
{-# language TypeApplications      #-}
{-# language UndecidableInstances  #-}
{-# language QuantifiedConstraints #-}
module Generics.Kind.Algebras where

import Data.PolyKinded.Atom
import Generics.Kind
import Data.Proxy

{-
data Algebra (t :: k) (r :: *) (f :: LoT k -> *) (tys :: LoT k) where
  (:|:) :: AlgebraBranch t r f tys -> Algebra t r g tys -> Algebra t r (f :+: g) tys
  F     :: AlgebraBranch t r f tys -> Algebra t r f tys

data AlgebraBranch (t :: l) (r :: *) (f :: LoT k -> *) (tys :: LoT k) where
  U   :: r -> AlgebraBranch t r U1 tys
  R   :: (HasRecPos t f ~ True, Interpret f tys ~ (t :@@: sys))
         => (r -> AlgebraBranch t r g tys)
         -> AlgebraBranch t r (Field f :*: g) tys
  NR  :: (HasRecPos t f ~ False) => (Interpret f tys -> AlgebraBranch t r g tys)
         -> AlgebraBranch t r (Field f :*: g) tys
  RU  :: (HasRecPos t f ~ True)  => (r -> r)
         -> AlgebraBranch t r (Field f) tys
  NRU :: (HasRecPos t f ~ False) => (Interpret f tys -> r)
         -> AlgebraBranch t r (Field f) tys
  E   :: (forall (ty :: k). AlgebraBranch t r f (ty :&&: tys))
         -> AlgebraBranch t r (Exists k f) tys
  C   :: (Interpret c tys => AlgebraBranch t r f tys)
         -> AlgebraBranch t r (c :=>: f) tys

type family HasRecPos (t :: l) (a :: Atom d k) :: Bool where
  HasRecPos t (Kon t) = True
  HasRecPos t (Kon t :@: x) = True
  HasRecPos t (Kon t :@: x :@: y) = True
  HasRecPos t (Kon t :@: x :@: y :@: z) = True
  HasRecPos t (Kon t :@: x :@: y :@: z :@: u) = True
  HasRecPos t (Kon t :@: x :@: y :@: z :@: u :@: v) = True
  -- Other places
  HasRecPos t (Kon k)     = False
  HasRecPos t (f :@: x)   = Or (HasRecPos t f) (HasRecPos t x)
  HasRecPos t (ForAll s)  = HasRecPos t s
  HasRecPos t (c :=>>: s) = HasRecPos t s 

foldG :: forall (f :: k) r tys. (forall sys. GenericK f sys)
         => Algebra f r (RepK f) tys -> f :@@: tys -> r
foldG alg = undefined
  where foldC :: forall g. AlgebraBranch f r g tys -> g tys -> r
        foldC (U r) U1 = r
        foldC (R f) (Field x :*: y) = foldC (f (foldG alg x)) y
        foldC (NR f) (Field x :*: y) = foldC (f x) y
-}