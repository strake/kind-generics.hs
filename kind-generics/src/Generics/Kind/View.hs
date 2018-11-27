{-# language TypeOperators         #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleContexts      #-}
{-# language FlexibleInstances     #-}
{-# language DataKinds             #-}
{-# language PolyKinds             #-}
{-# language TypeFamilies          #-}
{-# language UndecidableInstances  #-}
{-# language QuantifiedConstraints #-}
{-# language TypeApplications      #-}
{-# language ScopedTypeVariables   #-}
module Generics.Kind.View where

import Generics.Kind

{-
type family SubstRep (f :: LoT (t -> k) -> *) (x :: t) :: LoT k -> * where
  SubstRep U1         x = U1
  SubstRep (f :+: g)  x = (SubstRep f x) :+: (SubstRep g x)
  SubstRep (f :*: g)  x = (SubstRep f x) :*: (SubstRep g x)
  SubstRep (M1 i c f) x = M1 i c (SubstRep f x)
  SubstRep (f :=>: g) x = (SubstAtom f x) :=>: (SubstRep g x)
-}

class SubstRep' (f :: LoT (t -> k) -> *) (x :: t) (xs :: LoT k) where
  type family SubstRep f x :: LoT k -> *
  substRep   :: f (x ':&&: xs) -> SubstRep f x xs
  unsubstRep :: SubstRep f x xs -> f (x ':&&: xs)

instance SubstRep' U1 x xs where
  type SubstRep U1 x = U1
  substRep   U1 = U1
  unsubstRep U1 = U1

instance (SubstRep' f x xs, SubstRep' g x xs) => SubstRep' (f :+: g) x xs where
  type SubstRep (f :+: g)  x = (SubstRep f x) :+: (SubstRep g x)
  substRep   (L1 x) = L1 (substRep   x)
  substRep   (R1 x) = R1 (substRep   x)
  unsubstRep (L1 x) = L1 (unsubstRep x)
  unsubstRep (R1 x) = R1 (unsubstRep x)

instance (SubstRep' f x xs, SubstRep' g x xs) => SubstRep' (f :*: g) x xs where
  type SubstRep (f :*: g) x = (SubstRep f x) :*: (SubstRep g x)
  substRep   (x :*: y) = substRep   x :*: substRep   y
  unsubstRep (x :*: y) = unsubstRep x :*: unsubstRep y

instance SubstRep' f x xs => SubstRep' (M1 i c f) x xs where
  type SubstRep (M1 i c f) x = M1 i c (SubstRep f x)
  substRep   (M1 x) = M1 (substRep   x)
  unsubstRep (M1 x) = M1 (unsubstRep x)

instance (Ty (SubstAtom c x) xs, Ty c (x ':&&: xs), SubstRep' f x xs)
         => SubstRep' (c :=>: f) x xs where
  type SubstRep (c :=>: f) x = (SubstAtom c x) :=>: (SubstRep f x)
  substRep   (C x) = C (substRep   x)
  unsubstRep (C x) = C (unsubstRep x)

instance (Ty (SubstAtom t x) xs ~ Ty t (x ':&&: xs))
         => SubstRep' (F t) x xs where
  type SubstRep (F t) x = F (SubstAtom t x)
  substRep   (F x) = F x
  unsubstRep (F x) = F x

type family SubstAtom (f :: Atom (t -> k) d) (x :: t) :: Atom k d where
  SubstAtom ('Var 'VZ)     x = 'Kon x
  SubstAtom ('Var ('VS v)) x = 'Var v
  SubstAtom ('Kon t)       x = 'Kon t
  SubstAtom (t1 ':@: t2)   x = (SubstAtom t1 x) ':@: (SubstAtom t2 x)

instance forall (f :: k -> ks) x xs.
         (GenericK f (x ':&&: xs), SubstRep' (RepK f) x xs)
         => GenericK (f x) xs where
  type RepK (f x) = SubstRep (RepK f) x
  fromK = substRep . fromK @_ @f @(x ':&&: xs)
  toK   = toK @_ @f @(x ':&&: xs) . unsubstRep