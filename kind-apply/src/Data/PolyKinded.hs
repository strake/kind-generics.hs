{-# language DataKinds       #-}
{-# language TypeOperators   #-}
{-# language GADTs           #-}
{-# language TypeFamilies    #-}
{-# language KindSignatures  #-}
{-# language TypeInType      #-}
{-# language PatternSynonyms #-}
{-# language UndecidableInstances   #-}
{-# language FlexibleContexts       #-}
{-# language ScopedTypeVariables    #-}
{-# language MultiParamTypeClasses  #-}
{-# language FunctionalDependencies #-}
{-# language ConstraintKinds        #-}
module Data.PolyKinded where

infixr 5 :&&:
data LoT k where
  LoT0    ::                LoT (*)
  (:&&:)  :: k -> LoT ks -> LoT (k -> ks)

type family (f :: k) :@@: (tys :: LoT k) :: * where
  f :@@: 'LoT0        = f
  f :@@: (a ':&&: as) = f a :@@: as

type Split (t :: d) (f :: k) = Split' t f 'LoT0
type family Split' (t :: d) (f :: k) (p :: LoT l) :: LoT k where
  Split' f     f acc = acc
  Split' (t a) f acc = Split' t f (a ':&&: acc)

data Nat = Z | S Nat

data TyEnv where
  TyEnv :: forall k. k -> LoT k -> TyEnv

type family SplitAt (n :: Nat) t :: TyEnv where 
  SplitAt n t = SplitAt' n t 'LoT0
type family SplitAt' (n :: Nat) (t :: d) (p :: LoT d) :: TyEnv where
  SplitAt' 'Z     t            acc = 'TyEnv t acc
  SplitAt' ('S n) (t (a :: l)) acc = SplitAt' n t (a ':&&: acc)

class HeadOf (t :: *) (f :: k) | t -> k f where
type Break t f x = (HeadOf t f, x ~ Split t f, t ~ (f :@@: x))