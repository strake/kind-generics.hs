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

type SplitF (t :: d) (f :: k) = SplitF' t f 'LoT0
type family SplitF' (t :: d) (f :: k) (p :: LoT l) :: LoT k where
  SplitF' f     f acc = acc
  SplitF' (t a) f acc = SplitF' t f (a ':&&: acc)

data Nat = Z | S Nat

data TyEnv where
  TyEnv :: forall k. k -> LoT k -> TyEnv

type family SplitN (n :: Nat) t :: TyEnv where 
  SplitN n t = SplitN' n t 'LoT0
type family SplitN' (n :: Nat) (t :: d) (p :: LoT d) :: TyEnv where
  SplitN' 'Z     t            acc = 'TyEnv t acc
  SplitN' ('S n) (t (a :: l)) acc = SplitN' n t (a ':&&: acc)

class (x ~ SplitF t f, t ~ (f :@@: x))
      => Split t (f :: k) (x :: LoT k) | t -> k f x