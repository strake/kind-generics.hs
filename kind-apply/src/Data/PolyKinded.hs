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
module Data.PolyKinded (
  -- * Lists of types and application
  LoT(..), (:@@:)
  -- * Splitting types
, SplitF, Nat(..), TyEnv(..), SplitN
) where

infixr 5 :&&:
-- | @LoT k@ represents a list of types which can be applied
-- to a data type of kind @k@.
data LoT k where
  -- | Empty list of types.
  LoT0    ::                LoT (*)
  -- | Cons a type with a list of types.
  (:&&:)  :: k -> LoT ks -> LoT (k -> ks)

-- | Apply a list of types to a type constructor.
--
-- >>> :kind! Either :@@: (Int :&&: Bool :&&: LoT0)
-- Either Int Bool :: *
type family (f :: k) :@@: (tys :: LoT k) :: * where
  f :@@: 'LoT0        = f
  f :@@: (a ':&&: as) = f a :@@: as

-- | Split a type @t@ until the constructor @f@ is found.
--
-- >>> :kind! SplitF (Either Int Bool) Either
-- Int :&&: Bool :&&: LoT0 :: LoT (* -> * -> *)
-- >>> :kind! SplitF (Either Int Bool) (Either Int)
-- Bool :&&: LoT0 :: LoT (* -> *)
type SplitF (t :: d) (f :: k) = SplitF' t f 'LoT0
type family SplitF' (t :: d) (f :: k) (p :: LoT l) :: LoT k where
  SplitF' f     f acc = acc
  SplitF' (t a) f acc = SplitF' t f (a ':&&: acc)

-- | Simple natural numbers.
data Nat = Z | S Nat

-- | A type constructor and a list of types that can be applied to it.
data TyEnv where
  TyEnv :: forall k. k -> LoT k -> TyEnv

-- | Split a type @t@ until its list of types has length @n@.
--
-- >>> :kind! SplitN (Either Int Bool) (S (S Z))
-- TyEnv Either (Int :&&: Bool :&&: LoT0) :: TyEnv
-- >>> :kind! SplitF (Either Int Bool) (S Z)
-- TyEnv (Either Int) (Bool :&&: LoT0) :: TyEnv
type family SplitN (n :: Nat) t :: TyEnv where 
  SplitN n t = SplitN' n t 'LoT0
type family SplitN' (n :: Nat) (t :: d) (p :: LoT d) :: TyEnv where
  SplitN' 'Z     t            acc = 'TyEnv t acc
  SplitN' ('S n) (t (a :: l)) acc = SplitN' n t (a ':&&: acc)