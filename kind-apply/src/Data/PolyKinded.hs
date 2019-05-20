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
  LoT(..), (:@@:), LoT1, LoT2
, HeadLoT, TailLoT
  -- ** Singleton for list of types
, SLoT(..), SForLoT(..), Proxy(..)
  -- * Splitting types
, SplitF, Nat(..), TyEnv(..), SplitN
) where

import Data.Proxy

infixr 5 :&&:
-- | @LoT k@ represents a list of types which can be applied
-- to a data type of kind @k@.
data LoT k where
  -- | Empty list of types.
  LoT0    ::                LoT (*)
  -- | Cons a type with a list of types.
  (:&&:)  :: k -> LoT ks -> LoT (k -> ks)

type LoT1 a = a ':&&: 'LoT0
type LoT2 a b = a ':&&: b ':&&: LoT0

-- | Apply a list of types to a type constructor.
--
-- >>> :kind! Either :@@: (Int :&&: Bool :&&: LoT0)
-- Either Int Bool :: *
type family (f :: k) :@@: (tys :: LoT k) :: * where
  f :@@: _  = f
  f :@@: as = f (HeadLoT as) :@@: (TailLoT as)

-- | Head of a non-empty list of types.
--
-- >>> :kind! HeadLoT (Int :&&: LoT0)
-- Int :: *
type family HeadLoT (tys :: LoT (k -> k')) :: k where
  HeadLoT (a :&&: _) = a

-- | Tail of a non-empty list of types.
--
-- >>> :kind! TailLoT (Int :&&: Bool :&&: LoT0)
-- Bool :&&: LoT0 :: LoT (Type -> Type)
type family TailLoT (tys :: LoT (k -> k')) :: LoT k' where
  TailLoT (_ :&&: as) = as

data SLoT (l :: LoT k) where
  SLoT0 :: SLoT LoT0
  SLoTA :: Proxy t -> SLoT ts -> SLoT (t :&&: ts)

class SForLoT (l :: LoT k) where
  slot :: SLoT l
instance SForLoT LoT0 where
  slot = SLoT0
instance SForLoT ts => SForLoT (t :&&: ts) where
  slot = SLoTA Proxy slot

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