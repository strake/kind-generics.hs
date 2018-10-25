{-# language DataKinds       #-}
{-# language TypeOperators   #-}
{-# language GADTs           #-}
{-# language TypeFamilies    #-}
{-# language KindSignatures  #-}
{-# language TypeInType      #-}
{-# language PatternSynonyms #-}
{-# language UndecidableInstances #-}
{-# language FlexibleContexts     #-}
{-# language ScopedTypeVariables  #-}
module Generics.Kind.ListOfTypes where

import Data.Kind

infixr 5 :&&:
data LoT k where
  LoT0    ::                LoT (*)
  (:&&:)  :: k -> LoT ks -> LoT (k -> ks)

type family (f :: k) :@@: (tys :: LoT k) :: * where
  f :@@: LoT0        = f
  f :@@: (a :&&: as) = f a :@@: as

type family Split (t :: d) (f :: k) :: LoT k where
  Split t f = Split' t f LoT0

type family Split' (t :: d) (f :: k) (p :: LoT l) :: LoT k where
  Split' f     f acc = acc
  Split' (t a) f acc = Split' t f (a :&&: acc)

