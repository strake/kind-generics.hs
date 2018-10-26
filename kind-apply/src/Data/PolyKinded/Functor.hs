{-# language DataKinds              #-}
{-# language PolyKinds              #-}
{-# language GADTs                  #-}
{-# language TypeOperators          #-}
{-# language MultiParamTypeClasses  #-}
{-# language ScopedTypeVariables    #-}
{-# language FunctionalDependencies #-}
{-# language TypeApplications       #-}
{-# language AllowAmbiguousTypes    #-}
{-# language TypeFamilies           #-}
module Data.PolyKinded.Functor where

import Data.PolyKinded

data Variance = Co | Contra | Phantom
type Variances = [Variance]

type family Mapping (v :: Variance) a b where
  Mapping 'Co     a b = a -> b
  Mapping 'Contra a b = b -> a

infixr 5 :^:
data Mappings (v :: Variances) (x :: LoT k) (y :: LoT k) where
  M0    :: Mappings '[] 'LoT0 'LoT0
  (:^:) :: Mapping v a b -> Mappings vs as bs
        -> Mappings (v ': vs) (a ':&&: as) (b ':&&: bs)

class KFunctor (f :: k) (v :: Variances) (as :: LoT k) (bs :: LoT k) | f -> v where
  kfmap :: Mappings v as bs -> f :@@: as -> f :@@: bs

kmapo :: forall t f v as bs. (Break t f as, KFunctor f v as bs)
      => Mappings v as bs -> t -> f :@@: bs
kmapo = kfmap @_ @f