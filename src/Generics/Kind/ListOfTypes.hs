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

{-
data (f :: k) :@@: (tys :: LoT k) :: * where
  A0  :: { unA0  :: f } -> f :@@: LoT0
  Arg :: { unArg :: f t :@@: ts } -> f :@@: (t :&&: ts)

pattern A1 x = Arg (A0 x)
pattern A2 x = Arg (A1 x)
pattern A3 x = Arg (A2 x)
pattern A4 x = Arg (A3 x)
pattern A5 x = Arg (A4 x)
pattern A6 x = Arg (A5 x)
pattern A7 x = Arg (A6 x)
pattern A8 x = Arg (A7 x)
pattern A9 x = Arg (A8 x)

data SLoT (tys :: LoT dtk) where
  SLoT0  ::            SLoT LoT0
  SLoTA  :: SLoT ts -> SLoT (t :&&: ts)

pattern SLoT1 = SLoTA SLoT0
pattern SLoT2 = SLoTA SLoT1
pattern SLoT3 = SLoTA SLoT2
pattern SLoT4 = SLoTA SLoT3
pattern SLoT5 = SLoTA SLoT4
pattern SLoT6 = SLoTA SLoT5
pattern SLoT7 = SLoTA SLoT6
pattern SLoT8 = SLoTA SLoT7
pattern SLoT9 = SLoTA SLoT8

class SForLoT (tys :: LoT k) where
  slot :: SLoT tys
instance SForLoT LoT0 where
  slot = SLoT0
instance SForLoT ts => SForLoT (t :&&: ts) where
  slot = SLoTA slot
-}

type family (f :: k) :@@: (tys :: LoT k) :: * where
  f :@@: LoT0        = f
  f :@@: (a :&&: as) = f a :@@: as

{-
unravel :: f :@@: ts -> Apply f ts
unravel (A0  x) = x
unravel (Arg x) = unravel x

unravel' :: SLoT ts -> f :@@: ts -> Apply f ts
unravel' _ = unravel

ravel :: SForLoT ts => Apply f ts -> f :@@: ts
ravel = ravel' slot

ravel' :: SLoT ts -> Apply f ts -> f :@@: ts
ravel' SLoT0      x = A0  x
ravel' (SLoTA ts) x = Arg (ravel' ts x)
-}

type family Split (t :: d) (f :: k) :: LoT k where
  Split t f = Split' t f LoT0

type family Split' (t :: d) (f :: k) (p :: LoT l) :: LoT k where
  Split' f     f acc = acc
  Split' (t a) f acc = Split' t f (a :&&: acc)

{-
split :: forall f t.
         (SForLoT (Split t f), t ~ Apply f (Split t f))
      => t -> f :@@: Split t f
split = ravel

unsplit :: forall f t.
           (SForLoT (Split t f), t ~ Apply f (Split t f))
        => f :@@: Split t f -> t
unsplit = unravel
-}
