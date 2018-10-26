{-# language GADTs         #-}
{-# language TypeOperators #-}
{-# language TypeFamilies  #-}
{-# language DataKinds     #-}
{-# language PolyKinds     #-}
module Generics.Kind.Atom where

import Data.PolyKinded

data TyVar d k where
  VZ :: TyVar (x -> xs) x
  VS :: TyVar xs k -> TyVar (x -> xs) k

type V0 = 'Var 'VZ
type V1 = 'Var ('VS 'VZ)
type V2 = 'Var ('VS ('VS 'VZ))
type V3 = 'Var ('VS ('VS ('VS 'VZ)))
type V4 = 'Var ('VS ('VS ('VS ('VS 'VZ))))
type V5 = 'Var ('VS ('VS ('VS ('VS ('VS 'VZ)))))
type V6 = 'Var ('VS ('VS ('VS ('VS ('VS ('VS 'VZ))))))
type V7 = 'Var ('VS ('VS ('VS ('VS ('VS ('VS ('VS 'VZ)))))))
type V8 = 'Var ('VS ('VS ('VS ('VS ('VS ('VS ('VS ('VS 'VZ))))))))
type V9 = 'Var ('VS ('VS ('VS ('VS ('VS ('VS ('VS ('VS ('VS 'VZ)))))))))

data Atom d k where
  Var    :: TyVar d k -> Atom d k
  Kon    :: k         -> Atom d k
  (:@:)  :: Atom d (k1 -> k2) -> Atom d k1 -> Atom d k2

type f :$: x = 'Kon f ':@: x
type a :~: b = 'Kon (~) ':@: a ':@: b

type family Ty (t :: Atom d k) (tys :: LoT d) :: k where
  Ty ('Var 'VZ)     (t ':&&: ts) = t
  Ty ('Var ('VS v)) (t ':&&: ts) = Ty ('Var v) ts
  Ty ('Kon t)       tys          = t
  Ty (f ':@: x)     tys          = (Ty f tys) (Ty x tys)