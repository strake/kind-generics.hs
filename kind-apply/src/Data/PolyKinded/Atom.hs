{-# language GADTs           #-}
{-# language TypeOperators   #-}
{-# language TypeFamilies    #-}
{-# language DataKinds       #-}
{-# language PolyKinds       #-}
{-# language ConstraintKinds #-}
module Data.PolyKinded.Atom where

import Data.Kind
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

infixr 5 :&:
data Atom d k where
  Var   :: TyVar d k -> Atom d k
  Kon   :: k         -> Atom d k
  (:@:) :: Atom d (k1 -> k2) -> Atom d k1 -> Atom d k2
  (:&:) :: Atom d Constraint -> Atom d Constraint -> Atom d Constraint
  KindOf :: Atom d k -> Atom d (*)

type f :$: x = 'Kon f ':@: x
type a :~: b = 'Kon (~) ':@: a ':@: b

type family Ty (t :: Atom d k) (tys :: LoT d) :: k where
  Ty ('Var 'VZ)     (t ':&&: ts) = t
  Ty ('Var ('VS v)) (t ':&&: ts) = Ty ('Var v) ts
  Ty ('Kon t)       tys          = t
  Ty (f ':@: x)     tys          = (Ty f tys) (Ty x tys)
  Ty (c ':&: d)     tys          = (Ty c tys, Ty d tys)
  Ty (KindOf (x :: Atom d k)) tys = k

type family Satisfies (cs :: [Atom d Constraint]) (tys :: LoT d) :: Constraint where
  Satisfies '[]       tys = ()
  Satisfies (c ': cs) tys = (Ty c tys, Satisfies cs tys)