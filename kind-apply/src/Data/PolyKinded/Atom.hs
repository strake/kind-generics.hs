{-# language GADTs           #-}
{-# language TypeOperators   #-}
{-# language TypeFamilies    #-}
{-# language DataKinds       #-}
{-# language PolyKinds       #-}
{-# language ConstraintKinds #-}
{-# language RankNTypes      #-}
{-# language AllowAmbiguousTypes #-}
module Data.PolyKinded.Atom where

import Data.Kind
import Data.PolyKinded
import Data.Type.Equality
import Data.Proxy

data TyVar d k where
  VZ :: TyVar (x -> xs) x
  VS :: TyVar xs k -> TyVar (x -> xs) k

type Var0 = 'Var 'VZ
type Var1 = 'Var ('VS 'VZ)
type Var2 = 'Var ('VS ('VS 'VZ))
type Var3 = 'Var ('VS ('VS ('VS 'VZ)))
type Var4 = 'Var ('VS ('VS ('VS ('VS 'VZ))))
type Var5 = 'Var ('VS ('VS ('VS ('VS ('VS 'VZ)))))
type Var6 = 'Var ('VS ('VS ('VS ('VS ('VS ('VS 'VZ))))))
type Var7 = 'Var ('VS ('VS ('VS ('VS ('VS ('VS ('VS 'VZ)))))))
type Var8 = 'Var ('VS ('VS ('VS ('VS ('VS ('VS ('VS ('VS 'VZ))))))))
type Var9 = 'Var ('VS ('VS ('VS ('VS ('VS ('VS ('VS ('VS ('VS 'VZ)))))))))

infixr 5 :&:
data Atom d k where
  Var    :: TyVar d k -> Atom d k
  Kon    :: k         -> Atom d k
  (:@:)  :: Atom d (k1 -> k2) -> Atom d k1 -> Atom d k2
  (:&:)  :: Atom d Constraint -> Atom d Constraint -> Atom d Constraint
  KindOf :: Atom d k -> Atom d (*)
  ForAll :: Atom (d1 -> d) (*) -> Atom d (*)

type f :$:  x = 'Kon f ':@: x
type a :~:  b = 'Kon (~) ':@: a ':@: b
type a :~~: b = 'Kon (~~) ':@: a ':@: b

type family Ty (t :: Atom d k) (tys :: LoT d) :: k where
  Ty ('Var 'VZ)     (t ':&&: ts)  = t
  Ty ('Var ('VS v)) (t ':&&: ts)  = Ty ('Var v) ts
  Ty ('Kon t)       tys           = t
  Ty (f ':@: x)     tys           = (Ty f tys) (Ty x tys)
  Ty (c ':&: d)     tys           = (Ty c tys, Ty d tys)
  Ty (KindOf (a :: Atom d k)) tys = k
  Ty (ForAll f)     tys           = ForAllTy f tys

data ForAllTy (f :: Atom (d1 -> d) (*)) (tys :: LoT d) where
  ForAllTy :: (forall t. Ty f (t ':&&: tys)) -> ForAllTy f tys

type family Satisfies (cs :: [Atom d Constraint]) (tys :: LoT d) :: Constraint where
  Satisfies '[]       tys = ()
  Satisfies (c ': cs) tys = (Ty c tys, Satisfies cs tys)