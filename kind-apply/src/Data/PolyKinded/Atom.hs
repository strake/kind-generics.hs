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
import GHC.Exts

data TyVar (d :: *) (k :: TYPE r) where
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
infixr 5 :=>>:
data Atom (d :: *) (k :: TYPE r) where
  Var :: TyVar d k -> Atom d k
  Kon :: k         -> Atom d k
  (:@:) :: Atom d (k1 -> k2) -> Atom d k1 -> Atom d k2
  (:&:) :: Atom d Constraint -> Atom d Constraint -> Atom d Constraint
  ForAll  :: Atom (d1 -> d) (*) -> Atom d (*)
  (:=>>:) :: Atom d Constraint -> Atom d (*) -> Atom d (*)

type f :$:  x = 'Kon f ':@: x
type a :~:  b = 'Kon (~) ':@: a ':@: b
type a :~~: b = 'Kon (~~) ':@: a ':@: b

type family Interpret (t :: Atom d k) (tys :: LoT d) :: k where
  Interpret ('Var 'VZ)     (t ':&&: ts) = t
  Interpret ('Var ('VS v)) (t ':&&: ts) = Interpret ('Var v) ts
  Interpret ('Kon t)       tys = t
  Interpret (f ':@: x)     tys = (Interpret f tys) (Interpret x tys)
  Interpret (c ':&: d)     tys = (Interpret c tys, Interpret d tys)
  Interpret (ForAll f)     tys = ForAllI f tys
  Interpret (c ':=>>: f)   tys = SuchThatI c f tys

newtype ForAllI (f :: Atom (d1 -> d) (*)) (tys :: LoT d) where
  ForAllI :: (forall t. Interpret f (t ':&&: tys)) -> ForAllI f tys

newtype SuchThatI (c :: Atom d Constraint) (f :: Atom d (*)) (tys :: LoT d) where
  SuchThatI :: (Interpret c tys => Interpret f tys) -> SuchThatI c f tys

type family Satisfies (cs :: [Atom d Constraint]) (tys :: LoT d) :: Constraint where
  Satisfies '[]       tys = ()
  Satisfies (c ': cs) tys = (Interpret c tys, Satisfies cs tys)