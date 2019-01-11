{-# language GADTs           #-}
{-# language TypeOperators   #-}
{-# language TypeFamilies    #-}
{-# language DataKinds       #-}
{-# language PolyKinds       #-}
{-# language ConstraintKinds #-}
{-# language RankNTypes      #-}
{-# language AllowAmbiguousTypes  #-}
{-# language UndecidableInstances #-}
{-# language ScopedTypeVariables  #-}
{-# language TypeApplications     #-}
{-# language ImpredicativeTypes   #-}
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

type family InterpretVar (t :: TyVar d k) (tys :: LoT d) :: k where
  InterpretVar 'VZ     (t ':&&: ts) = t
  InterpretVar ('VS v) (t ':&&: ts) = InterpretVar v ts

type family Interpret (t :: Atom d k) (tys :: LoT d) :: k where
  Interpret ('Var v)     tys = InterpretVar v tys
  Interpret ('Kon t)     tys = t
  Interpret (f ':@: x)   tys = (Interpret f tys) (Interpret x tys)
  Interpret (c ':&: d)   tys = (Interpret c tys, Interpret d tys)
  Interpret (ForAll f)   tys = ForAllI f tys
  Interpret (c ':=>>: f) tys = SuchThatI c f tys

newtype ForAllI (f :: Atom (d1 -> d) (*)) (tys :: LoT d) where
  ForAllI :: (forall t. Interpret f (t ':&&: tys)) -> ForAllI f tys

newtype WrappedI (f :: Atom d (*)) (tys :: LoT d) =
  WrapI { unwrapI :: Interpret f tys }

toWrappedI :: forall f tys t. ForAllI f tys -> WrappedI f (t ':&&: tys)
toWrappedI (ForAllI x) = WrapI (x @t)

fromWrappedI :: forall f tys. (forall t. WrappedI f (t ':&&: tys)) -> ForAllI f tys
fromWrappedI = coerce @(forall t. WrappedI f (t ':&&: tys))

newtype SuchThatI (c :: Atom d Constraint) (f :: Atom d (*)) (tys :: LoT d) where
  SuchThatI :: (Interpret c tys => Interpret f tys) -> SuchThatI c f tys

type family Satisfies (cs :: [Atom d Constraint]) (tys :: LoT d) :: Constraint where
  Satisfies '[]       tys = ()
  Satisfies (c ': cs) tys = (Interpret c tys, Satisfies cs tys)

type family ContainsTyVar (v :: TyVar d k) (t :: Atom d p) :: Bool where
  ContainsTyVar v (Var v)     = 'True
  ContainsTyVar v (Var w)     = 'False
  ContainsTyVar v (Kon t)     = 'False
  ContainsTyVar v (f :@: x)   = Or (ContainsTyVar v f) (ContainsTyVar v x)
  ContainsTyVar v (x :&: y)   = Or (ContainsTyVar v x) (ContainsTyVar v y)
  ContainsTyVar v (c :=>>: f) = Or (ContainsTyVar v c) (ContainsTyVar v f)
  ContainsTyVar v (ForAll f)  = ContainsTyVar (VS v) f

type family Or (x :: Bool) (y :: Bool) :: Bool where
  Or True  thing = True
  Or thing True  = True
  Or False False = False