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
module Data.PolyKinded.Atom.Rec (
  TyVar(..), InterpretVar
, Var0, Var1, Var2, Var3, Var4, Var5, Var6, Var7, Var8, Var9
, Atom(..), RecLoT, Interpret
, ForAllI(..), WrappedI(..), toWrappedI, SuchThatI
) where

import Data.Kind
import Data.PolyKinded
import Data.Type.Equality
import GHC.Exts

import Data.PolyKinded.Atom (TyVar(..), InterpretVar)

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
data Atom (r :: *) (d :: *) (k :: TYPE v) where
  Var :: TyVar d k -> Atom r d k
  Kon :: k         -> Atom r d k
  (:@:) :: Atom r d (k1 -> k2) -> Atom r d k1 -> Atom r d k2
  (:&:) :: Atom r d Constraint -> Atom r d Constraint -> Atom r d Constraint
  ForAll  :: Atom r (d1 -> d) (*) -> Atom r d (*)
  (:=>>:) :: Atom r d Constraint -> Atom r d (*) -> Atom r d (*)
  Rec :: Atom r d r

type RecLoT r d = (r, LoT d)

type family Interpret (t :: Atom r d k) (tys :: RecLoT r d) :: k where
  Interpret ('Var v)     '(r, tys) = InterpretVar v tys
  Interpret ('Kon t)     '(r, tys) = t
  Interpret (f ':@: x)   rtys = (Interpret f rtys) (Interpret x rtys)
  Interpret (c ':&: d)   rtys = (Interpret c rtys, Interpret d rtys)
  Interpret (ForAll f)   rtys = ForAllI f rtys
  Interpret (c ':=>>: f) rtys = SuchThatI c f rtys
  Interpret Rec          '(r, tys) = r

data ForAllI (f :: Atom r (d1 -> d) (*)) (rtys :: RecLoT r d) where
  ForAllI :: (forall t. Interpret f '(r, t ':&&: tys)) -> ForAllI f '(r, tys)

newtype WrappedI (f :: Atom r d (*)) (rtys :: RecLoT r d) =
  WrapI { unwrapI :: Interpret f rtys }

toWrappedI :: forall f r tys t. ForAllI f '(r, tys) -> WrappedI f '(r, t ':&&: tys)
toWrappedI (ForAllI x) = WrapI (x @t)

-- fromWrappedI :: forall f r tys. (forall t. WrappedI f '(r, t ':&&: tys)) -> ForAllI f '(r, tys)
-- fromWrappedI = coerce @(forall t. WrappedI f '(r, t ':&&: tys))

newtype SuchThatI (c :: Atom r d Constraint) (f :: Atom r d (*)) (rtys :: RecLoT r d) where
  SuchThatI :: (Interpret c rtys => Interpret f rtys) -> SuchThatI c f rtys