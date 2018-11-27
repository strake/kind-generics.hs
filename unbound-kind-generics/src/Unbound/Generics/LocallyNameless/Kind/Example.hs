{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language TypeFamilies #-}
{-# language DataKinds #-}
{-# language QuantifiedConstraints #-}
{-# language TypeApplications #-}
{-# language ScopedTypeVariables #-}
-- | Example of how to use `unbound-kind-generics`
module Unbound.Generics.LocallyNameless.Kind.Example where

import Data.Typeable (Typeable)
import qualified Data.Typeable as T
import Generics.Kind
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Kind.Derive

-- | Variables stand for expressions
type Var t = Name (Expr t)

-- | Well-typed lambda expressions
data Expr t where
  V   :: Var t -> Expr t
  Lam :: (Typeable a, Typeable b) => (Bind (Var a) (Expr b)) -> Expr (a -> b)
  App :: (Typeable a) => Expr (a -> b) -> Expr a -> Expr b

eval :: Typeable t => Expr t -> FreshM (Expr t)
eval (V x) = fail $ "unbound variable " ++ show x
eval e@(Lam {}) = return e
eval (App e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case v1 of
   (Lam bnd) -> do
     -- open the lambda by picking a fresh name for the bound variable x in body
     (x, body) <- unbind bnd
     let body' = subst x v2 body
     eval body'
   _ -> fail "application of non-lambda"

example :: forall a. Typeable a => Expr (a -> a)
example =
  let x = s2n "x"
      y = s2n "y"
      e1 = Lam @(a -> a) $ bind x (Lam @(a -> a) $ bind y (V x)) -- \x y -> x
      z = s2n "z"
      e2 = Lam @a $ bind z (V z) -- \z -> z
  in runFreshM $ eval (App (App e1 e2) e2)

deriving instance Show (Expr t)

instance GenericK (Expr t) LoT0 where
  type RepK (Expr t) =
    ((F (Kon (Name (Expr t)))))
    :+:
    (ERefl {- V1 = a -} (ERefl {- V0 = b -} (
      ((Kon t) :~: ((->) :$: V1 :@: V0))
      :=>:
      (F (Bind :$: (Name :$: (Expr :$: V1)) :@: (Expr :$: V0))) )))
    :+:
    (ERefl {- V0 = a -} (
      (F (Expr :$: ((->) :$: V0 :@: (Kon t)))) :*: F (Expr :$: V0) ))

  fromK (V   v)   = L1 (F v)
  fromK (Lam b)   = R1 (L1 (ERefl (ERefl (C (F b)))))
  fromK (App x y) = R1 (R1 (ERefl (F x :*: F y)))

  toK (L1 (F v))                          = V v
  toK (R1 (L1 (ERefl (ERefl (C (F b)))))) = Lam b
  toK (R1 (R1 (ERefl (F x :*: F y))))     = App x y

instance Typeable t => Alpha (Expr t) where
  aeq'        = aeqDefK
  fvAny'      = fvAnyDefK
  close       = closeDefK
  open        = openDefK
  isPat       = isPatDefK
  isTerm      = isTermDefK
  isEmbed     = isEmbedDefK
  nthPatFind  = nthPatFindDefK
  namePatFind = namePatFindDefK
  swaps'      = swapsDefK
  lfreshen'   = lfreshenDefK
  freshen'    = freshenDefK
  acompare'   = acompareDefK

instance (Typeable small, Typeable big)
         => Subst (Expr small) (Expr big) where
  isvar (V x) = buildSubstName x
  isvar _     = Nothing
  subst  = gsubstDefK
  substs = gsubstsDefK