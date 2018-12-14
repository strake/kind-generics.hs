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
{-# language TemplateHaskell #-}
-- | Example of how to use `unbound-kind-generics`
module Unbound.Generics.LocallyNameless.Kind.Example where

import Data.Typeable (Typeable)
import qualified Data.Typeable as T
import Generics.Kind
import Generics.Kind.TH
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Kind.Derive

-- | Variables stand for expressions
type Var t = Name (Expr t)

-- | Well-typed lambda expressions
data Expr t where
  V   :: Var t -> Expr t
  Lam :: (Typeable a, Typeable b) => (Bind (Var a) (Expr b)) -> Expr (a -> b)
  App :: (Typeable a) => Expr (a -> b) -> Expr a -> Expr b

$(deriveGenericK ''Expr)

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



{-
instance GenericK (Expr t) LoT0 where
  type RepK (Expr t) =
    ((Field (Kon (Name (Expr t)))))
    :+:
    (Exists (*) {- Var1 = a -} ((Typeable :$: Var0) :=>:
      (Exists (*) {- Var0 = b -} ((Typeable :$: Var0) :=>:
        (((Kon t) :~: ((->) :$: Var1 :@: Var0))
         :=>:
         (Field (Bind :$: (Name :$: (Expr :$: Var1)) :@: (Expr :$: Var0)))) ))))
    :+:
    (Exists (*) {- Var0 = a -} (
      (Typeable :$: Var0)
      :=>:
      ((Field (Expr :$: ((->) :$: Var0 :@: (Kon t)))) :*: Field (Expr :$: Var0)) ))

  fromK (V   v)   = L1 (Field v)
  fromK (Lam b)   = R1 (L1 (Exists (SuchThat (Exists (SuchThat (SuchThat (Field b)))))))
  fromK (App x y) = R1 (R1 (Exists (SuchThat (Field x :*: Field y))))

  toK (L1 (Field v)) = V v
  toK (R1 (L1 (Exists (SuchThat (Exists (SuchThat (SuchThat (Field b)))))))) = Lam b
  toK (R1 (R1 (Exists (SuchThat (Field x :*: Field y))))) = App x y
-}

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