{-# language GADTs               #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts    #-}
module Generics.SOP.Kind.Derive.Eq where

import Generics.SOP.Kind

geq :: forall f tys. AllFields Show f tys
    => RepK f tys -> RepK f tys -> Bool
geq x y = goS x y
  where
    goS :: forall g. AllFields Show g tys
        => NS (NB tys) g -> NS (NB tys) g -> Bool 
    goS (Z x) (Z y) = goB x y
    goS (S x) (S y) = goS x y
    goS _     _     = False

    goB :: forall b. AllFieldsB Show b tys
        => NB tys b -> NB tys b -> Bool
    goB (C_ x) (C_ y) = goB x y
    goB (F_ x) (F_ y) = goP x y

    goP :: forall d. AllFieldsP Show d tys
        => NP (NA tys) d -> NP (NA tys) d -> Bool
    goP Nil          Nil          = True
    goP (A_ x :* xs) (A_ y :* ys) = x == y && goP xs ys