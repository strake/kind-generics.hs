{-# language GADTs               #-}
{-# language PolyKinds           #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts    #-}
module Generics.SOP.Kind.Derive.Eq where

import Generics.SOP.Kind

geq' :: forall t f x.
        (GenericS t f x, AllFields Eq (CodeK f) x)
     => t -> t -> Bool
geq' x y = geq (fromS x) (fromS y)

geq :: forall f tys. AllFields Eq f tys
    => RepK f tys -> RepK f tys -> Bool
geq = goS
  where
    goS :: forall g. AllFields Eq g tys
        => NS (NB tys) g -> NS (NB tys) g -> Bool 
    goS (Z x) (Z y) = goB x y
    goS (S x) (S y) = goS x y
    goS _     _     = False

    goB :: forall b. AllFieldsB Eq b tys
        => NB tys b -> NB tys b -> Bool
    goB (C_ x) (C_ y) = goB x y
    goB (F_ x) (F_ y) = goP x y
    goB (E_ _) (E_ _) = error "existentials are not supported"

    goP :: forall d. AllFieldsP Eq d tys
        => NP (NA tys) d -> NP (NA tys) d -> Bool
    goP Nil          Nil          = True
    goP (A_ x :* xs) (A_ y :* ys) = x == y && goP xs ys