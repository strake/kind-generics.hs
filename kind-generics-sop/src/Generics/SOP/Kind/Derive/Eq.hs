{-# language GADTs               #-}
{-# language PolyKinds           #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts    #-}
{-# language TypeApplications    #-}
{-# language TypeOperators       #-}
{-# language DataKinds           #-}
{-# language AllowAmbiguousTypes #-}
module Generics.SOP.Kind.Derive.Eq where

import Generics.SOP.Kind

geq' :: forall f x.
        (GenericK f x, AllFields Eq (CodeK f) x)
     => f :@@: x -> f :@@: x -> Bool
geq' x y = geq (fromK @_ @f @x x) (fromK @_ @f @x y)

geq :: forall f tys. AllFields Eq f tys
    => RepK f tys -> RepK f tys -> Bool
geq = goS
  where
    goS :: forall g. AllFields Eq g tys
        => NS (NB tys) g -> NS (NB tys) g -> Bool 
    goS (Z x) (Z y) = goB x y
    goS (S x) (S y) = goS x y
    goS _     _     = False

    goB :: forall b rys. AllFieldsB Eq b rys
        => NB rys b -> NB rys b -> Bool
    goB (SuchThat_ x) (SuchThat_ y) = goB x y
    goB (Fields_ x)   (Fields_ y) = goP x y
    goB (Exists_ _)   (Exists_ _) = error "existentials are not supported"

    goP :: forall d rys. AllFieldsP Eq d rys
        => NP (NA rys) d -> NP (NA rys) d -> Bool
    goP Nil             Nil          = True
    goP (Atom_ x :* xs) (Atom_ y :* ys) = x == y && goP xs ys