module Generics.SOP.Kind.Derive.Eq where

import Generics.SOP.Kind

geq :: RepK f tys -> RepK f tys -> Bool
geq x y = goS x y
  where
    goS (Z x) (Z y) = goB x y
    goS (S x) (S y) = goS x y
    goS _     _     = False

    goB (C_ x) (C_ y) = goB x y
    goB (F_ x) (F_ y) = goP x y

    goP Nil          Nil          = True
    goP (A_ x :* xs) (A_ y :* ys) = x == y && goP xs ys