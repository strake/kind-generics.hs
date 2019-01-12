{-# OPTIONS_GHC -fno-warn-orphans  #-}
{-# language TypeOperators         #-}
{-# language TypeFamilies          #-}
{-# language DataKinds             #-}
{-# language PolyKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language GADTs                 #-}
module Generics.Kind.Rec.Examples where

import Generics.Kind.Rec

instance GenericK [] (a :&&: LoT0) where
  type RepK [] = U1 :+: Field Var0 :*: Field (Rec :@: Var0)

  fromK []     = L1 U1
  fromK (x:xs) = R1 (Field x :*: Field xs)
  toK (L1 U1)                     = []
  toK (R1 (Field x :*: Field xs)) = x:xs