{-# language AllowAmbiguousTypes #-}
{-# language DataKinds #-}
{-# language EmptyCase #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language PolyKinds #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# options_ghc -Wno-orphans #-}
module Main (main) where

import Data.Kind
import Data.Proxy
import Generics.Kind
import Generics.Kind.TH

main :: IO ()
main =
  let insts = [ -- Representation types
                isGenericK @_ @(V1 _) @'LoT0
              , isGenericK @_ @V1     @(_ ':&&: 'LoT0)

              , isGenericK @_ @((:+:) _ _ _) @'LoT0
              , isGenericK @_ @((:+:) _ _)   @(_ ':&&: 'LoT0)
              , isGenericK @_ @((:+:) _)     @(_ ':&&: _ ':&&: 'LoT0)
              , isGenericK @_ @(:+:)         @(_ ':&&: _ ':&&: _ ':&&: 'LoT0)

              , isGenericK @_ @((:*:) _ _ _) @'LoT0
              , isGenericK @_ @((:*:) _ _)   @(_ ':&&: 'LoT0)
              , isGenericK @_ @((:*:) _)     @(_ ':&&: _ ':&&: 'LoT0)
              , isGenericK @_ @(:*:)         @(_ ':&&: _ ':&&: _ ':&&: 'LoT0)

              , isGenericK @_ @(U1 _) @'LoT0
              , isGenericK @_ @U1     @(_ ':&&: 'LoT0)

              , isGenericK @_ @(M1 _ _ _ _) @'LoT0
              , isGenericK @_ @(M1 _ _ _)   @(_ ':&&: 'LoT0)
              , isGenericK @_ @(M1 _ _)     @(_ ':&&: _ ':&&: 'LoT0)
              , isGenericK @_ @(M1 _)       @(_ ':&&: _ ':&&: _ ':&&: 'LoT0)
              , isGenericK @_ @M1           @(_ ':&&: _ ':&&: _ ':&&: _ ':&&: 'LoT0)

              , isGenericK @_ @(Field _ _)        @'LoT0

              , isGenericK @_ @((:=>:) _ _ _) @'LoT0

              , isGenericK @_ @(Exists _ _ _) @'LoT0
              , isGenericK @_ @(Exists _ _)   @(_ ':&&: 'LoT0)
              , isGenericK @_ @(Exists _)     @(_ ':&&: _ ':&&: 'LoT0)

                -- Other data types
              , isGenericK @_ @(LoT _) @'LoT0
              , isGenericK @_ @LoT     @(_ ':&&: 'LoT0)

              , isGenericK @_ @TyEnv @'LoT0

                -- Data families
              , isGenericK @_ @(DF Char Int _) @'LoT0
              , isGenericK @_ @(DF Char Int)   @(_ ':&&: 'LoT0)

              , isGenericK @_ @(DF () () _) @'LoT0
              , isGenericK @_ @(DF () ())   @(_ ':&&: 'LoT0)

              , isGenericK @_ @(DF Bool () (Maybe _)) @'LoT0

                -- Tricky cases
              , isGenericK @_ @(TC1 _) @'LoT0
              , isGenericK @_ @TC1     @(_ ':&&: 'LoT0)

              , isGenericK @_ @(TC2 _) @'LoT0
              , isGenericK @_ @TC2     @(_ ':&&: 'LoT0)

              , isGenericK @_ @(TC3 _ _) @'LoT0
              , isGenericK @_ @(TC3 _)   @(_ ':&&: 'LoT0)

              , isGenericK @_ @(TC4 _) @'LoT0
              , isGenericK @_ @TC4     @(_ ':&&: 'LoT0)

              , isGenericK @_ @(TC5 _) @'LoT0
              ]
  in insts `seq` pure ()

isGenericK :: forall k (f :: k) (x :: LoT k). GenericK f x => ()
isGenericK = fromK @k @f @x `seq` ()

----------------
-- Data families
----------------

data family DF a b c
data instance DF Char Int c = DF1 c
data instance DF a a c = DF2 a c
data instance DF Bool () (Maybe c) = DF3 c

---------------
-- Tricky cases
---------------

-- An existential context with multiple constraints
data TC1 :: Type -> Type where
  MkTC1 :: forall a. (Eq a, Read a, Show a) => TC1 a

-- A kind variable being used as a type variable
data TC2 :: forall k. k -> Type where
  MkTC2 :: forall k (a :: k). k -> Proxy a -> TC2 a

-- Visible dependent quantification
data TC3 k :: k -> Type where
  MkTC3 :: forall k (a :: k). k -> Proxy a -> TC3 k a

-- This sort of type family is OK to partially apply
type family UnsaturateMe :: Type -> Type
newtype TC4 :: Type -> Type where
  MkTC4 :: forall a. UnsaturateMe a -> TC4 a

-- Tricky kind inference involving Proxy
data TC5 :: Type -> Type where
  MkTC5 :: forall k (a :: k). k -> Proxy a -> TC5 k

$(concat <$> traverse deriveGenericK
    [ -- Representation types
      ''V1, ''(:+:), ''(:*:), ''U1, ''M1, ''Field, ''(:=>:), ''Exists

      -- Other data types
    , ''LoT, ''TyEnv

      -- Data families
    , 'DF1, 'DF2, 'DF3

      -- Tricky cases
    , ''TC1, ''TC2, ''TC3, ''TC4, ''TC5
    ])
