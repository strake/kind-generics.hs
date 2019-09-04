{-# language DataKinds              #-}
{-# language PolyKinds              #-}
{-# language GADTs                  #-}
{-# language TypeOperators          #-}
{-# language MultiParamTypeClasses  #-}
{-# language FlexibleInstances      #-}
{-# language FlexibleContexts       #-}
{-# language UndecidableInstances   #-}
{-# language QuantifiedConstraints  #-}
{-# language TypeApplications       #-}
{-# language TypeFamilies           #-}
{-# language ScopedTypeVariables    #-}
{-# language PartialTypeSignatures  #-}
module Generics.Kind.Derive.Json where

import Control.Applicative
import Control.Monad
import Data.Aeson
import Data.Aeson.Types
import Data.Proxy
import GHC.Generics (Meta (..))
import GHC.TypeLits
import Generics.Kind

gtoJSON' :: forall t. (GenericK t, GToJSONK (RepK t) LoT0)
         => t -> Value
gtoJSON' x = gtoJSON (fromK @_ @t @LoT0 x)

gfromJSON' :: forall t. (GenericK t, GFromJSONK (RepK t) LoT0)
           => Value -> Parser t
gfromJSON' v = fmap (toK @_ @t @LoT0) (gfromJSON v)

class GToJSONK (f :: LoT k -> *) (x :: LoT k) where
  gtoJSON :: f x -> Value
class GFromJSONK (f :: LoT k -> *) (x :: LoT k) where
  gfromJSON :: Value -> Parser (f x)

instance ToJSON (Interpret t x)
         => GToJSONK (Field t) x where
  gtoJSON (Field t) = toJSON t
instance FromJSON (Interpret t x)
         => GFromJSONK (Field t) x where
  gfromJSON = fmap Field . parseJSON

instance GToJSONK U1 x where
  gtoJSON U1 = Null
instance GFromJSONK U1 x where
  gfromJSON Null = pure U1
  gfromJSON _    = empty

instance (GToJSONK f x, GToJSONK g x)
         => GToJSONK (f :+: g) x where
  gtoJSON (L1 f) = gtoJSON f
  gtoJSON (R1 g) = gtoJSON g
instance (GFromJSONK f x, GFromJSONK g x)
         => GFromJSONK (f :+: g) x where
  gfromJSON v = (L1 <$> gfromJSON v) <|> (R1 <$> gfromJSON v)

instance (GToJSONK f x, GToJSONK g x)
         => GToJSONK (f :*: g) x where
  gtoJSON (f :*: g) = toJSON (gtoJSON f, gtoJSON g)
instance (GFromJSONK f x, GFromJSONK g x)
         => GFromJSONK (f :*: g) x where
  gfromJSON v = do (f, g) <- parseJSON v
                   (:*:) <$> gfromJSON f <*> gfromJSON g

instance forall name f x i fx st.
         (GToJSONK f x, KnownSymbol name)
         => GToJSONK (M1 i ('MetaCons name fx st) f) x where
  gtoJSON (M1 f) = toJSON (symbolVal $ Proxy @name, gtoJSON f)
instance forall name f x i fx st.
         (GFromJSONK f x, KnownSymbol name)
         => GFromJSONK (M1 i ('MetaCons name fx st) f) x where
  gfromJSON v = do (name, f) <- parseJSON v
                   guard $ name == symbolVal (Proxy @name)
                   M1 <$> gfromJSON f

instance GToJSONK f x
         => GToJSONK (M1 i ('MetaData _1 _2 _3 _4) f) x where
  gtoJSON (M1 f) = gtoJSON f
instance GFromJSONK f x
         => GFromJSONK (M1 i ('MetaData _1 _2 _3 _4) f) x where
  gfromJSON = fmap M1 . gfromJSON

instance GToJSONK f x
         => GToJSONK (M1 i ('MetaSel _1 _2 _3 _4) f) x where
  gtoJSON (M1 f) = gtoJSON f
instance GFromJSONK f x
         => GFromJSONK (M1 i ('MetaSel _1 _2 _3 _4) f) x where
  gfromJSON = fmap M1 . gfromJSON

instance (Interpret c x => GToJSONK f x)
         => GToJSONK (c :=>: f) x where
  gtoJSON (SuchThat f) = gtoJSON f
instance (Interpret c x, GFromJSONK f x)
         => GFromJSONK (c :=>: f) x where
  gfromJSON = fmap SuchThat . gfromJSON

instance (forall t. GToJSONK f (t ':&&: x))
         => GToJSONK (Exists k f) x where
  gtoJSON (Exists x) = gtoJSON x
instance (forall t. GFromJSONK f (t ':&&: x))
         => GFromJSONK (Exists k f) x where
  gfromJSON = fmap Exists . gfromJSON
