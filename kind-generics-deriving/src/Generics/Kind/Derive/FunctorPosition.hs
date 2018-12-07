{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances     #-}
{-# language DataKinds             #-}
{-# language PolyKinds             #-}
{-# language KindSignatures        #-}
{-# language ScopedTypeVariables   #-}
{-# language QuantifiedConstraints #-}
{-# language TypeOperators         #-}
{-# language UndecidableInstances  #-}
{-# language TypeApplications      #-}
{-# language TypeFamilies          #-}
{-# language FlexibleContexts      #-}
{-# language AllowAmbiguousTypes   #-}
module Generics.Kind.Derive.FunctorPosition where

import Data.Proxy
import Generics.Kind
import GHC.TypeLits

fmapDefaultPos :: forall v f as bs.
                  (GenericK f as, GenericK f bs,
                   GFunctorPos (RepK f) v as bs)
               => (Interpret (Var v) as -> Interpret (Var v) bs)
               -> f :@@: as -> f :@@: bs
fmapDefaultPos f = toK @_ @f @bs . gfmapp (Proxy @v) f . fromK @_ @f @as

class GFunctorPos (f :: LoT k -> *) (v :: TyVar k *)
                  (as :: LoT k) (bs :: LoT k) where
  gfmapp :: Proxy v
         -> (Interpret (Var v) as -> Interpret (Var v) bs)
         -> f as -> f bs

gfmapp' :: forall as bs f v. (GFunctorPos f v as bs)
        => Proxy v
        -> (Interpret (Var v) as -> Interpret (Var v) bs)
        -> f as -> f bs
gfmapp' = gfmapp

instance GFunctorPos U1 v as bs where
  gfmapp _ _ U1 = U1

instance GFunctorPos f v as bs
         => GFunctorPos (M1 i c f) v as bs where
  gfmapp p v (M1 x) = M1 (gfmapp p v x)

instance (GFunctorPos f v as bs, GFunctorPos g v as bs)
         => GFunctorPos (f :+: g) v as bs where
  gfmapp p v (L1 x) = L1 (gfmapp p v x)
  gfmapp p v (R1 x) = R1 (gfmapp p v x)

instance (GFunctorPos f v as bs, GFunctorPos g v as bs)
         => GFunctorPos (f :*: g) v as bs where
  gfmapp p v (x :*: y) = gfmapp p v x :*: gfmapp p v y

instance (Interpret c as => GFunctorPos f v as bs, {- Interpret c as => -} Interpret c bs)
         => GFunctorPos (c :=>: f) v as bs where
  gfmapp p v (SuchThat x) = SuchThat (gfmapp p v x)

instance forall k f v as bs.
         (forall (t :: k). GFunctorPos f ('VS v) (t ':&&: as) (t ':&&: bs))
         => GFunctorPos (Exists k f) v as bs where
  gfmapp _ v (Exists (x :: f (t ':&&: x)))
    = Exists (gfmapp' @(t ':&&: x) @(t ':&&: _) (Proxy @('VS v)) v x)

type family ContainsTyVar (v :: TyVar d k) (t :: Atom d p) :: Bool where
  ContainsTyVar v (Var v)   = 'True
  ContainsTyVar v (Var w)   = 'False
  ContainsTyVar v (Kon t)   = 'False
  ContainsTyVar v (f :@: x) = Or (ContainsTyVar v f) (ContainsTyVar v x)
  ContainsTyVar v other     = 'False

type family Or (x :: Bool) (y :: Bool) :: Bool where
  Or True  thing = True
  Or thing True  = True
  Or False False = False

class GFunctorArgPos (t :: Atom d (*)) (v :: TyVar d *)
                     (as :: LoT d) (bs :: LoT d)
                     (p :: Bool) where
  gfmappf :: Proxy t -> Proxy v -> Proxy as -> Proxy bs -> Proxy p
          -> (Interpret (Var v) as -> Interpret (Var v) bs)
          -> Interpret t as -> Interpret t bs

instance forall t v as bs. GFunctorArgPos t v as bs (ContainsTyVar v t)
         => GFunctorPos (Field t) v as bs where
  gfmapp p v (Field x) = Field (gfmappf (Proxy @t) p (Proxy @as) (Proxy @bs) (Proxy @(ContainsTyVar v t)) v x)

instance (Interpret t as ~ Interpret t bs) => GFunctorArgPos t v as bs False where
  gfmappf _ _ _ _ _ _ = id

instance TypeError (Text "Should never get here")
         => GFunctorArgPos ('Kon t) v as bs whatever where
  gfmappf _ _ _ _ _ _ = id

-- We found the same variable
instance GFunctorArgPos ('Var 'VZ) 'VZ (a ':&&: as) (b ':&&: bs) True where
  gfmappf _ _ _ _ _ f x = f x
-- We need to keep looking
instance forall v n r as s bs isthere.
         GFunctorArgPos ('Var v) n as bs isthere
         => GFunctorArgPos ('Var ('VS v)) ('VS n) (r ':&&: as) (s ':&&: bs) isthere where
  gfmappf _ _ _ _ _ f x
    = gfmappf (Proxy @('Var v)) (Proxy @n) (Proxy @as) (Proxy @bs) (Proxy @isthere) f x
-- If we arrive to another we do not want, keep it as it is
instance TypeError (Text "Should never get here")
         => GFunctorArgPos ('Var 'VZ) ('VS n) (r ':&&: as) (r ':&&: bs) whatever where
  gfmappf _ _ _ _ _ _ x = x

-- Going through functor
instance forall f x v as bs.
         ( Functor f, GFunctorArgPos x v as bs (ContainsTyVar v x) )
         => GFunctorArgPos (f :$: x) v as bs True where
  gfmappf _ _ _ _ _ f x
    = fmap (gfmappf (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) (Proxy @(ContainsTyVar v x)) f) x

instance forall f y x v as bs.
         ( Functor (f (Interpret y as)), Interpret y as ~ Interpret y bs
         , GFunctorArgPos x v as bs (ContainsTyVar v x) )
         => GFunctorArgPos (f :$: y ':@: x) v as bs True where
  gfmappf _ _ _ _ _ f x
    = fmap (gfmappf (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) (Proxy @(ContainsTyVar v x)) f) x

instance forall f y1 y2 x v as bs.
         (Functor (f (Interpret y1 as) (Interpret y2 as)),
          Interpret y1 as ~ Interpret y1 bs, Interpret y2 as ~ Interpret y2 bs,
          GFunctorArgPos x v as bs (ContainsTyVar v x) )
         => GFunctorArgPos (f :$: y1 ':@: y2 ':@: x) v as bs True where
  gfmappf _ _ _ _ _ f x
    = fmap (gfmappf (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) (Proxy @(ContainsTyVar v x)) f) x