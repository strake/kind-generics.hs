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
                  (GenericK f, GenericK f,
                   GFunctorPos (RepK f) v as bs)
               => (Interpret (Var v) as -> Interpret (Var v) bs)
               -> f :@@: as -> f :@@: bs
fmapDefaultPos f = toK @_ @f @bs . gfmapp @_ @(RepK f) @v @as @bs f . fromK @_ @f @as

fmapDefault :: forall f a b. (GenericK f, GenericK f,
               GFunctorPos (RepK f) VZ (LoT1 a) (LoT1 b))
            => (a -> b) -> f a -> f b
fmapDefault = fmapDefaultPos @VZ @f @(LoT1 a) @(LoT1 b)

bimapDefault :: forall f a c b d.
                (GenericK f, GenericK f, GenericK f,
                 GFunctorPos (RepK f) VZ      (LoT2 a d) (LoT2 c d),
                 GFunctorPos (RepK f) (VS VZ) (LoT2 a b) (LoT2 a d))
             => (a -> c) -> (b -> d) -> f a b -> f c d
bimapDefault f g = fmapDefaultPos @VZ      @f @(LoT2 a d) @(LoT2 c d) f
                 . fmapDefaultPos @(VS VZ) @f @(LoT2 a b) @(LoT2 a d) g

class GFunctorPos (f :: LoT k -> *) (v :: TyVar k *)
                  (as :: LoT k) (bs :: LoT k) where
  gfmapp :: (Interpret (Var v) as -> Interpret (Var v) bs)
         -> f as -> f bs

instance GFunctorPos U1 v as bs where
  gfmapp _ U1 = U1

instance forall f v as bs i c. GFunctorPos f v as bs
         => GFunctorPos (M1 i c f) v as bs where
  gfmapp v (M1 x) = M1 (gfmapp @_ @f @v @as @bs v x)

instance forall f g v as bs. (GFunctorPos f v as bs, GFunctorPos g v as bs)
         => GFunctorPos (f :+: g) v as bs where
  gfmapp v (L1 x) = L1 (gfmapp @_ @f @v @as @bs v x)
  gfmapp v (R1 x) = R1 (gfmapp @_ @g @v @as @bs v x)

instance forall f g v as bs. (GFunctorPos f v as bs, GFunctorPos g v as bs)
         => GFunctorPos (f :*: g) v as bs where
  gfmapp v (x :*: y) = gfmapp @_ @f @v @as @bs v x :*: gfmapp @_ @g @v @as @bs v y

instance forall c f v as bs z.
         (Interpret c as => GFunctorPos f v as bs, z ~ Interpret c bs, Interpret c as => z)
         => GFunctorPos (c :=>: f) v as bs where
  gfmapp v (SuchThat x) = SuchThat (gfmapp @_ @f @v @as @bs v x)

instance forall k f v as bs.
         (forall (t :: k). GFunctorPos f ('VS v) (t ':&&: as) (t ':&&: bs))
         => GFunctorPos (Exists k f) v as bs where
  gfmapp v (Exists (x :: f (t ':&&: x)))
    = Exists (gfmapp @_ @f @(VS v) @(t ':&&: x) @(t ':&&: _) v x)

instance forall t v as bs. GFunctorArgPos t v as bs (ContainsTyVar v t)
         => GFunctorPos (Field t) v as bs where
  gfmapp v (Field x) = Field (gfmappf @_ @t @v @as @bs @(ContainsTyVar v t) v x)

class GFunctorArgPos (t :: Atom d (*)) (v :: TyVar d *)
                     (as :: LoT d) (bs :: LoT d)
                     (p :: Bool) where
  gfmappf :: (Interpret (Var v) as -> Interpret (Var v) bs)
          -> Interpret t as -> Interpret t bs

instance (Interpret t as ~ Interpret t bs) => GFunctorArgPos t v as bs False where
  gfmappf _ = id

instance TypeError (Text "Should never get here")
         => GFunctorArgPos ('Kon t) v as bs whatever where
  gfmappf _ = id

instance ( Functor (Interpret f as), Interpret f as ~ Interpret f bs
         , GFunctorArgPos x v as bs (ContainsTyVar v x) )
         => GFunctorArgPos (f :@: x) v as bs True where
  gfmappf f x = fmap (gfmappf @_ @x @v @as @bs @(ContainsTyVar v x) f) x

-- We found the same variable
instance GFunctorArgPos ('Var 'VZ) 'VZ (a ':&&: as) (b ':&&: bs) True where
  gfmappf f x = f x
-- We need to keep looking
instance forall d (v :: TyVar d (*)) n r as s bs isthere.
         GFunctorArgPos ('Var v) n as bs isthere
         => GFunctorArgPos ('Var ('VS v)) ('VS n) (r ':&&: as) (s ':&&: bs) isthere where
  gfmappf f x = gfmappf @d @(Var v) @n @as @bs @isthere f x
-- If we arrive to another we do not want, keep it as it is
instance TypeError (Text "Should never get here")
         => GFunctorArgPos ('Var 'VZ) ('VS n) (r ':&&: as) (r ':&&: bs) True where
  gfmappf _ = id
instance TypeError (Text "Should never get here")
         => GFunctorArgPos ('Var ('VS n)) 'VZ (r ':&&: LoT0) (r ':&&: LoT0) True where
  gfmappf _ = id

-- Alternative implementation
{-
type family EqualTyVar (v :: TyVar d (*)) (w :: TyVar d (*)) :: Bool where
  EqualTyVar v v = True
  EqualTyVar v w = False

class GFunctorVarPos (v :: TyVar d *) (w :: TyVar d *)
                     (as :: LoT d) (bs :: LoT d)
                     (equal :: Bool) where
  gfmappv :: (Interpret (Var w) as -> Interpret (Var w) bs)
          -> Interpret (Var v) as -> Interpret (Var v) bs

instance v ~ w => GFunctorVarPos v w as bs True where
  gfmappv f = f
instance (Interpret (Var v) as ~ Interpret (Var v) bs)
        => GFunctorVarPos v w as bs False where
  gfmappv _ = id

instance forall v w as bs. GFunctorVarPos v w as bs (EqualTyVar v w)
         => GFunctorArgPos (Var v) w as bs True where
  gfmappf = gfmappv @_ @v @w @as @bs @(EqualTyVar v w)
-}
