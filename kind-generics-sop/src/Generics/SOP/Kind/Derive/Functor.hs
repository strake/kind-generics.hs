{-# language GADTs                 #-}
{-# language PolyKinds             #-}
{-# language ScopedTypeVariables   #-}
{-# language FlexibleContexts      #-}
{-# language TypeOperators         #-}
{-# language DataKinds             #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeApplications      #-}
{-# language FlexibleInstances     #-}
{-# language UndecidableInstances  #-}
{-# language AllowAmbiguousTypes   #-}
module Generics.SOP.Kind.Derive.Functor where

import Data.PolyKinded.Functor
import Data.Proxy
import Generics.SOP.Kind

kfmapDefault :: forall k (f :: k) v as bs.
                (GenericK f as, GenericK f bs, AllAtoms (GFunctorArg v 'Co as bs) (CodeK f))
             => Mappings v as bs -> f :@@: as -> f :@@: bs
kfmapDefault v = toK @k @f @bs . gfmap v . fromK @k @f @as

gfmap :: forall k (f :: DataType k) v as bs. AllAtoms (GFunctorArg v 'Co as bs) f
      => Mappings v as bs -> RepK f as -> RepK f bs
gfmap v = goS
  where
    goS :: forall (g :: DataType k). AllAtoms (GFunctorArg v 'Co as bs) g
        => NS (NB as) g -> NS (NB bs) g
    goS (Z (x :: NB as b)) = Z (goB x)
    goS (S x) = S (goS x)

    goB :: forall (b :: Branch k). AllAtomsB (GFunctorArg v 'Co as bs) b
        => NB as b -> NB bs b
    -- goB v (SuchThat_ x) = SuchThat_ (goB v x)
    goB (SuchThat_ _) = error "constraints are not supported"
    -- goB v (Exists_ x) = Exists_ (goB ((id :^: v) :: Mappings ('Co ': v) (t ':&&: cs) (t ':&&: ds)) x)
    goB (Exists_ _) = error "existentials are not supported"
    goB (Fields_ x) = Fields_ (goP x)

    goP :: forall (d :: Fields k). AllAtomsP (GFunctorArg v 'Co as bs) d
        => NP (NA as) d -> NP (NA bs) d
    goP Nil = Nil
    goP ((Atom_ x :: NA as fl) :* xs) = Atom_ (gfmapf (Proxy @fl) (Proxy @'Co) v x) :* goP xs

class GFunctorArg (v :: Variances) (intended :: Variance)
                  (as :: LoT d) (bs :: LoT d) (t :: Atom d (*)) where
  gfmapf :: Proxy t -> Proxy intended
         -> Mappings v as bs
         -> Mapping intended (Interpret t as) (Interpret t bs)

-- COPIED STRAIGHT FROM KIND-GENERICS (WITHOUT SOP)

instance GFunctorArg v 'Co as bs ('Kon t) where
  gfmapf _ _ _ = id
instance GFunctorArg v 'Contra as bs ('Kon t) where
  gfmapf _ _ _ = id

instance GFunctorArg (r ': v) r (a ':&&: as) (b ':&&: bs) ('Var 'VZ) where
  gfmapf _ _ (f :^: _) = f

instance forall vr pre v intended a as b bs.
         GFunctorArg v intended as bs ('Var vr)
         => GFunctorArg (pre ': v) intended (a ':&&: as) (b ':&&: bs) ('Var ('VS vr)) where
  gfmapf _ _ (_ :^: rest) = gfmapf (Proxy @('Var vr)) (Proxy @intended) rest

instance forall f x v v1 as bs.
         (KFunctor f '[v1] (Interpret x as ':&&: 'LoT0) (Interpret x bs ':&&: 'LoT0),
          GFunctorArg v v1 as bs x)
         => GFunctorArg v 'Co as bs (f :$: x) where
  gfmapf _ _ v = kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^: M0)

instance forall f x y v v1 v2 as bs.
         (KFunctor f '[v1, v2] (Interpret x as ':&&: Interpret y as ':&&: 'LoT0)
                               (Interpret x bs ':&&: Interpret y bs ':&&: 'LoT0),
          GFunctorArg v v1 as bs x, GFunctorArg v v2 as bs y)
         => GFunctorArg v 'Co as bs (f :$: x ':@: y) where
  gfmapf _ _ v = kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^:
                        gfmapf (Proxy @y) (Proxy @v2) v :^: M0)

instance forall f x y z v v1 v2 v3 as bs.
         (KFunctor f '[v1, v2, v3] (Interpret x as ':&&: Interpret y as ':&&: Interpret z as ':&&: 'LoT0)
                                   (Interpret x bs ':&&: Interpret y bs ':&&: Interpret z bs ':&&: 'LoT0),
          GFunctorArg v v1 as bs x, GFunctorArg v v2 as bs y, GFunctorArg v v3 as bs z)
         => GFunctorArg v 'Co as bs (f :$: x ':@: y ':@: z) where
  gfmapf _ _ v = kfmap (gfmapf (Proxy @x) (Proxy @v1) v :^:
                        gfmapf (Proxy @y) (Proxy @v2) v :^:
                        gfmapf (Proxy @z) (Proxy @v3) v :^: M0)
