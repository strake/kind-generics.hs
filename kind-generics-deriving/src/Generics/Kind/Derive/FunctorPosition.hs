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

fmapDefaultPos :: (GenericS r f as, GenericS t f bs,
                   GFunctorPos (RepK f) v a as b bs)
               => Proxy v -> (a -> b) -> r -> t
fmapDefaultPos p f = toS . gfmapp p f . fromS

class GFunctorPos (f :: LoT k -> *) (v :: TyVar k *)
                (a :: *) (as :: LoT k) (b :: *) (bs :: LoT k) where
  gfmapp :: Proxy v -> (a -> b) -> f as -> f bs

gfmapp' :: forall as bs f v a b. (GFunctorPos f v a as b bs)
        => Proxy v -> (a -> b) -> f as -> f bs
gfmapp' = gfmapp

instance GFunctorPos U1 v a as b bs where
  gfmapp _ _ U1 = U1

instance GFunctorPos f v a as b bs
         => GFunctorPos (M1 i c f) v a as b bs where
  gfmapp p v (M1 x) = M1 (gfmapp p v x)

instance (GFunctorPos f v a as b bs, GFunctorPos g v a as b bs)
         => GFunctorPos (f :+: g) v a as b bs where
  gfmapp p v (L1 x) = L1 (gfmapp p v x)
  gfmapp p v (R1 x) = R1 (gfmapp p v x)

instance (GFunctorPos f v a as b bs, GFunctorPos g v a as b bs)
         => GFunctorPos (f :*: g) v a as b bs where
  gfmapp p v (x :*: y) = gfmapp p v x :*: gfmapp p v y

instance (Ty c as => GFunctorPos f v a as b bs, {- Ty c as => -} Ty c bs)
         => GFunctorPos (c :=>: f) v a as b bs where
  gfmapp p v (C x) = C (gfmapp p v x)

instance forall f v a as b bs.
         (forall (t :: *). GFunctorPos f (VS v) a (t ':&&: as) b (t ':&&: bs))
         => GFunctorPos (E f) v a as b bs where
  gfmapp p v (E (x :: f (t ':&&: x))) = E (gfmapp' @(t ':&&: x) @(t :&&: _) (Proxy @(VS v)) v x)

instance forall f v a as b bs.
         (forall (t :: *). GFunctorPos f (VS v) a (t ':&&: as) b (t ':&&: bs))
         => GFunctorPos (ERefl f) v a as b bs where
  gfmapp p v (ERefl (x :: f (t ':&&: x))) = ERefl (gfmapp' @(t ':&&: x) @(t :&&: _) (Proxy @(VS v)) v x)

class GFunctorArgPos (t :: Atom d (*)) (v :: TyVar d *)
                   (a :: *) (as :: LoT d) (b :: *) (bs :: LoT d) where
  gfmappf :: Proxy t -> Proxy v -> Proxy as -> Proxy bs
          -> (a -> b) -> Ty t as -> Ty t bs

instance forall t v a as b bs. GFunctorArgPos t v a as b bs
         => GFunctorPos (F t) v a as b bs where
  gfmapp p v (F x) = F (gfmappf (Proxy @t) p (Proxy @as) (Proxy @bs) v x)

instance GFunctorArgPos ('Kon t) v a as b bs where
  gfmappf _ _ _ _ _ = id

-- We found the same variable
instance GFunctorArgPos ('Var 'VZ) 'VZ a (a ':&&: as) b (b ':&&: bs) where
  gfmappf _ _ _ _ f x = f x
-- We need to keep looking
instance forall v n a r as b s bs.
         GFunctorArgPos ('Var v) n a as b bs
         => GFunctorArgPos ('Var ('VS v)) ('VS n) a (r ':&&: as) b (s ':&&: bs) where
  gfmappf _ _ _ _ f x = gfmappf (Proxy @('Var v)) (Proxy @n) (Proxy @as) (Proxy @bs) f x
-- If we arrive to another we do not want, keep it as it is
instance GFunctorArgPos ('Var VZ) ('VS n) a (r ':&&: as) b (r ':&&: bs) where
  gfmappf _ _ _ _ _ x = x

-- Going through functor
instance forall f x v a as b bs.
         (Functor f, GFunctorArgPos x v a as b bs)
         => GFunctorArgPos (f :$: x) v a as b bs where
  gfmappf _ _ _ _ f x = fmap (gfmappf (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x

instance forall f y x v a as b bs.
         (Functor (f (Ty y as)), Ty y as ~ Ty y bs, GFunctorArgPos x v a as b bs)
         => GFunctorArgPos (f :$: y :@: x) v a as b bs where
  gfmappf _ _ _ _ f x = fmap (gfmappf (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x

instance forall f y1 y2 x v a as b bs.
         (Functor (f (Ty y1 as) (Ty y2 as)),
          Ty y1 as ~ Ty y1 bs, Ty y2 as ~ Ty y2 bs,
          GFunctorArgPos x v a as b bs)
         => GFunctorArgPos (f :$: y1 :@: y2 :@: x) v a as b bs where
  gfmappf _ _ _ _ f x = fmap (gfmappf (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x