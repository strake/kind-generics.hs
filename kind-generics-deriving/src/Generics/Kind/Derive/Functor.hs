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
module Generics.Kind.Derive.Functor where

import Data.Proxy
import Generics.Kind

fmap1DefaultS :: (GenericS r f as, GenericS t f bs,
                  GFunctor1 (RepK f) v a as b bs)
               => Proxy v -> (a -> b) -> r -> t
fmap1DefaultS p f = toS . gfmap1 p f . fromS

class GFunctor1 (f :: LoT k -> *) (v :: TyVar k *)
                (a :: *) (as :: LoT k) (b :: *) (bs :: LoT k) where
  gfmap1 :: Proxy v -> (a -> b) -> f as -> f bs

gfmap1' :: forall as bs f v a b. (GFunctor1 f v a as b bs)
        => Proxy v -> (a -> b) -> f as -> f bs
gfmap1' = gfmap1

instance GFunctor1 U1 v a as b bs where
  gfmap1 _ _ U1 = U1

instance GFunctor1 f v a as b bs
         => GFunctor1 (M1 i c f) v a as b bs where
  gfmap1 p v (M1 x) = M1 (gfmap1 p v x)

instance (GFunctor1 f v a as b bs, GFunctor1 g v a as b bs)
         => GFunctor1 (f :+: g) v a as b bs where
  gfmap1 p v (L1 x) = L1 (gfmap1 p v x)
  gfmap1 p v (R1 x) = R1 (gfmap1 p v x)

instance (GFunctor1 f v a as b bs, GFunctor1 g v a as b bs)
         => GFunctor1 (f :*: g) v a as b bs where
  gfmap1 p v (x :*: y) = gfmap1 p v x :*: gfmap1 p v y

instance (Ty c as => GFunctor1 f v a as b bs, {- Ty c as => -} Ty c bs)
         => GFunctor1 (c :=>: f) v a as b bs where
  gfmap1 p v (C x) = C (gfmap1 p v x)

instance forall f v a as b bs.
         (forall (t :: *). GFunctor1 f (VS v) a (t ':&&: as) b (t ':&&: bs))
         => GFunctor1 (E f) v a as b bs where
  gfmap1 p v (E (x :: f (t ':&&: x))) = E (gfmap1' @(t ':&&: x) @(t :&&: _) (Proxy @(VS v)) v x)

instance forall f v a as b bs.
         (forall (t :: *). GFunctor1 f (VS v) a (t ':&&: as) b (t ':&&: bs))
         => GFunctor1 (ERefl f) v a as b bs where
  gfmap1 p v (ERefl (x :: f (t ':&&: x))) = ERefl (gfmap1' @(t ':&&: x) @(t :&&: _) (Proxy @(VS v)) v x)

class GFunctorArg1 (t :: Atom d (*)) (v :: TyVar d *)
                   (a :: *) (as :: LoT d) (b :: *) (bs :: LoT d) where
  gfmapf1 :: Proxy t -> Proxy v -> Proxy as -> Proxy bs
          -> (a -> b) -> Ty t as -> Ty t bs

instance forall t v a as b bs. GFunctorArg1 t v a as b bs
         => GFunctor1 (F t) v a as b bs where
  gfmap1 p v (F x) = F (gfmapf1 (Proxy @t) p (Proxy @as) (Proxy @bs) v x)

instance GFunctorArg1 ('Kon t) v a as b bs where
  gfmapf1 _ _ _ _ _ = id

-- We found the same variable
instance GFunctorArg1 ('Var 'VZ) 'VZ a (a ':&&: as) b (b ':&&: bs) where
  gfmapf1 _ _ _ _ f x = f x
-- We need to keep looking
instance forall v n a r as b s bs.
         GFunctorArg1 ('Var v) n a as b bs
         => GFunctorArg1 ('Var ('VS v)) ('VS n) a (r ':&&: as) b (s ':&&: bs) where
  gfmapf1 _ _ _ _ f x = gfmapf1 (Proxy @('Var v)) (Proxy @n) (Proxy @as) (Proxy @bs) f x
-- If we arrive to another we do not want, keep it as it is
instance GFunctorArg1 ('Var VZ) ('VS n) a (r ':&&: as) b (r ':&&: bs) where
  gfmapf1 _ _ _ _ _ x = x

-- Going through functor
instance forall f x v a as b bs.
         (Functor f, GFunctorArg1 x v a as b bs)
         => GFunctorArg1 (f :$: x) v a as b bs where
  gfmapf1 _ _ _ _ f x = fmap (gfmapf1 (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x

instance forall f y x v a as b bs.
         (Functor (f (Ty y as)), Ty y as ~ Ty y bs, GFunctorArg1 x v a as b bs)
         => GFunctorArg1 (f :$: y :@: x) v a as b bs where
  gfmapf1 _ _ _ _ f x = fmap (gfmapf1 (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x

instance forall f y1 y2 x v a as b bs.
         (Functor (f (Ty y1 as) (Ty y2 as)),
          Ty y1 as ~ Ty y1 bs, Ty y2 as ~ Ty y2 bs,
          GFunctorArg1 x v a as b bs)
         => GFunctorArg1 (f :$: y1 :@: y2 :@: x) v a as b bs where
  gfmapf1 _ _ _ _ f x = fmap (gfmapf1 (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x