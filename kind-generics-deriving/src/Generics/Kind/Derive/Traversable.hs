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
module Generics.Kind.Derive.Traversable where

import Data.Proxy
import Generics.Kind

traverseDefault :: (GenericS r f as, GenericS t f bs,
                    GTraversable (RepK f) v a as b bs,
                    Applicative g)
                => Proxy v -> (a -> g b) -> r -> g t
traverseDefault p f = fmap toS . gtraverse p f . fromS

class GTraversable (f :: LoT k -> *) (v :: TyVar k *)
                   (a :: *) (as :: LoT k) (b :: *) (bs :: LoT k) where
  gtraverse :: Applicative g => Proxy v -> (a -> g b) -> f as -> g (f bs)

gtraverse' :: forall as bs f v a b g.
              (GTraversable f v a as b bs, Applicative g)
           => Proxy v -> (a -> g b) -> f as -> g (f bs)
gtraverse' = gtraverse

instance GTraversable U1 v a as b bs where
  gtraverse _ _ U1 = pure U1

instance GTraversable f v a as b bs
         => GTraversable (M1 i c f) v a as b bs where
  gtraverse p v (M1 x) = M1 <$> gtraverse p v x

instance (GTraversable f v a as b bs, GTraversable g v a as b bs)
         => GTraversable (f :+: g) v a as b bs where
  gtraverse p v (L1 x) = L1 <$> gtraverse p v x
  gtraverse p v (R1 x) = R1 <$> gtraverse p v x

instance (GTraversable f v a as b bs, GTraversable g v a as b bs)
         => GTraversable (f :*: g) v a as b bs where
  gtraverse p v (x :*: y) = (:*:) <$> gtraverse p v x <*> gtraverse p v y

instance (Ty c as => GTraversable f v a as b bs, {- Ty c as => -} Ty c bs)
         => GTraversable (c :=>: f) v a as b bs where
  gtraverse p v (C x) = C <$> gtraverse p v x

instance forall f v a as b bs.
         (forall (t :: *). GTraversable f (VS v) a (t ':&&: as) b (t ':&&: bs))
         => GTraversable (E f) v a as b bs where
  gtraverse p v (E (x :: f (t ':&&: x))) = E <$> gtraverse' @(t ':&&: x) @(t :&&: _) (Proxy @(VS v)) v x

instance forall f v a as b bs.
         (forall (t :: *). GTraversable f (VS v) a (t ':&&: as) b (t ':&&: bs))
         => GTraversable (ERefl f) v a as b bs where
  gtraverse p v (ERefl (x :: f (t ':&&: x))) = ERefl <$> gtraverse' @(t ':&&: x) @(t :&&: _) (Proxy @(VS v)) v x

class GTraversableArg (t :: Atom d (*)) (v :: TyVar d *)
                   (a :: *) (as :: LoT d) (b :: *) (bs :: LoT d) where
  gtraversef :: Applicative g => Proxy t -> Proxy v -> Proxy as -> Proxy bs
             -> (a -> g b) -> Ty t as -> g (Ty t bs)

instance forall t v a as b bs. GTraversableArg t v a as b bs
         => GTraversable (F t) v a as b bs where
  gtraverse p v (F x) = F <$> gtraversef (Proxy @t) p (Proxy @as) (Proxy @bs) v x

instance GTraversableArg ('Kon t) v a as b bs where
  gtraversef _ _ _ _ _ = pure

-- We found the same variable
instance GTraversableArg ('Var 'VZ) 'VZ a (a ':&&: as) b (b ':&&: bs) where
  gtraversef _ _ _ _ f x = f x
-- We need to keep looking
instance forall v n a r as b s bs.
         GTraversableArg ('Var v) n a as b bs
         => GTraversableArg ('Var ('VS v)) ('VS n) a (r ':&&: as) b (s ':&&: bs) where
  gtraversef _ _ _ _ f x = gtraversef (Proxy @('Var v)) (Proxy @n) (Proxy @as) (Proxy @bs) f x
-- If we arrive to another we do not want, keep it as it is
instance GTraversableArg ('Var VZ) ('VS n) a (r ':&&: as) b (r ':&&: bs) where
  gtraversef _ _ _ _ _ x = pure x

-- Going through functor
instance forall f x v a as b bs.
         (Traversable f, GTraversableArg x v a as b bs)
         => GTraversableArg (f :$: x) v a as b bs where
  gtraversef _ _ _ _ f x = traverse (gtraversef (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x

instance forall f y x v a as b bs.
         (Traversable (f (Ty y as)), Ty y as ~ Ty y bs, GTraversableArg x v a as b bs)
         => GTraversableArg (f :$: y :@: x) v a as b bs where
  gtraversef _ _ _ _ f x = traverse (gtraversef (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x

instance forall f y1 y2 x v a as b bs.
         (Traversable (f (Ty y1 as) (Ty y2 as)),
          Ty y1 as ~ Ty y1 bs, Ty y2 as ~ Ty y2 bs,
          GTraversableArg x v a as b bs)
         => GTraversableArg (f :$: y1 :@: y2 :@: x) v a as b bs where
  gtraversef _ _ _ _ f x = traverse (gtraversef (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x