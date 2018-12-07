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

traverseDefault :: forall f as bs g v.
                   (GenericK f as, GenericK f bs,
                    GTraversable (RepK f) v as bs,
                    Applicative g)
                => Proxy v
                -> (Interpret (Var v) as -> g (Interpret (Var v) bs))
                -> f :@@: as -> g (f :@@: bs)
traverseDefault p f = fmap (toK @_ @f @bs) . gtraverse p f . fromK @_ @f @as

class GTraversable (f :: LoT k -> *) (v :: TyVar k *)
                   (as :: LoT k) (bs :: LoT k) where
  gtraverse :: Applicative g 
            => Proxy v
            -> (Interpret (Var v) as -> g (Interpret (Var v) bs))
            -> f as -> g (f bs)

gtraverse' :: forall as bs f v g.
              (GTraversable f v as bs, Applicative g)
           => Proxy v
           -> (Interpret (Var v) as -> g (Interpret (Var v) bs))
           -> f as -> g (f bs)
gtraverse' = gtraverse

instance GTraversable U1 v as bs where
  gtraverse _ _ U1 = pure U1

instance GTraversable f v as bs
         => GTraversable (M1 i c f) v as bs where
  gtraverse p v (M1 x) = M1 <$> gtraverse p v x

instance (GTraversable f v as bs, GTraversable g v as bs)
         => GTraversable (f :+: g) v as bs where
  gtraverse p v (L1 x) = L1 <$> gtraverse p v x
  gtraverse p v (R1 x) = R1 <$> gtraverse p v x

instance (GTraversable f v as bs, GTraversable g v as bs)
         => GTraversable (f :*: g) v as bs where
  gtraverse p v (x :*: y) = (:*:) <$> gtraverse p v x <*> gtraverse p v y

instance (Interpret c as => GTraversable f v as bs, {- Ty c as => -} Interpret c bs)
         => GTraversable (c :=>: f) v as bs where
  gtraverse p v (SuchThat x) = SuchThat <$> gtraverse p v x

instance forall k f v as bs.
         (forall (t :: k). GTraversable f (VS v) (t ':&&: as) (t ':&&: bs))
         => GTraversable (Exists k f) v as bs where
  gtraverse p v (Exists (x :: f (t ':&&: x)))
    = Exists <$> gtraverse' @(t ':&&: x) @(t :&&: _) (Proxy @(VS v)) v x

class GTraversableArg (t :: Atom d (*)) (v :: TyVar d *)
                      (as :: LoT d) (bs :: LoT d) where
  gtraversef :: Applicative g
             => Proxy t -> Proxy v -> Proxy as -> Proxy bs
             -> (Interpret (Var v) as -> g (Interpret (Var v) bs))
             -> Interpret t as -> g (Interpret t bs)

instance forall t v as bs. GTraversableArg t v as bs
         => GTraversable (Field t) v as bs where
  gtraverse p v (Field x) = Field <$> gtraversef (Proxy @t) p (Proxy @as) (Proxy @bs) v x

instance GTraversableArg ('Kon t) v as bs where
  gtraversef _ _ _ _ _ = pure

-- We found the same variable
instance GTraversableArg ('Var 'VZ) 'VZ (a ':&&: as) (b ':&&: bs) where
  gtraversef _ _ _ _ f x = f x
-- We need to keep looking
instance forall v n r as s bs.
         GTraversableArg ('Var v) n as bs
         => GTraversableArg ('Var ('VS v)) ('VS n) (r ':&&: as) (s ':&&: bs) where
  gtraversef _ _ _ _ f x = gtraversef (Proxy @('Var v)) (Proxy @n) (Proxy @as) (Proxy @bs) f x
-- If we arrive to another we do not want, keep it as it is
instance GTraversableArg ('Var VZ) ('VS n) (r ':&&: as) (r ':&&: bs) where
  gtraversef _ _ _ _ _ x = pure x

-- Going through functor
instance forall f x v as bs.
         (Traversable f, GTraversableArg x v as bs)
         => GTraversableArg (f :$: x) v as bs where
  gtraversef _ _ _ _ f x = traverse (gtraversef (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x

instance forall f y x v as bs.
         ( Traversable (f (Interpret y as)), Interpret y as ~ Interpret y bs
         , GTraversableArg x v as bs )
         => GTraversableArg (f :$: y :@: x) v as bs where
  gtraversef _ _ _ _ f x = traverse (gtraversef (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x

instance forall f y1 y2 x v as bs.
         (Traversable (f (Interpret y1 as) (Interpret y2 as)),
         Interpret y1 as ~ Interpret y1 bs, Interpret y2 as ~ Interpret y2 bs,
          GTraversableArg x v as bs)
         => GTraversableArg (f :$: y1 :@: y2 :@: x) v as bs where
  gtraversef _ _ _ _ f x = traverse (gtraversef (Proxy @x) (Proxy @v) (Proxy @as) (Proxy @bs) f) x