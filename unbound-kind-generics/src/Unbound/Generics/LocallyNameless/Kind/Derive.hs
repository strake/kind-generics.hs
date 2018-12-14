{-# language TypeOperators #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language PolyKinds #-}
{-# language DataKinds #-}
{-# language UndecidableInstances #-}
{-# language QuantifiedConstraints #-}
{-# language GADTs #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language ConstraintKinds #-}
module Unbound.Generics.LocallyNameless.Kind.Derive (
  -- Default definitions for 'Alpha'
  aeqDefK
, fvAnyDefK
, closeDefK
, openDefK
, isPatDefK
, isTermDefK
, isEmbedDefK
, nthPatFindDefK
, namePatFindDefK
, swapsDefK
, lfreshenDefK
, freshenDefK
, acompareDefK
  -- Default definitions for 'Subst'
, buildSubstName
, gsubstDefK
, gsubstsDefK
) where

import Control.Arrow (first)
import Control.Monad (liftM)
import Data.Function (on)
import Data.Functor.Contravariant (Contravariant(..))
import Data.Kind
import Data.List (find)
import Data.Monoid (All(..))
import Type.Reflection

import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Fresh
import Unbound.Generics.LocallyNameless.LFresh
import Unbound.Generics.LocallyNameless.Subst
import Unbound.Generics.PermM
import Generics.Kind

type GenericAlpha a = (GenericK a LoT0, GAlphaK (RepK a) LoT0 LoT0)

aeqDefK :: forall a. (GenericAlpha a)
        => AlphaCtx -> a -> a -> Bool
aeqDefK c = (gaeqK c) `on` (fromK @_ @a @LoT0)
fvAnyDefK :: forall g a. (GenericAlpha a, Contravariant g, Applicative g)
          => AlphaCtx -> (AnyName -> g AnyName) -> a -> g a 
fvAnyDefK c nfn = fmap (toK @_ @a @LoT0) . gfvAnyK c nfn . fromK @_ @a @LoT0
closeDefK :: forall a. (GenericAlpha a)
          => AlphaCtx -> NamePatFind -> a -> a 
closeDefK c b = toK @_ @a @LoT0 . gcloseK c b . fromK @_ @a @LoT0
openDefK :: forall a. (GenericAlpha a)
         => AlphaCtx -> NthPatFind -> a -> a 
openDefK c b = toK @_ @a @LoT0 . gopenK c b . fromK @_ @a @LoT0
isPatDefK :: forall a. (GenericAlpha a)
          => a -> DisjointSet AnyName
isPatDefK = gisPatK . fromK @_ @a @LoT0
isTermDefK :: forall a. (GenericAlpha a)
           => a -> All
isTermDefK = gisTermK . fromK @_ @a @LoT0
isEmbedDefK :: a -> Bool
isEmbedDefK _ = False
nthPatFindDefK :: forall a. (GenericAlpha a)
               => a -> NthPatFind
nthPatFindDefK = gnthPatFindK . fromK @_ @a @LoT0
namePatFindDefK :: forall a. (GenericAlpha a)
                => a -> NamePatFind
namePatFindDefK = gnamePatFindK . fromK @_ @a @LoT0
swapsDefK :: forall a. (GenericAlpha a)
          => AlphaCtx -> Perm AnyName -> a -> a 
swapsDefK ctx perm = toK @_ @a @LoT0 . gswapsK ctx perm . fromK @_ @a @LoT0
lfreshenDefK :: forall m a b. (LFresh m, GenericAlpha a)
             => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b 
lfreshenDefK ctx m cont = glfreshenK ctx (fromK @_ @a @LoT0 m) (cont . toK @_ @a @LoT0)
freshenDefK :: forall m a. (Fresh m, GenericAlpha a)
            => AlphaCtx -> a -> m (a, Perm AnyName) 
freshenDefK ctx = retractFFM . liftM (first (toK @_ @a @LoT0)) . gfreshenK ctx . fromK @_ @a @LoT0
acompareDefK :: forall a. (GenericAlpha a)
             => AlphaCtx -> a -> a -> Ordering
acompareDefK c = (gacompareK c) `on` (fromK @_ @a @LoT0)

-- | The "Generic" representation version of 'Alpha'
class GAlphaK (f :: LoT k -> *) (a :: LoT k) (b :: LoT k) where
  gaeqK :: AlphaCtx -> f a -> f b -> Bool

  gfvAnyK :: (a ~ b, Contravariant g, Applicative g)
         => AlphaCtx -> (AnyName -> g AnyName) -> f a -> g (f a)

  gcloseK :: a ~ b => AlphaCtx -> NamePatFind -> f a -> f a
  gopenK :: a ~ b => AlphaCtx -> NthPatFind -> f a -> f a

  gisPatK :: a ~ b => f a -> DisjointSet AnyName
  gisTermK :: a ~ b => f a -> All

  gnthPatFindK :: a ~ b => f a -> NthPatFind
  gnamePatFindK :: a ~ b => f a -> NamePatFind

  gswapsK :: a ~ b => AlphaCtx -> Perm AnyName -> f a -> f a
  gfreshenK :: (a ~ b, Fresh m) => AlphaCtx -> f a -> FFM m (f a, Perm AnyName)

  glfreshenK :: (a ~ b, LFresh m) => AlphaCtx -> f a -> (f a -> Perm AnyName -> m c) -> m c

  gacompareK :: AlphaCtx -> f a -> f b -> Ordering

instance forall t a b.
         (Alpha (Interpret t a), Alpha (Interpret t b),
          Typeable (Interpret t a), Typeable (Interpret t b))
         => GAlphaK (Field t) a b where
  gaeqK ctx (Field c1) (Field c2) =
    case eqTypeRep (typeRep @(Interpret t a)) (typeRep @(Interpret t b)) of
      Nothing    -> False
      Just HRefl -> aeq' ctx c1 c2
  {-# INLINE gaeqK #-}

  gfvAnyK ctx nfn = fmap Field . fvAny' ctx nfn . unField
  {-# INLINE gfvAnyK #-}

  gcloseK ctx b = Field . close ctx b . unField
  {-# INLINE gcloseK #-}
  gopenK ctx b = Field . open ctx b . unField
  {-# INLINE gopenK #-}

  gisPatK = isPat . unField
  {-# INLINE gisPatK #-}
  gisTermK = isTerm . unField
  {-# INLINE gisTermK #-}

  gnthPatFindK = nthPatFind . unField
  {-# INLINE gnthPatFindK #-}
  gnamePatFindK = namePatFind . unField
  {-# INLINE gnamePatFindK #-}

  gswapsK ctx perm = Field . swaps' ctx perm . unField
  {-# INLINE gswapsK #-}
  gfreshenK ctx = liftM (first Field) . liftFFM . freshen' ctx . unField
  {-# INLINE gfreshenK #-}

  glfreshenK ctx (Field c) cont = lfreshen' ctx c (cont . Field)
  {-# INLINE glfreshenK #-}

  gacompareK ctx (Field c1) (Field c2) =
    case eqTypeRep (typeRep @(Interpret t a)) (typeRep @(Interpret t b)) of
      Nothing    -> compare (SomeTypeRep (typeRep @(Interpret t a)))
                            (SomeTypeRep (typeRep @(Interpret t b)))
      Just HRefl -> acompare' ctx c1 c2

instance GAlphaK f a b => GAlphaK (M1 i d f) a b where
  gaeqK ctx (M1 f1) (M1 f2) = gaeqK ctx f1 f2
  {-# INLINE gaeqK #-}

  gfvAnyK ctx nfn = fmap M1 . gfvAnyK ctx nfn . unM1
  {-# INLINE gfvAnyK #-}

  gcloseK ctx b = M1 . gcloseK ctx b . unM1
  {-# INLINE gcloseK #-}
  gopenK ctx b = M1 . gopenK ctx b . unM1
  {-# INLINE gopenK #-}

  gisPatK = gisPatK . unM1
  {-# INLINE gisPatK #-}
  gisTermK = gisTermK . unM1
  {-# INLINE gisTermK #-}

  gnthPatFindK = gnthPatFindK . unM1
  {-# INLINE gnthPatFindK #-}
  gnamePatFindK = gnamePatFindK . unM1
  {-# INLINE gnamePatFindK #-}

  gswapsK ctx perm = M1 . gswapsK ctx perm . unM1
  {-# INLINE gswapsK #-}
  gfreshenK ctx = liftM (first M1) . gfreshenK ctx . unM1
  {-# INLINE gfreshenK #-}

  glfreshenK ctx (M1 f) cont =
    glfreshenK ctx f (cont . M1)
  {-# INLINE glfreshenK #-}

  gacompareK ctx (M1 f1) (M1 f2) = gacompareK ctx f1 f2

instance GAlphaK U1 a b where
  gaeqK _ctx _ _ = True
  {-# INLINE gaeqK #-}

  gfvAnyK _ctx _nfn _ = pure U1

  gcloseK _ctx _b _ = U1
  gopenK _ctx _b _ = U1

  gisPatK _ = mempty
  gisTermK _ = mempty

  gnthPatFindK _ = mempty
  gnamePatFindK _ = mempty

  gswapsK _ctx _perm _ = U1
  gfreshenK _ctx _ = return (U1, mempty)
  {-# INLINE gfreshenK #-}

  glfreshenK _ctx _ cont = cont U1 mempty

  gacompareK _ctx _ _ = EQ

instance (GAlphaK f a b, GAlphaK g a b) => GAlphaK (f :*: g) a b where
  gaeqK ctx (f1 :*: g1) (f2 :*: g2) =
    gaeqK ctx f1 f2 && gaeqK ctx g1 g2
  {-# INLINE gaeqK #-}

  gfvAnyK ctx nfn (f :*: g) = (:*:) <$> gfvAnyK ctx nfn f
                                   <*> gfvAnyK ctx nfn g
  {-# INLINE gfvAnyK #-}

  gcloseK ctx b (f :*: g) = gcloseK ctx b f :*: gcloseK ctx b g
  {-# INLINE gcloseK #-}
  gopenK ctx b (f :*: g) = gopenK ctx b f :*: gopenK ctx b g
  {-# INLINE gopenK #-}

  gisPatK (f :*: g) = gisPatK f <> gisPatK g
  {-# INLINE gisPatK #-}
  gisTermK (f :*: g) = gisTermK f <> gisTermK g
  {-# INLINE gisTermK #-}

  gnthPatFindK (f :*: g) = gnthPatFindK f <> gnthPatFindK g
  {-# INLINE gnthPatFindK #-}
  gnamePatFindK (f :*: g) = gnamePatFindK f <> gnamePatFindK g
  {-# INLINE gnamePatFindK #-}

  gswapsK ctx perm (f :*: g) =
    gswapsK ctx perm f :*: gswapsK ctx perm g
  {-# INLINE gswapsK #-}

  gfreshenK ctx (f :*: g) = do
    ~(g', perm2) <- gfreshenK ctx g
    ~(f', perm1) <- gfreshenK ctx (gswapsK ctx perm2 f)
    return (f' :*: g', perm1 <> perm2)
  {-# INLINE gfreshenK #-}

  glfreshenK ctx (f :*: g) cont =
    glfreshenK ctx g $ \g' perm2 ->
    glfreshenK ctx (gswapsK ctx perm2 f) $ \f' perm1 ->
    cont (f' :*: g') (perm1 <> perm2)
  {-# INLINE glfreshenK #-}

  gacompareK ctx (f1 :*: g1) (f2 :*: g2) =
    (gacompareK ctx f1 f2) <> (gacompareK ctx g1 g2)

instance (GAlphaK f a b, GAlphaK g a b) => GAlphaK (f :+: g) a b where
  gaeqK ctx  (L1 f1) (L1 f2) = gaeqK ctx f1 f2
  gaeqK ctx  (R1 g1) (R1 g2) = gaeqK ctx g1 g2
  gaeqK _ctx _       _       = False
  {-# INLINE gaeqK #-}

  gfvAnyK ctx nfn (L1 f) = fmap L1 (gfvAnyK ctx nfn f)
  gfvAnyK ctx nfn (R1 g) = fmap R1 (gfvAnyK ctx nfn g)
  {-# INLINE gfvAnyK #-}

  gcloseK ctx b (L1 f) = L1 (gcloseK ctx b f)
  gcloseK ctx b (R1 g) = R1 (gcloseK ctx b g)
  {-# INLINE gcloseK #-}
  gopenK ctx b (L1 f) = L1 (gopenK ctx b f)
  gopenK ctx b (R1 g) = R1 (gopenK ctx b g)
  {-# INLINE gopenK #-}

  gisPatK (L1 f) = gisPatK f
  gisPatK (R1 g) = gisPatK g
  {-# INLINE gisPatK #-}

  gisTermK (L1 f) = gisTermK f
  gisTermK (R1 g) = gisTermK g
  {-# INLINE gisTermK #-}

  gnthPatFindK (L1 f) = gnthPatFindK f
  gnthPatFindK (R1 g) = gnthPatFindK g
  {-# INLINE gnthPatFindK #-}

  gnamePatFindK (L1 f) = gnamePatFindK f
  gnamePatFindK (R1 g) = gnamePatFindK g
  {-# INLINE gnamePatFindK #-}

  gswapsK ctx perm (L1 f) = L1 (gswapsK ctx perm f)
  gswapsK ctx perm (R1 f) = R1 (gswapsK ctx perm f)
  {-# INLINE gswapsK #-}

  gfreshenK ctx (L1 f) = liftM (first L1) (gfreshenK ctx f)
  gfreshenK ctx (R1 f) = liftM (first R1) (gfreshenK ctx f)
  {-# INLINE gfreshenK #-}

  glfreshenK ctx (L1 f) cont =
    glfreshenK ctx f (cont . L1)
  glfreshenK ctx (R1 g) cont =
    glfreshenK ctx g (cont . R1)
  {-# INLINE glfreshenK #-}

  gacompareK _ctx (L1 _) (R1 _)   = LT
  gacompareK _ctx (R1 _) (L1 _)   = GT
  gacompareK ctx  (L1 f1) (L1 f2) = gacompareK ctx f1 f2
  gacompareK ctx  (R1 g1) (R1 g2) = gacompareK ctx g1 g2
  {-# INLINE gacompareK #-}

instance ((Interpret c a, Interpret c b) => GAlphaK f a b)
         => GAlphaK (c :=>: f) a b where
  gaeqK ctx (SuchThat f1) (SuchThat f2) = gaeqK ctx f1 f2
  {-# INLINE gaeqK #-}

  gfvAnyK ctx nfn (SuchThat f) = fmap SuchThat (gfvAnyK ctx nfn f)
  {-# INLINE gfvAnyK #-}

  gcloseK ctx b (SuchThat f) = SuchThat (gcloseK ctx b f)
  {-# INLINE gcloseK #-}
  gopenK ctx b (SuchThat f) = SuchThat (gopenK ctx b f)
  {-# INLINE gopenK #-}

  gisPatK (SuchThat f) = gisPatK f
  {-# INLINE gisPatK #-}

  gisTermK (SuchThat f) = gisTermK f
  {-# INLINE gisTermK #-}

  gnthPatFindK (SuchThat f) = gnthPatFindK f
  {-# INLINE gnthPatFindK #-}

  gnamePatFindK (SuchThat f) = gnamePatFindK f
  {-# INLINE gnamePatFindK #-}

  gswapsK ctx perm (SuchThat f) = SuchThat (gswapsK ctx perm f)
  {-# INLINE gswapsK #-}

  gfreshenK ctx (SuchThat f) = liftM (first SuchThat) (gfreshenK ctx f)
  {-# INLINE gfreshenK #-}

  glfreshenK ctx (SuchThat f) cont = glfreshenK ctx f (cont . SuchThat)
  {-# INLINE glfreshenK #-}

  gacompareK ctx (SuchThat f1) (SuchThat f2) = gacompareK ctx f1 f2
  {-# INLINE gacompareK #-}

instance (forall (t1 :: k) (t2 :: k). GAlphaK f (t1 :&&: a) (t2 :&&: b))
         => GAlphaK (Exists k f) a b where

  gaeqK ctx (Exists f1) (Exists f2) = gaeqK ctx f1 f2
  {-# INLINE gaeqK #-}

  gfvAnyK ctx nfn (Exists f) = fmap Exists (gfvAnyK ctx nfn f)
  {-# INLINE gfvAnyK #-}

  gcloseK ctx b (Exists f) = Exists (gcloseK ctx b f)
  {-# INLINE gcloseK #-}
  gopenK ctx b (Exists f) = Exists (gopenK ctx b f)
  {-# INLINE gopenK #-}

  gisPatK (Exists f) = gisPatK f
  {-# INLINE gisPatK #-}

  gisTermK (Exists f) = gisTermK f
  {-# INLINE gisTermK #-}

  gnthPatFindK (Exists f) = gnthPatFindK f
  {-# INLINE gnthPatFindK #-}

  gnamePatFindK (Exists f) = gnamePatFindK f
  {-# INLINE gnamePatFindK #-}

  gswapsK ctx perm (Exists f) = Exists (gswapsK ctx perm f)
  {-# INLINE gswapsK #-}

  gfreshenK ctx (Exists f) = liftM (first Exists) (gfreshenK ctx f)
  {-# INLINE gfreshenK #-}

  glfreshenK ctx (Exists f) cont = glfreshenK ctx f (cont . Exists)
  {-# INLINE glfreshenK #-}

  gacompareK ctx (Exists f1) (Exists f2) = gacompareK ctx f1 f2

gsubstDefK :: forall a b. (GenericK a LoT0, GSubstK b (RepK a) LoT0, Subst b a)
           => Name b -> b -> a -> a
gsubstDefK n u x =
  if (isFreeName n)
  then case (isvar x :: Maybe (SubstName a b)) of
    Just (SubstName m) | m == n -> u
    _ -> case (isCoerceVar x :: Maybe (SubstCoerce a b)) of
      Just (SubstCoerce m f) | m == n -> maybe x id (f u)
      _ -> toK @_ @a @LoT0 $ gsubstK n u (fromK @_ @a @LoT0 x)
  else error $ "Cannot substitute for bound variable " ++ show n

gsubstsDefK :: forall a b. (GenericK a LoT0, GSubstK b (RepK a) LoT0, Subst b a)
            => [(Name b, b)] -> a -> a
gsubstsDefK ss x
  | all (isFreeName . fst) ss =
    case (isvar x :: Maybe (SubstName a b)) of
      Just (SubstName m) | Just (_, u) <- find ((==m) . fst) ss -> u
      _ -> case isCoerceVar x :: Maybe (SubstCoerce a b) of
          Just (SubstCoerce m f) | Just (_, u) <- find ((==m) . fst) ss -> maybe x id (f u)
          _ -> toK @_ @a @LoT0 $ gsubstsK ss (fromK @_ @a @LoT0 x)
  | otherwise =
    error $ "Cannot substitute for bound variable in: " ++ show (map fst ss)

buildSubstName :: forall a b. (Typeable a, Typeable b)
               => Name a -> Maybe (SubstName a b)
buildSubstName x = case eqTypeRep (typeRep @a) (typeRep @b) of
  Nothing    -> Nothing
  Just HRefl -> Just (SubstName x)

class GSubstK b (f :: LoT k -> *) (a :: LoT k) where
  gsubstK :: Name b -> b -> f a -> f a
  gsubstsK :: [(Name b, b)] -> f a -> f a

instance Subst b (Interpret t a) => GSubstK b (Field t) a where
  gsubstK nm val = Field . subst nm val . unField
  gsubstsK ss = Field . substs ss . unField

instance GSubstK b f a => GSubstK b (M1 i c f) a where
  gsubstK nm val = M1 . gsubstK nm val . unM1
  gsubstsK ss = M1 . gsubstsK ss . unM1

instance GSubstK b U1 a where
  gsubstK _nm _val _ = U1
  gsubstsK _ss _ = U1

instance (GSubstK b f a, GSubstK b g a) => GSubstK b (f :*: g) a where
  gsubstK nm val (f :*: g) = gsubstK nm val f :*: gsubstK nm val g
  gsubstsK ss (f :*: g) = gsubstsK ss f :*: gsubstsK ss g

instance (GSubstK b f a, GSubstK b g a) => GSubstK b (f :+: g) a where
  gsubstK nm val (L1 f) = L1 $ gsubstK nm val f
  gsubstK nm val (R1 g) = R1 $ gsubstK nm val g

  gsubstsK ss (L1 f) = L1 $ gsubstsK ss f
  gsubstsK ss (R1 g) = R1 $ gsubstsK ss g

instance ((Interpret c a) => GSubstK b f a) => GSubstK b (c :=>: f) a where
  gsubstK nm val (SuchThat f) = SuchThat $ gsubstK nm val f
  gsubstsK ss (SuchThat f) = SuchThat $ gsubstsK ss f

instance (forall (t :: k). GSubstK b f (t :&&: a)) => GSubstK b (Exists k f) a where
  gsubstK nm val (Exists f) = Exists $ gsubstK nm val f
  gsubstsK ss (Exists f) = Exists $ gsubstsK ss f