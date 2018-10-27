# `kind-generics`: generic programming for arbitrary kinds and GADTs

Data type-generic programming in Haskell is restricted to types of kind `*` (by using `Generic`) or `* -> *` (by using `Generic1`). This works fine for implementing generic equality or generic printing, notions which are applied to types of kind `*`. But what about having a generic `Bifunctor` or `Contravariant`? We need to extend our language for describing data types to other kinds -- hopefully without having to introduce `Generic2`, `Generic3`, and so on.

The language for describing data types in `GHC.Generics` is also quite restricted. In particular, it can only describe algebraic data types, not the full extent of GADTs. It turns out that both problems are related: if you want to describe a constructor of the form `forall a. blah`, then `blah` must be a data type which takes one additional type variable. As a result, we need to enlarge and shrink the kind at will.

This library, `kind-generics`, provides a new type class `GenericK` and a set of additional functors `F` (from *field*), `C` (from *constraint*), and `E` (from *existential*) which extend the language of `GHC.Generics`. We have put a lot of effort in coming with a simple programming experience, even though the implementation is full of type trickery.

## Short summary for simple data types

GHC has built-in support for data type-generic programming via its `GHC.Generics` module. In order to use those facilities, your data type must implement the `Generic` type class. Fortunately, GHC can automatically derive such instances for algebraic data types. For example:

```haskell
{-# language DeriveGeneric #-}  -- this should be at the top of the file

data Tree a = Branch (Tree a) (Tree a) | Leaf a
            deriving Generic    -- this is the magical line
```

From this `Generic` instance, `kind-generics` can derive another one for its very own `GenericK`. It needs one additional piece of information, though: the description of the data type in the enlarged language of descriptions. The reason for this is that `Generic` does not distinguish whether the type of a field mentions one of the type variables (`a` in this case) or not. But `GenericK` requires so.

Let us look at the `GenericK` instance for `Tree`:

```haskell
instance GenericK Tree (a :&&: LoT0) where
  type RepK Tree = (F (Tree :$: V0) :*: F (Tree :$: V0)) :+: (F V0)
```

In this case we have two constructors, separated by `(:+:)`. The first constructor has two fields, tied together by `(:*:)`. In the description of each field is where the difference with `GHC.Generics` enters the game: you need to describe *each* piece which makes us the type. In this case `Tree :$: V0` says that the type constructor `Tree` is applied to the first type variable. Type variables, in turn, are represented by zero-indexed `V0`, `V1`, and so on.

The other piece of information we need to give `GenericK` is how to separate the type constructor from its arguments. The first line of the instance always takes the name of the type, and then a *list of types* representing each of the arguments. In this case there is only one argument, and thus the list has only one element. In order to get better type inference you might also add the following declaration:

```haskell
instance HeadOf (Tree a) Tree
```

You can finally use the functionality from `kind-generics` and derive some type classes automatically:

```haskell
import Generics.Kind.Derive.Eq
import Generics.Kind.Derive.Functor

instance Eq a => Eq (Tree a) where
  (==) = geq'
instance Functor Tree where
  fmap = fmapDefault
```

## Type variables in a list: `LoT` and `(:@@:)`

## The new functors: `F`, `C` and `E`

## Implementing a generic operation for GADTs