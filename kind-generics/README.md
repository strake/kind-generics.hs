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

Let us have a closer look at the definition of the `GenericK` type class. If you have been using other data type-generic programming libraries you might recognize `RepK` as the generalized version of `Rep`, which ties a data type with its description, and the pair of functions `fromK` and `toK` to go back and forth the original values and their generic counterparts.

```haskell
class GenericK (f :: k) (x :: LoT k) where
  type RepK f :: LoT k -> *
  fromK :: f :@@: x -> RepK f x
  toK   :: RepK f x -> f :@@: x
```

But what are those `LoT` and `(:@@:)` which appear there? That is indeed the secret sauce which makes the whole `kind-generics` library work. The name `LoT` comes from *list of types*. It is a type-level version of a regular list, where the `(:)` constructor is replaced by `(:&&:)` and the empty list is represented by `LoT0`. For example:

```haskell
Int :&&: [Bool] :&&: LoT0  -- a list with two basic types
Int :&&: [] :&&: LoT0      -- type constructor may also appear
```

What can you do with such a list of types? You can pass them as type arguments to a type constructor. This is the role of `(:@@:)` (which you can pronounce *of*, or *application*). For example:

```haskell
Either :@@: (Int :&&: Bool :&&: LoT0) = Either Int Bool
Free   :@@: ([]  :&&: Int  :&&: LoT0) = Free [] Int
Int    :@@:                     LoT0 = Int
```

Wait, you cannot apply any list of types to any constructor! Something like `Maybe []` is rejected by the compiler, and so should we reject `Maybe ([] :&&: LoT0)`. To prevent such problems, the list of types is decorated with the *kinds* of all the types inside of it. Going back to the previous examples:

```haskell
Int :&&: [Bool] :&&: LoT0  ::  LoT (* -> * -> *)
Int :&&: [] :&&: LoT0      ::  LoT (* -> (* -> *) -> *)
```

The application operator `(:@@:)` only allows us to apply a list of types of kind `k` to types constructors of the same kind. The shared variable in the head of the type class enforces this invariant also in our generic descriptions.

## Describing fields: the functor `F`

As mentioned in the introduction, `kind-generics` features a more expressive language to describe the types of the fields of data types. We call the description of a specific type an *atom*. The language of atoms reproduces the ways in which you can build a type in Haskell:

1. You can have a constant type `t`, which is represented by `Kon t`.
2. You can mention a variable, which is represented by `V0`, `V1`, and so on. For those interested in the internals, there is a general `Var v` where `v` is a type-level number. The library provides the synonyms for ergonomic reasons.
3. You can take two types `f` and `x` and apply one to the other, `f :@: x`.

For example, suppose the `a` is the name of the first type variable and `b` the name of the second. Here are the corresponding atoms:

```haskell
a            ->  V0
Maybe a      ->  Kon Maybe :@: V0
Either b a   ->  Kon Either :@: V1 :@: V0
b (Maybe a)  ->  V1 :@: (Kon Maybe :@: V0)
```

Since the `Kon f :@: x` pattern is very common, `kind-generics` also allows you to write it as simply `f :$: x`. The names `(:$:)` and `(:@:)` are supposed to resemble `(<$>)` and `(<*>)` from the `Applicative` type class.

The kind of an atom is described by two pieces of information, `Atom d k`. The first argument `d` specifies the amounf of variables that it uses. The second argument `k` tells you the kind of the type you obtain if you replace the variable markers `V0`, `V1`, ... by actual types. For example:

```haskell
V0                     ->  Atom (k -> ks)             k
V1 :@: (Maybe :$: V0)  ->  Atom (* -> (* -> *) -> ks) (*)
```

In the first example, if you tell me the value of the variable `a` regardless of the kind `k`, the library can build a type of kind `k`. In the second example, the usage requires the first variable to be a ground type, and the second one to be a one-parameter type constructor. If you give those types, the library can build a type of kind `*`.

This operation we have just described is embodied by the `Ty` type family. A call looks like `Ty atom lot`, where `atom` is an atom and `lot` a list of types which matches the requirements of the atom. We say that `Ty` *interprets* the `atom`. Going back to the previous examples:

```haskell
Ty V0                    Int                      =  Int
Ty V1 :@: (Maybe :$: V0) (Bool :&&: [] :&&: LoT0) =  [Maybe Bool]
```

This bridge is used in the first of the pattern functors that `kind-generics` add to those from `GHC.Generics`. The pattern functor `F` is used to represent fields in a constructor, where the type is represented by an atom. Compare its definition with the `K1` type from `GHC.Generics`:

```haskell
newtype F  (t :: Atom d (*)) (x :: LoT d) = F { unF :: Ty t x }
newtype K1 i (t ::  *) = K1 { unK1 :: t }
```

At the term level there is almost no difference in the usage, except for the fact that fields are wrapped in the `F` constructor instead of `K1`.

```haskell
instance GenericK Tree (a :&&: LoT0) where
  type RepK Tree = (F (Tree :$: V0) :*: F (Tree :$: V0)) :+: (F V0)

  fromK (Branch l r) = L1 (F l :*: F r)
  fromK (Node   x)   = R1 (F x)
```

On the other hand, separating the atom from the list of types gives us the ability to interpret the same atom with different list of types. This is paramount to classes like `Functor`, in which the same type constructor is applied to different type variables.

## Functors for GADTS: `(:=>:)` and `E`

Generalised Algebraic Data Types, GADTs for short, extend the capabilities of Haskell data types. Once the extension is enabled, constructor gain the ability to constrain the set of allowed types, and to introduce existential types. Here is an extension of the previously-defined `Tree` type to include an annotation in every leaf, each of them with possibly a different type, and also require `Show` for the `a`s:

```haskell
data WeirdTree a where
  WeirdBranch :: WeirdTree a -> WeirdTree a -> WeirdTree a 
  WeirdLeaf   :: Show a => t -> a -> WeirdTree a
```

The family of pattern functors `U1`, `F`, `(:+:)`, and `(:*:)` is not enough. Let us see what other things we use in the representation of `WeirdTree`:

```haskell
instance GenericK WeirdTree (a ':&&: 'LoT0) where
  type RepK WeirdTree
    = F (WeirdTree :$: V0) :*: F (WeirdTree :$: V0)
      :+: E ((Show :$: V1) :=>: (F V0 :*: F V1))
```

Here the `(:=>:)` pattern functor plays the role of `=>` in the definition of the data type. It reuses the same notion of atoms from `F`, but requiring those atoms to give back a constraint instead of a ground type.

But wait a minute! You have just told me that the first type variable is represented by `V0`, and in the representation above `Show a` is transformed into `Show :$: V1`, what is going on? This change stems from `E`, which represents existential quantification. Whenever you go inside an `E`, you gain a new type variable in your list of types. This new variable is put *at the front* of the list of types, shifting all the other one position. In the example above, inside the `E` the atom `V0` points to `t`, and `V1` points to `a`. This approach implies that inside nested existentials the innermost variable corresponds to head of the list of types `V0`.

Unfortunately, at this point you need to write your own conversion functions if you use any of these extended features (pull requests implementing it in Template Haskell are more than welcome).

```haskell
instance GenericK WeirdTree (a ':&&: 'LoT0) where
  type RepK WeirdTree = ...

  fromK (WeirdBranch l r) = L1 $         F l :*: F r
  fromK (WeirdLeaf   a x) = R1 $ E $ C $ F a :*: F x

  toK ...
```

If you have ever done this work in `GHC.Generics`, there is not a big step. You just need to apply the `E` and `C` constructor every time there is an existential or constraint, respectively. However, since the additional information required by those types is implicitly added by the compiler, you do not need to write anything else.

## Implementing a generic operation with `kind-generics`

The last stop in our journey through `kind-generics` is being able to implement a generic operation. At this point we assume that the reader is comfortable with the definition of generic operations using `GHC.Generics`, so only the differences with that style are pointed out.

Take an operation like `Show`. Using `GHC.Generics` style, you create a type class whose instances are the corresponding pattern functors:

```haskell
class GShow (f :: * -> *) where
  gshow :: f x -> String

instance GShow U1 ...
instance Show t => GShow (K1 i t) ...
instance (GShow f, GShow g) => GShow (f :+: g) ...
instance (GShow f, GShow g) => GShow (f :*: g) ...
```

When using `kind-generics`, the type class needs to feature the separation between the head and its type arguments, in a similar way to `GenericK`. In this case, that means extending the class with a new parameter, and reworking the basic cases to include that argument.

```haskell
class GShow (f :: LoT k -> *) (x :: LoT k) where
  gshow :: f :@@: x -> String

instance GShow U1 x ...
instance (GShow f x, GShow g x) => GShow (f :+: g) x ...
instance (GShow f x, GShow g x) => GShow (f :*: g) x ...
```

Now we have the three new constructors. Let us start with `F atom`: when is it `Show`able? Whenever the interpretation of the atom, with the given list of types, satisfies the `Show` constraint. We can use the type family `Ty` to express this fact:

```haskell
instance (Show (Ty a x)) => GShow (F a) x where
  gshow (F x) = show x
```

In the case of existential constraints we do not need to enforce any additional constraints. However, we need to extend our list of types with a new one for the existential. We can do that using the `QuantifiedConstraints` extension introduced in GHC 8.6:

```haskell
{-# language QuantifiedConstraints #-}

instance (forall t. Show f (t :&&: x)) => GShow (E f) x where
  gshow (E x) = gshow x
```

The most interesting case is the one for constraints. If we have a constraint in a constructor, we know that by pattern matching on it we can use the constraint. In other words, we are allowed to assume that the constraint at the left-hand side of `(:=>:)` holds when trying to decide whether `GShow` does. This is again allowed by the `QuantifiedConstraints` extension:

```haskell
{-# language QuantifiedConstraints #-}

instance (Ty c x => GShow f x) => GShow (c :=>: f) x where
  gshow (C x) = gshow x
```

Note that sometimes we cannot implement a generic operation for every GADT. One example is generic equality (which you can find in the module `Generics.Kind.Derive.Eq`): when faced with two values of a constructor with an existential, we cannot move forward, since we have no way of knowing if the types enclosed by each value are the same or not.

## Conclusion and limitations

The `kind-generics` library extends the support for data type-generic programming from `GHC.Generics` to account for kinds different from `*`  and `* -> *` and for GADTs. We have tried to reuse as much information as possible from what the compiler already gives us for free, in particular you can obtain a `GenericK` instance if you already have a `Generic` one.

Although we can now express a larger amount of types and operations, not *all* Haskell data types are expressible in this language. In particular, we cannot have *dependent* kinds, like in the following data type:

```haskell
data Proxy k (d :: k) = Proxy
```

because the kind of the second argument `d` refers to the first argument `k`.