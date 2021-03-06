# `kind-generics-th`: Template Haskell support for generating `GenericK` instances

This package provides Template Haskell functionality to automatically derive
`GenericK` instances. Currently, this only supports the version of `GenericK`
as found in the `kind-generics` library. (The `GenericK` class found in
`kind-generics-sop` is not supported at the moment.)

## How to use this library

To derive instances of `GenericK` for a data type, simply pass the Template
Haskell–quoted `Name` of the type to the `deriveGenericK` function, as in the
following example:

```haskell
$(deriveGenericK ''Either)
```

If you wish to pass a data family instance, one can pass the name of a
constructor belonging to the particular family instance, such as in the
following example:

```haskell
data family Foo a b
data instance Foo Int b = MkFooInt b

$(deriveGenericK 'MkFooInt)
```

You will likely need to enable most of these language extensions in order for
GHC to accept the generated code:

* `DataKinds`
* `EmptyCase` (if using an empty data type)
* `FlexibleInstances`
* `MultiParamTypeClasses`
* `PolyKinds` (if using a poly-kinded data type)
* `TemplateHaskell`
* `TypeFamilies`

## How many `GenericK` instances are generated

`deriveGenericK` typically generates multiple `GenericK` instances per data
type, as there is one `GenericK` instance per partial application of a data
type constructor. For instance, `$(deriveGenericK ''Either)` will generate
three `GenericK` instances:

```haskell
instance GenericK (Either a b) where ...
instance GenericK (Either a)   where ...
instance GenericK Either       where ...
```

Not every data type can be partially applied all the way in this fashion,
however. Some notable counterexamples are:

1. Data family instances. In the following example:

   ```haskell
   data family Bar a b
   data instance Bar a a = MkBar a
   ```

   One cannot partially apply to `Bar a a` to simply `Bar a`, so
   `$(deriveGenericK 'MkBar)` will only generate a single instance for
   `GenericK (Bar a a)`.
2. Dependent kinds. `kind-generics` is not currently capable of representing
   data types such as the following in their full generality:

   ```haskell
   data Baz k (a :: k)
   ```

   Because the `k` type variable is used in the kind of `a` (i.e., it is used
   in a visible, dependent fashion). As a consequence,
   `$(deriveGenericK ''Baz)` will only generate the following instances:

   * `instance GenericK (Baz k a)`
   * `instance GenericK (Baz k)  `
3. Data types with type family applications. In the following example:

   ```haskell
   type family Fam a
   newtype WrappedFam a = WrapFam (Fam a)
   ```

   It is impossible to write a `GenericK` instance for a partial application
   of `WrappedFam`, since the representation type would necessarily need to
   partially apply `Fam`, which GHC does not permit. Therefore,
   `$(deriveGenericK ''WrappedFam)` will only generate a single instance for
   `GenericK (WrappedFam a)`.

   There are some uses of type families that are not supported altogether.
   For instance, if a type family is applied to an _existentially_ quantified
   type variable, as in the following example:

   ```haskell
   data ExFam where
     MkExFam :: forall a. Fam a -> ExFam
   ```

   Representing `ExFam` would fundamentally require a partial application of
   `Fam`, as `type RepK ExFam = Exists * (Field (Fam :$: Var0))`. As a result,
   it is impossible to give `ExFam` a `GenericK` instance.

   Note that not all type families are problematic. For instance:

   ```haskell
   type family Fam2 :: * -> *
   newtype WrappedFam2 a = WrapFam2 (Fam2 a)
   ```

   In this example, `Fam2` is perfectly fine to partially apply, so
   `$(deriveGenericK ''WrappedFam2)` will generate two instances (as opposed
   to just one, as was the case for `WrappedFam`).

## Limitations

`kind-generics` is capable of representing a wide variety of data types. The
Template Haskell machinery in this library makes a best-effort attempt to
automate the creation of most of these instances, but there are a handful of
corner cases that it does not handle well. This section documents all of the
known limitations of `deriveGenericK`:

1. Data constructors with rank-_n_ field types (e.g., `(forall a. a -> a)`)
   are currently not supported.
2. Data constructors with unlifted field types (e.g., `Int#` or `(# Bool #)`)
   are unlikely to work.
3. GADTs that make use of certain forms of kind equalities are currently not
   supported. For example:

   ```haskell
   data Quux (a :: k) where
     MkQuux :: forall (a :: *). Maybe a -> Quux a
   ```

   If one were to rewrite `Quux` to make the existential quantification
   explicit, it would look like this:

   ```haskell
   data Quux (a :: k) =
     forall (a' :: *). (k ~ Type, a' ~~ a) => MkQuux (Maybe a')
   ```

   Therefore, we ought to get a `GenericK` instance like this:

   ```haskell
   instance GenericK (Quux :: k -> *) where
     type RepK (Quux :: k -> *) =
       Exists *
         ((Kon (k ~ Type) :&: (Var0 :~~: Var1)) :=>: Field (Maybe :$: Var0))
     ...
   ```

   Devising an algorithm that converts the original GADT definition of `Quux`
   into the explicitly existential form is not straightforward, however. In
   particular, `deriveGenericK` only detects the `k ~ *` part correctly at the
   moment, so it will generate an ill kinded instance for `Quux`.
