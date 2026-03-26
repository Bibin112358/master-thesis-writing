# Master Outline

## Abstract

## Acknowledgements


## Introduction

### Background

### Motivation

### Contribution


## Upgrading Boogie

### State before

### Methodology

### Changes

#### Normal changes

#### SMT change

#### CLI change

## Why did we choose Boogie Maps

## Support Boogie Maps


### Semantics of Boogie Maps

[TODO ref Boogie manual]
[TODO ref git issue claiming outdated manual]

#### Select

Arguably, the most important operation of Boogie Maps is selecting from a map.
This operation might also be known under different names,
like get [TODO ref, Java?], read [TODO ref array axioms], apply [TODO ref lambda calculus], [TODO more?]

We will use select from now on, as the Boogie developers use this word as well [TODO ref Boogie manual]


### Goals to Support

#### Want
- parameterized

#### Ok Limitations
- polymorphic
- arbitrary nesting levels


### SMT VC axioms


### Where to start

Boogie Maps are values.
So the first step is to adjust the value type in our semantics to include Boogie Maps.
This is the current value datatype in the semantics:

```haskell
datatype lit =  LBool bool  | LInt int | LReal real

text \<open>The values (and as a result the semantics) are parametrized by the carrier type 'a for the 
abstract values (values that have a type constructed via type constructors)\<close>

datatype 'a val = LitV lit | AbsV (the_absv: 'a)
```

We can see a literal constructor (for boolean, integers and real numbers) and an Isabelle type parameterized constructor for the abstract values
TODO ref to Boogie Abstract values section

We want to adjust this datatype with a new constructor:

```haskell
datatype 'a val = LitV lit | AbsV (the_absv: 'a) | MapV ?
```

The question now is, what should we put in place of `?`?


### Some initial ideas and why they don't work

Intuitively we would want something like this:

```haskell
datatype 'a val = LitV lit | AbsV (the_absv: 'a) | MapV "'a val ⇒ 'a val"
```

But Isabelle rejects this.
This is not a technical limitation, but a logical one.

It contradicts Cantor's theorem, as the cardinality for `"'a val ⇒ 'a val"` is strictly larger than `'a val`,
but `MapV` would provide an injective function from `"'a val ⇒ 'a val"` to `'a val`.
[TODO explain more in detail?]

Note, that the problem is only the recursive occurrence of `"'a val"` as the domain of the function, not the image, e.g.
`MapV "'a val ⇒ bool"` is not fine, whereas `MapV "bool ⇒ 'a val"` is fine.


### Solution [Draft]

The main idea to resolve the above mentioned issue, is to "explicitly unroll" the recursion on the left-hand-side,
and thereby creating different levels of maps.
Level 0: Just primitive values, meaning literal values and abstract values.
Level 1: Maps that take Level 0 values as keys and Level 0 or Level 1 values as map values.
Level 2: Maps that take Level 0 or Level 1 values as keys and Level 0, 1 or 2 values as map values.

In general:
Level n: Maps that take values of Level <= n-1 as values as keys and have map values of level <= n.

[TODO visualization]

Note, it is important to include all previous levels, as we want to be able to model maps
from level 0 to level 2 and vice versa, e.g.
`[int][[int]int]int` and `[[[int]int]int]int`

With this approach, one has to explicitly tell define how many levels one wants when defining the semantics.


#### Program dependent semantics [Early Notes]

- [TODO currently fixed at 3 levels]
- [TODO explain program dependent semantics or just limitation]


#### Datatype [Draft]

This could be achieved with something like this:

```haskell
datatype ’a val0 = LitV0 lit | AbsV0 (the_absv: ’a)
datatype ’a val1 = MapV1 "'a val0 => ('a val1 + ’a val0)"
datatype ’a val2 = MapV2 "('a val1 + ’a val0) => ('a val2 + 'a val1 + ’a val0)"
datatype ’a val3 = MapV3 "('a val2 + 'a val1 + ’a val0) => ('a val3 + 'a val2 + 'a val1 + ’a val0)"
```

To avoid creating many similar datatypes, we introduced a helper datatype
and then build the different levels using type synonyms:

```haskell
(* TODO explain L *)
datatype ’k L = FunL "’k ⇒ ’k L + ’k"

datatype ’a val0 = LitV0 lit | AbsV0 (the_absv: ’a)
type synonym ’a val1 = "’a val0 L"
type_synonym 'a val2 = "('a val1 + 'a val0) L"
type_synonym 'a val3 = "(’a val2 + 'a val1 + 'a val0) L"
type synonym ’a val3210 = "’a val3 + ’a val2 + 'a val1 + 'a val0"
```

To marry this with the current the value datatype, we extend it with a generic MapV constructor,
using a second type parameter `'m`, that is instantiated later.
```haskell
datatype ('a, 'm) val = LitV lit | AbsV (the_absv: 'a) | MapV 'm
```

And then we can instantiate it with our semantics of with a fixed amount of levels.

```haskell
type synonym ’a val321  = "’a val3 + ’a val2 + ’a val1"
type synonym ’a valn = "(’a, ’a val321) val"
```

Note, we explicitly exclude `'a val0`, as these are primitive values
and therefore make little sense under `MapV`.

We are far from done though, as we need to define required functionality
and make sure, that these definitions fulfill our requirements,
most prominently our array axioms.


#### Type of Val

One important function for values, which will also be relevant for our map semantics [TODO ref to store and wf],
is the `type_of_val` function.
As one might guess, it returns the boogie type of boogie values.
To support boogie maps, we first have to extend the current type definition with a Boogie Map Type:

```haskell
datatype prim_ty 
 = TBool | TInt | TReal

type_synonym tcon_id = string (* type constructor id *)

datatype ty
  = TVar nat | (* type variables as de-bruijn indices *)
    TPrim prim_ty | (* primitive types *)
    TCon tcon_id "ty list" (* type constructor *) |
    TMap ty ty (* maps *)
```

Note, since we only support single-arity maps [TODO ref to goals],
it is enough to represent the map as two types, one for the key and one for the value.
Otherwise, we would need a list of types for the keys.


The next thing is implementing the case to get the types for maps.
Here we already run into trouble, since our modelling is too general.
For example, if we have a map of val1, then this could map
from bools and ints to bools and ints, and it would not be clear from the outside,
if it is supposed to be a `[int]int, [bool]bool, [int]bool, [bool]int` or some other map.

To mitigate this issue, we explicitly store the supposed type of the key and value in the datatype:

```haskell
datatype ’k L = FunL "’k ⇒ ’k L + ’k" ty ty
```

Of course, there is no semantic connection between the provided types and the function,
e.g. both `ty` could be `TPrim TBool`, but the function could still map bools to ints.
This will be resolved later [TODO ref wf].

At least, we are now able to extract the type of the map,
the defintions can be found in the appendix [TODO ref.]

Relevant for the next few sections are the function to extract the key and value type from a map type:

```haskell
fun key_ty where "key_ty (TMap tk _) = tk" | "key_ty _ = undefined"
fun val_ty where "val_ty (TMap _ tv) = tv" | "val_ty _ = undefined"
```


#### Constrained Types [Early Notes]

- current definition too general
- will need some additional invariants that the map values need to fulfill
- with this invariants, we can create a constrained type using typedef [TODO ref to Typedef and lifting] [TODO ref typdef in Isabelle]


#### Type Safety [Early Draft]

From [TODO ref SMT VC axioms, specific axiom] we need the property,
that if we select from a map using a key of the key type of the map,
then the result is of the value type of the map:

```haskell
(∀k. type_of_val k = key_ty (type_of_val m) --> type_of_val (selectImpl m k) = val_ty (type_of_val m))
```

(assuming we have `selectImpl`, which we will see later [TODO ref Select]).

This property does not hold for our current `valn` definition,
as it just maps from values to values, regardless of their type.

[TODO mention why it is hard to do that structurally using datatypes only?]

We will actually enforce a stronger condition:
```haskell
(∀k. type_of_val (selectImpl m k) = val_ty (type_of_val m))
```

The reason is can be found in the next section [TODO ref No Duplicate representation].


#### No Duplicate representation [Early Notes]

- we want a unique Isabelle representation for each Boogie map
- why? otherwise equality might not behave as we would expect
- currently two problems

- problem 1: a high-level map could model a low-level map
- solution 1: wf_ty, might be implied by type safety [TODO ref] but easier to explicitly list

- problem 2: the function representation might differ outside the relevant domain
- solution 2: force default value in these cases

- why does the default value need to be of the correct value?
- wf may not recurse in a negative position [TODO citation needed? or just explain?]
- so it is hard to cleanly case distinct on `wf k`,
    which is why it is easier to enforce both conditions in the fuzzy zone
- [TODO picture of table showing the fuzzy border]


#### Closed [Early Notes]

- if we have constrained type, and use operations like select/store, the result should be constrained again, i.e. fulfill the invariant
- so we need the select to be closed
- not true in general, as the result might be a bad map, [TODO example?]
- desired property: `(∀k. wf k --> wf (selectImpl m k))`
- not possible, as `wf k` appears in negative position
- could make strong by replacing with `wf_ty k`
- or just `(∀k. wf (selectImpl m k))`, enforcing that the result is always wf, not matter if the key is or not
- the closedness of store is a derived property now


#### Well Formed Definition [Early Notes]
[TODO this before select/store, with an assumed select, as this design decision affects select/store]

```haskell
inductive wf where
    wfLitV: "wf (LitV v)" | wfAbsV: "wf (AbsV v)" |
    wfMapV: "⟦ wf_ty m;  (∀k. wf (selectImpl m k));
      (∀k. (¬wf k ∨ type_of_val k ≠ key_ty (type_of_val m)) ⟶ (selectImpl m k) = val_of_type (val_ty (type_of_val m)));
      (∀k. type_of_val (selectImpl m k) = val_ty (type_of_val m))
      ⟧ ⟹ wf m"
```


#### Conversion from and to internal datatype
[TODO should this just be in the appendix?]

For our map semantics we introduced these different levels. [TODO ref Solution]
These only matter here, so we want to hide this implementation detail from the rest of the semantics.
That is why we made the val datatype so generic [TODO ref datatype ('a, 'm) val].

Therefore, we need a way to translate the instantiated version of the generic val datatype,
into our level representation:

[TODO potentially simplify sum semantics, i.e. Inr (Inl x) -> In2 x]
```haskell
fun toVal3210 :: "'a valn ⇒ 'a val3210" where
    "toVal3210 (LitV v) = (Inr (Inr (Inr (LitV0 v))))"
  | "toVal3210 (AbsV v) = (Inr (Inr (Inr (AbsV0 v))))"
  | "toVal3210 (MapV (Inr (Inr m))) = (Inr (Inr (Inl m)))"
  | "toVal3210 (MapV (Inr (Inl m))) = (Inr (Inl m))"
  | "toVal3210 (MapV (Inl m)) = (Inl m)"

fun val3ToValn :: "'a val3210 ⇒ 'a valn" where
    "val3ToValn (Inr (Inr (Inr (LitV0 v)))) = (LitV v)"
  | "val3ToValn (Inr (Inr (Inr (AbsV0 v)))) = (AbsV v)"
  | "val3ToValn (Inr (Inr (Inl m))) = (MapV (Inr (Inr m)))"
  | "val3ToValn (Inr (Inl m)) = (MapV (Inr (Inl m)))"
  | "val3ToValn (Inl m) = (MapV (Inl m))"
```


#### Select [Early Notes]

Now we can define a select function for our current map semantics.

First, we define an auxiliary function, that performs the operation on our internal representation:

[TODO potentially simplify semantics: remove primitive cases, move default case to non-aux function to avoid conversions]
```haskell
fun selectImplAux :: "'a::absval val3210 ⇒ 'a val3210 ⇒ 'a val3210" where
    "selectImplAux (Inr (Inr (Inr (LitV0 v)))) _ = (Inr (Inr (Inr undefined)))"
  | "selectImplAux (Inr (Inr (Inr (AbsV0 v)))) _ = (Inr (Inr (Inr undefined)))"
  | "selectImplAux (Inr (Inr (Inl (FunL m _ _)))) (Inr (Inr (Inr k))) = Inr (Inr (m k))"
  | "selectImplAux (Inr (Inl (FunL m _ _))) (Inr (Inr k)) = Inr (m k)"
  | "selectImplAux (Inl (FunL m _ _)) (Inr k) = (m k)"
  | "selectImplAux m _ = toVal3210 (val_of_type (val_ty (type_of_val (val3ToValn m))))"
```

`absval` is a type class, that is needed to call `type_of_val`.
This is addressed later in the section [TODO ref other changes].

Let's focus on `"selectImplAux (Inr (Inl (FunL m _ _))) (Inr (Inr k)) = Inr (m k)"`
...

Primitive [TODO ref wf]

default [TODO ref wf]



#### Store

#### Well Formed


#### Showing one wf map?
Appendix?

#### Proving Axioms
Proofs in Appendix?

#### Typedef and lifting

#### Final Lemmas (for VC phases and so on)


### Alternative Approaches

### Adjusting Proofgen Module


### Evaluation

## Future Work

## Conclusion/Summary


## Bibliography
## List of figures/tables
## Agreements

## Appendix
