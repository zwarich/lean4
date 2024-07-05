/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.HashMap.Basic

/-!
# Hash sets

This file develops the type `Std.Data.HashSet` of dependent hash sets.

The operations `map` and `filterMap` on `Std.Data.HashSet` are defined in the module
`Std.Data.HashSet.AdditionalOperations`.

Lemmas about the operations on `Std.Data.HashSet` are available in the
module `Std.Data.HashSet.Lemmas`.

See the module `Std.Data.HashSet.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u}

namespace Std

/--
Hash sets.

This is a simple separate-chaining hash table. The data of the hash map consists of a cached size
and an array of buckets, where each bucket is a linked list of keys. The number of buckets
is always a power of two. The hash map doubles its size upon inserting an element such that the
number of elements is more than 75% of the number of buckets.

These hash sets contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.Data.HashSet.Raw` and
`Std.Data.HashSet.Raw.WF` unbundle the invariant from the hash map. When in doubt, prefer
`HashSet` over `HashSet.Raw`.
-/
structure HashSet (α : Type u) [BEq α] [Hashable α] where
  /-- Internal implementation detail of the hash set. -/
  inner : HashMap α Unit

namespace HashSet

/--
Creates a new empty hash set. The optional parameter `capacity` can be supplied to presize the
map so that it can hold the given number of elements without reallocating. It is also possible to
use the empty collection notations `∅` and `{}` to create an empty hash map with the default
capacity.
-/
@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : HashSet α :=
  ⟨HashMap.empty capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashSet α) where
  emptyCollection := empty

/-- Inserts the given element into the set. -/
@[inline] def insert [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α :=
  ⟨m.inner.insertIfNew a ()⟩

/--
Checks whether an element is present in a set and inserts the element if it was not found.

Equivalent to (but potentially faster than) calling `contains` followed by `insertIfNew`.
-/
@[inline] def containsThenInsert [BEq α] [Hashable α] (m : HashSet α) (a : α) : Bool × HashSet α :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsertIfNew a ()
  ⟨replaced, ⟨r⟩⟩

/--
Returns `true` if the given key is present in the set. There is also a `Prop`-valued version of
this: `a ∈ m` is equivalent to `m.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` use
`==` for comparisons, while for hash sets, both use `==`.
-/
@[inline] def contains [BEq α] [Hashable α] (m : HashSet α) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (HashSet α) where
  mem a m := a ∈ m.inner

instance [BEq α] [Hashable α] {m : HashSet α} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.inner))

/-- Removes the element if it exists. -/
@[inline] def remove [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α :=
  ⟨m.inner.remove a⟩

/-- The number of elements present in the set -/
@[inline] def size [BEq α] [Hashable α] (m : HashSet α) : Nat :=
  m.inner.size

/--
Returns `true` if the hash set contains no elements.

Note that if your `BEq` instance is not reflexive or your `Hashable` instance is not
lawful, then it is possible that this function returns `false` even though `m.contains a = false`
for all `a`.
-/
@[inline] def isEmpty [BEq α] [Hashable α] (m : HashSet α) : Bool :=
  m.inner.isEmpty

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

/-- Removes all elements from the hash map for which the given function returns `false`. -/
@[inline] def filter [BEq α] [Hashable α] (f : α → Bool) (m : HashSet α) : HashSet α :=
  ⟨m.inner.filter fun a _ => f a⟩

/-- Folds the given function over the elements of the hash set in some order. -/
@[inline] def foldM [BEq α] [Hashable α] {m : Type v → Type v} [Monad m] {β : Type v}
    (f : β → α → m β) (init : β) (b : HashSet α) : m β :=
  b.inner.foldM (fun b a _ => f b a) init

/-- Folds the given function over the elements of the hash set in some order. -/
@[inline] def fold [BEq α] [Hashable α] {β : Type v} (f : β → α → β) (init : β) (m : HashSet α) :
    β :=
  m.inner.fold (fun b a _ => f b a) init

/-- Carries out a monadic action on each mapping in the hash map in some order. -/
@[inline] def forM [BEq α] [Hashable α] {m : Type v → Type v} [Monad m] (f : α → m PUnit)
    (b : HashSet α) : m PUnit :=
  b.inner.forM (fun a _ => f a)

/-- Support for the `for` loop construct in `do` blocks. -/
@[inline] def forIn [BEq α] [Hashable α] {m : Type v → Type v} [Monad m] {β : Type v}
    (f : α → β → m (ForInStep β)) (init : β) (b : HashSet α) : m β :=
  b.inner.forIn (fun a _ acc => f a acc) init

instance [BEq α] [Hashable α] {m : Type v → Type v} : ForM m (HashSet α) α where
  forM m f := m.forM f

instance [BEq α] [Hashable α] {m : Type v → Type v} : ForIn m (HashSet α) α where
  forIn m init f := m.forIn f init

/-- Transforms the hash set into a list of elements in some order. -/
@[inline] def toList [BEq α] [Hashable α] (m : HashSet α) : List α :=
  m.inner.keys

/-- Transforms the hash set into an array of elements in some order. -/
@[inline] def toArray [BEq α] [Hashable α] (m : HashSet α) : Array α :=
  m.inner.keysArray

/--
Inserts multiple elements into the hash set by iterating over the given collection and calling
`insert`.
-/
@[inline] def insertMany [BEq α] [Hashable α] {ρ : Type v} [ForIn Id ρ α] (m : HashSet α) (l : ρ) :
    HashSet α :=
  ⟨m.inner.insertManyUnit l⟩

/-- Creates a hash set from a list of elements. -/
@[inline] def ofList [BEq α] [Hashable α] {ρ : Type v} [ForIn Id ρ α] (l : ρ) : HashSet α :=
  ⟨HashMap.unitOfList l⟩

/--
Returns the number of buckets in the internal representation of the hash set. This function may
be useful for things like monitoring system health, but it should be considered an internal
implementation detail.
-/
def Internal.numBuckets [BEq α] [Hashable α] (m : HashSet α) : Nat :=
  HashMap.Internal.numBuckets m.inner

instance [BEq α] [Hashable α] [Repr α] : Repr (HashSet α) where
  reprPrec m prec := Repr.addAppParen ("Std.HashSet.ofList " ++ reprArg m.toList) prec

end Unverified

end HashSet

end Std
