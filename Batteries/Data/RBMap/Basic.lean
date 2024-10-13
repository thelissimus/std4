/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Batteries.Classes.Order
import Batteries.Control.ForInStep.Basic
import Batteries.Tactic.Lint.Misc
import Batteries.Tactic.Alias

/-!
# Red-black trees

This module implements a type `RBMap α β cmp` which is a functional data structure for
storing a key-value store in a binary search tree.

It is built on the simpler `RBSet α cmp` type, which stores a set of values of type `α`
using the function `cmp : α → α → Ordering` for determining the ordering relation.
The tree will never store two elements that compare `.eq` under the `cmp` function,
but the function does not have to satisfy `cmp x y = .eq → x = y`, and in the map case
`α` is a key-value pair and the `cmp` function only compares the keys.
-/

namespace Batteries

/--
In a red-black tree, every node has a color which is either "red" or "black"
(this particular choice of colors is conventional). A nil node is considered black.
-/
inductive RBColor where
  /-- A red node is required to have black children. -/
  | red
  /-- Every path from the root to a leaf must pass through the same number of black nodes. -/
  | black
  deriving Repr

/--
A red-black tree. (This is an internal implementation detail of the `RBSet` type,
which includes the invariants of the tree.) This is a binary search tree augmented with
a "color" field which is either red or black for each node and used to implement
the re-balancing operations.
See: [Red–black tree](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree)
-/
inductive RBNode (α : Type u) where
  /-- An empty tree. -/
  | nil
  /-- A node consists of a value `v`, a subtree `l` of smaller items,
  and a subtree `r` of larger items. The color `c` is either `red` or `black`
  and participates in the red-black balance invariant (see `Balanced`). -/
  | node (c : RBColor) (l : RBNode α) (v : α) (r : RBNode α)
  deriving Repr

namespace RBNode
open RBColor

instance : EmptyCollection (RBNode α) := ⟨nil⟩

/-- The minimum element of a tree is the left-most value. -/
protected def min? : RBNode α → Option α
  | nil            => none
  | node _ nil v _ => some v
  | node _ l _ _   => l.min?

/-- The maximum element of a tree is the right-most value. -/
protected def max? : RBNode α → Option α
  | nil            => none
  | node _ _ v nil => some v
  | node _ _ _ r   => r.max?

@[deprecated (since := "2024-04-17")] protected alias min := RBNode.min?
@[deprecated (since := "2024-04-17")] protected alias max := RBNode.max?

/--
Fold a function in tree order along the nodes. `v₀` is used at `nil` nodes and
`f` is used to combine results at branching nodes.
-/
@[specialize] def fold (v₀ : σ) (f : σ → α → σ → σ) : RBNode α → σ
  | nil          => v₀
  | node _ l v r => f (l.fold v₀ f) v (r.fold v₀ f)

/-- Fold a function on the values from left to right (in increasing order). -/
@[specialize] def foldl (f : σ → α → σ) : (init : σ) → RBNode α → σ
  | b, nil          => b
  | b, node _ l v r => foldl f (f (foldl f b l) v) r

/-- Fold a function on the values from right to left (in decreasing order). -/
@[specialize] def foldr (f : α → σ → σ) : RBNode α → (init : σ) → σ
  | nil,          b => b
  | node _ l v r, b => l.foldr f <| f v <| r.foldr f b

/-- `O(n)`. Convert the tree to a list in ascending order. -/
def toList (t : RBNode α) : List α := t.foldr (·::·) []

/-- Run monadic function `f` on each element of the tree (in increasing order). -/
@[specialize] def forM [Monad m] (f : α → m PUnit) : RBNode α → m PUnit
  | nil          => pure ⟨⟩
  | node _ l v r => do forM f l; f v; forM f r

/-- Fold a monadic function on the values from left to right (in increasing order). -/
@[specialize] def foldlM [Monad m] (f : σ → α → m σ) : (init : σ) → RBNode α → m σ
  | b, nil          => pure b
  | b, node _ l v r => do foldlM f (← f (← foldlM f b l) v) r

/-- Implementation of `for x in t` loops over a `RBNode` (in increasing order). -/
@[inline] protected def forIn [Monad m]
    (as : RBNode α) (init : σ) (f : α → σ → m (ForInStep σ)) : m σ := do
  ForInStep.run <$> visit as init
where
  /-- Inner loop of `forIn`. -/
  @[specialize] visit : RBNode α → σ → m (ForInStep σ)
    | nil,          b => return ForInStep.yield b
    | node _ l v r, b => ForInStep.bindM (visit l b) fun b => ForInStep.bindM (f v b) (visit r ·)

instance : ForIn m (RBNode α) α where
  forIn := RBNode.forIn

/--
An auxiliary data structure (an iterator) over an `RBNode` which lazily
pulls elements from the left.
-/
protected inductive Stream (α : Type _)
  /-- The stream is empty. -/
  | nil
  /-- We are ready to deliver element `v` with right child `r`,
  and where `tail` represents all the subtrees we have yet to destructure. -/
  | cons (v : α) (r : RBNode α) (tail : RBNode.Stream α)

/-- `O(log n)`. Turn a node into a stream, by descending along the left spine. -/
def toStream : RBNode α → (_ : RBNode.Stream α := .nil) → RBNode.Stream α
  | nil, acc => acc
  | node _ l v r, acc => toStream l (.cons v r acc)

namespace Stream

/-- `O(1)` amortized, `O(log n)` worst case: Get the next element from the stream. -/
def next? : RBNode.Stream α → Option (α × RBNode.Stream α)
  | nil => none
  | cons v r tail => some (v, toStream r tail)

/-- Fold a function on the values from left to right (in increasing order). -/
@[specialize] def foldl (f : σ → α → σ) : (init : σ) → RBNode.Stream α → σ
  | b, nil           => b
  | b, cons v r tail => foldl f (r.foldl f (f b v)) tail

/-- Fold a function on the values from right to left (in decreasing order). -/
@[specialize] def foldr (f : α → σ → σ) : RBNode.Stream α → (init : σ) → σ
  | nil,           b => b
  | cons v r tail, b => f v <| r.foldr f <| tail.foldr f b

/-- `O(n)`. Convert the stream to a list in ascending order. -/
def toList (t : RBNode.Stream α) : List α := t.foldr (·::·) []

end Stream

instance : ToStream (RBNode α) (RBNode.Stream α) := ⟨(·.toStream)⟩
instance : Stream (RBNode.Stream α) α := ⟨Stream.next?⟩

/-- Returns `true` iff every element of the tree satisfies `p`. -/
@[specialize] def all (p : α → Bool) : RBNode α → Bool
  | nil          => true
  | node _ l v r => p v && all p l && all p r

/-- Returns `true` iff any element of the tree satisfies `p`. -/
@[specialize] def any (p : α → Bool) : RBNode α → Bool
  | nil          => false
  | node _ l v r => p v || any p l || any p r

/-- Asserts that `p` holds on every element of the tree. -/
def All (p : α → Prop) : RBNode α → Prop
  | nil          => True
  | node _ l v r => p v ∧ All p l ∧ All p r

theorem All.imp (H : ∀ {x : α}, p x → q x) : ∀ {t : RBNode α}, t.All p → t.All q
  | nil => id
  | node .. => fun ⟨h, hl, hr⟩ => ⟨H h, hl.imp H, hr.imp H⟩

theorem all_iff {t : RBNode α} : t.all p ↔ t.All (p ·) := by
  induction t <;> simp [*, all, All, and_assoc]

instance {t : RBNode α} [DecidablePred p] : Decidable (t.All p) :=
  decidable_of_iff (t.all p) (by simp [all_iff])

/-- Asserts that `p` holds on some element of the tree. -/
def Any (p : α → Prop) : RBNode α → Prop
  | nil          => False
  | node _ l v r => p v ∨ Any p l ∨ Any p r

theorem any_iff {t : RBNode α} : t.any p ↔ t.Any (p ·) := by
  induction t <;> simp [*, any, Any, or_assoc]

instance {t : RBNode α} [DecidablePred p] : Decidable (t.Any p) :=
  decidable_of_iff (t.any p) (by simp [any_iff])

/-- True if `x` is an element of `t` "exactly", i.e. up to equality, not the `cmp` relation. -/
def EMem (x : α) (t : RBNode α) : Prop := t.Any (x = ·)

instance : Membership α (RBNode α) where
  mem t x := EMem x t

/-- True if the specified `cut` matches at least one element of of `t`. -/
def MemP (cut : α → Ordering) (t : RBNode α) : Prop := t.Any (cut · = .eq)

/-- True if `x` is equivalent to an element of `t`. -/
@[reducible] def Mem (cmp : α → α → Ordering) (x : α) (t : RBNode α) : Prop := MemP (cmp x) t

-- These instances are put in a special namespace because they are usually not what users want
-- when deciding membership in a RBSet, since this does a naive linear search through the tree.
-- The real `O(log n)` instances are defined in `Data.RBMap.Lemmas`.
@[nolint docBlame] scoped instance Slow.instDecidableEMem [DecidableEq α] {t : RBNode α} :
    Decidable (EMem x t) := inferInstanceAs (Decidable (Any ..))

@[nolint docBlame] scoped instance Slow.instDecidableMemP {t : RBNode α} :
    Decidable (MemP cut t) := inferInstanceAs (Decidable (Any ..))

@[nolint docBlame] scoped instance Slow.instDecidableMem {t : RBNode α} :
    Decidable (Mem cmp x t) := inferInstanceAs (Decidable (Any ..))

/--
Asserts that `t₁` and `t₂` have the same number of elements in the same order,
and `R` holds pairwise between them. The tree structure is ignored.
-/
@[specialize] def all₂ (R : α → β → Bool) (t₁ : RBNode α) (t₂ : RBNode β) : Bool :=
  let result := StateT.run (s := t₂.toStream) <| t₁.forM fun a s => do
    let (b, s) ← s.next?
    bif R a b then pure (⟨⟩, s) else none
  result matches some (_, .nil)

instance [BEq α] : BEq (RBNode α) where
  beq a b := a.all₂ (· == ·) b

/--
We say that `x < y` under the comparator `cmp` if `cmp x y = .lt`.

* In order to avoid assuming the comparator is always lawful, we use a
  local `∀ [TransCmp cmp]` binder in the relation so that the ordering
  properties of the tree only need to hold if the comparator is lawful.
* The `Nonempty` wrapper is a no-op because this is already a proposition,
  but it prevents the `[TransCmp cmp]` binder from being introduced when we don't want it.
-/
def cmpLT (cmp : α → α → Ordering) (x y : α) : Prop := Nonempty (∀ [TransCmp cmp], cmp x y = .lt)

theorem cmpLT_iff [TransCmp cmp] : cmpLT cmp x y ↔ cmp x y = .lt := ⟨fun ⟨h⟩ => h, (⟨·⟩)⟩

instance (cmp) [TransCmp cmp] : Decidable (cmpLT cmp x y) := decidable_of_iff' _ cmpLT_iff

/-- We say that `x ≈ y` under the comparator `cmp` if `cmp x y = .eq`. See also `cmpLT`. -/
def cmpEq (cmp : α → α → Ordering) (x y : α) : Prop := Nonempty (∀ [TransCmp cmp], cmp x y = .eq)

theorem cmpEq_iff [TransCmp cmp] : cmpEq cmp x y ↔ cmp x y = .eq := ⟨fun ⟨h⟩ => h, (⟨·⟩)⟩

instance (cmp) [TransCmp cmp] : Decidable (cmpEq cmp x y) := decidable_of_iff' _ cmpEq_iff

/-- `O(n)`. Verifies an ordering relation on the nodes of the tree. -/
def isOrdered (cmp : α → α → Ordering)
    (t : RBNode α) (l : Option α := none) (r : Option α := none) : Bool :=
  match t with
  | nil =>
    match l, r with
    | some l, some r => cmp l r = .lt
    | _, _ => true
  | node _ a v b => isOrdered cmp a l v && isOrdered cmp b v r

/-- The first half of Okasaki's `balance`, concerning red-red sequences in the left child. -/
@[inline] def balance1 : RBNode α → α → RBNode α → RBNode α
  | node red (node red a x b) y c, z, d
  | node red a x (node red b y c), z, d => node red (node black a x b) y (node black c z d)
  | a,                             x, b => node black a x b

/-- The second half of Okasaki's `balance`, concerning red-red sequences in the right child. -/
@[inline] def balance2 : RBNode α → α → RBNode α → RBNode α
  | a, x, node red b y (node red c z d)
  | a, x, node red (node red b y c) z d => node red (node black a x b) y (node black c z d)
  | a, x, b                             => node black a x b

/-- Returns `red` if the node is red, otherwise `black`. (Nil nodes are treated as `black`.) -/
@[inline] def isRed : RBNode α → RBColor
  | node c .. => c
  | _         => black

/--
Returns `black` if the node is black, otherwise `red`.
(Nil nodes are treated as `red`, which is not the usual convention but useful for deletion.)
-/
@[inline] def isBlack : RBNode α → RBColor
  | node c .. => c
  | _         => red

/-- Changes the color of the root to `black`. -/
def setBlack : RBNode α → RBNode α
  | nil          => nil
  | node _ l v r => node black l v r

/-- `O(n)`. Reverses the ordering of the tree without any rebalancing. -/
@[simp] def reverse : RBNode α → RBNode α
  | nil          => nil
  | node c l v r => node c r.reverse v l.reverse

section Insert

/--
The core of the `insert` function. This adds an element `x` to a balanced red-black tree.
Importantly, the result of calling `ins` is not a proper red-black tree,
because it has a broken balance invariant.
(See `Balanced.ins` for the balance invariant of `ins`.)
The `insert` function does the final fixup needed to restore the invariant.
-/
@[specialize] def ins (cmp : α → α → Ordering) (x : α) : RBNode α → RBNode α
  | nil => node red nil x nil
  | node red a y b =>
    match cmp x y with
    | Ordering.lt => node red (ins cmp x a) y b
    | Ordering.gt => node red a y (ins cmp x b)
    | Ordering.eq => node red a x b
  | node black a y b =>
    match cmp x y with
    | Ordering.lt => balance1 (ins cmp x a) y b
    | Ordering.gt => balance2 a y (ins cmp x b)
    | Ordering.eq => node black a x b

/--
`insert cmp t v` inserts element `v` into the tree, using the provided comparator
`cmp` to put it in the right place and automatically rebalancing the tree as necessary.
-/
@[specialize] def insert (cmp : α → α → Ordering) (t : RBNode α) (v : α) : RBNode α :=
  match isRed t with
  | red => (ins cmp v t).setBlack
  | black => ins cmp v t

end Insert

/-- Recolor the root of the tree to `red` if possible. -/
def setRed : RBNode α → RBNode α
  | node _ a v b => node red a v b
  | nil          => nil

/-- Rebalancing a tree which has shrunk on the left. -/
def balLeft (l : RBNode α) (v : α) (r : RBNode α) : RBNode α :=
  match l with
  | node red a x b                    => node red (node black a x b) v r
  | l => match r with
    | node black a y b                => balance2 l v (node red a y b)
    | node red (node black a y b) z c => node red (node black l v a) y (balance2 b z (setRed c))
    | r                               => node red l v r -- unreachable

/-- Rebalancing a tree which has shrunk on the right. -/
def balRight (l : RBNode α) (v : α) (r : RBNode α) : RBNode α :=
  match r with
  | node red b y c                    => node red l v (node black b y c)
  | r => match l with
    | node black a x b                => balance1 (node red a x b) v r
    | node red a x (node black b y c) => node red (balance1 (setRed a) x b) y (node black c v r)
    | l                               => node red l v r -- unreachable

/-- The number of nodes in the tree. -/
@[simp] def size : RBNode α → Nat
  | nil => 0
  | node _ x _ y => x.size + y.size + 1

/-- Concatenate two trees with the same black-height. -/
def append : RBNode α → RBNode α → RBNode α
  | nil, x | x, nil => x
  | node red a x b, node red c y d =>
    match append b c with
    | node red b' z c' => node red (node red a x b') z (node red c' y d)
    | bc               => node red a x (node red bc y d)
  | node black a x b, node black c y d =>
    match append b c with
    | node red b' z c' => node red (node black a x b') z (node black c' y d)
    | bc               => balLeft a x (node black bc y d)
  | a@(node black ..), node red b x c => node red (append a b) x c
  | node red a x b, c@(node black ..) => node red a x (append b c)
termination_by x y => x.size + y.size

/-! ## erase -/

/--
The core of the `erase` function. The tree returned from this function has a broken invariant,
which is restored in `erase`.
-/
@[specialize] def del (cut : α → Ordering) : RBNode α → RBNode α
  | nil          => nil
  | node _ a y b =>
    match cut y with
    | .lt => match a.isBlack with
      | black => balLeft (del cut a) y b
      | red => node red (del cut a) y b
    | .gt => match b.isBlack with
      | black => balRight a y (del cut b)
      | red => node red a y (del cut b)
    | .eq => append a b

/--
The `erase cut t` function removes an element from the tree `t`.
The `cut` function is used to locate an element in the tree:
it returns `.gt` if we go too high and `.lt` if we go too low;
if it returns `.eq` we will remove the element.
(The function `cmp k` for some key `k` is a valid cut function, but we can also use cuts that
are not of this form as long as they are suitably monotonic.)
-/
@[specialize] def erase (cut : α → Ordering) (t : RBNode α) : RBNode α := (del cut t).setBlack

/-- Finds an element in the tree satisfying the `cut` function. -/
@[specialize] def find? (cut : α → Ordering) : RBNode α → Option α
  | nil => none
  | node _ a y b =>
    match cut y with
    | .lt => find? cut a
    | .gt => find? cut b
    | .eq => some y

/-- `upperBound? cut` retrieves the smallest entry larger than or equal to `cut`, if it exists. -/
@[specialize] def upperBound? (cut : α → Ordering) : RBNode α → (ub : Option α := .none) → Option α
  | nil,          ub => ub
  | node _ a y b, ub =>
    match cut y with
    | .lt => upperBound? cut a (some y)
    | .gt => upperBound? cut b ub
    | .eq => some y

/-- `lowerBound? cut` retrieves the largest entry smaller than or equal to `cut`, if it exists. -/
@[specialize] def lowerBound? (cut : α → Ordering) : RBNode α → (lb : Option α := .none) → Option α
  | nil,          lb => lb
  | node _ a y b, lb =>
    match cut y with
    | .lt => lowerBound? cut a lb
    | .gt => lowerBound? cut b (some y)
    | .eq => some y

/-- Returns the root of the tree, if any. -/
def root? : RBNode α → Option α
  | nil => none
  | node _ _ v _ => some v

/--
`O(n)`. Map a function on every value in the tree.
This requires `IsMonotone` on the function in order to preserve the order invariant.
-/
@[specialize] def map (f : α → β) : RBNode α → RBNode β
  | nil => nil
  | node c l v r => node c (l.map f) (f v) (r.map f)

/-- Converts the tree into an array in increasing sorted order. -/
def toArray (n : RBNode α) : Array α := n.foldl (init := #[]) (·.push ·)

/--
A `RBNode.Path α` is a "cursor" into an `RBNode` which represents the path
from the root to a subtree. Note that the path goes from the target subtree
up to the root, which is reversed from the normal way data is stored in the tree.
See [Zipper](https://en.wikipedia.org/wiki/Zipper_(data_structure)) for more information.
-/
inductive Path (α : Type u) where
  /-- The root of the tree, which is the end of the path of parents. -/
  | root
  /-- A path that goes down the left subtree. -/
  | left (c : RBColor) (parent : Path α) (v : α) (r : RBNode α)
  /-- A path that goes down the right subtree. -/
  | right (c : RBColor) (l : RBNode α) (v : α) (parent : Path α)

/-- Fills the `Path` with a subtree. -/
def Path.fill : Path α → RBNode α → RBNode α
  | .root, t => t
  | .left c parent y b, a
  | .right c a y parent, b => parent.fill (node c a y b)

/--
Like `find?`, but instead of just returning the element, it returns the entire subtree
at the element and a path back to the root for reconstructing the tree.
-/
@[specialize] def zoom (cut : α → Ordering) : RBNode α → (e : Path α := .root) → RBNode α × Path α
  | nil, path => (nil, path)
  | n@(node c a y b), path =>
    match cut y with
    | .lt => zoom cut a (.left c path y b)
    | .gt => zoom cut b (.right c a y path)
    | .eq => (n, path)

/--
This function does the second part of `RBNode.ins`,
which unwinds the stack and rebuilds the tree.
-/
def Path.ins : Path α → RBNode α → RBNode α
  | .root, t => t.setBlack
  | .left red parent y b, a
  | .right red a y parent, b => parent.ins (node red a y b)
  | .left black parent y b, a => parent.ins (balance1 a y b)
  | .right black a y parent, b => parent.ins (balance2 a y b)

/--
`path.insertNew v` inserts element `v` into the tree, assuming that `path` is zoomed in
on a `nil` node such that inserting a new element at this position is valid.
-/
@[inline] def Path.insertNew (path : Path α) (v : α) : RBNode α :=
  path.ins (node red nil v nil)

/--
`path.insert t v` inserts element `v` into the tree, assuming that `(t, path)` was the result of a
previous `zoom` operation (so either the root of `t` is equivalent to `v` or it is empty).
-/
def Path.insert (path : Path α) (t : RBNode α) (v : α) : RBNode α :=
  match t with
  | nil => path.insertNew v
  | node c a _ b => path.fill (node c a v b)

/--
`path.del t c` does the second part of `RBNode.del`, which unwinds the stack
and rebuilds the tree. The `c` argument is the color of the node before the deletion
(we used `t₀.isBlack` for this in `RBNode.del` but the original tree is no longer
available in this formulation).
-/
def Path.del : Path α → RBNode α → RBColor → RBNode α
  | .root, t, _ => t.setBlack
  | .left c parent y b, a, red
  | .right c a y parent, b, red => parent.del (node red a y b) c
  | .left c parent y b, a, black => parent.del (balLeft a y b) c
  | .right c a y parent, b, black => parent.del (balRight a y b) c

/--
`path.erase t v` removes the root element of `t` from the tree, assuming that `(t, path)` was
the result of a previous `zoom` operation.
-/
def Path.erase (path : Path α) (t : RBNode α) : RBNode α :=
  match t with
  | nil => path.fill nil
  | node c a _ b => path.del (a.append b) c

/--
`modify cut f t` uses `cut` to find an element,
then modifies the element using `f` and reinserts it into the tree.

Because the tree structure is not modified,
`f` must not modify the ordering properties of the element.

The element in `t` is used linearly if `t` is unshared.
-/
@[specialize] def modify (cut : α → Ordering) (f : α → α) (t : RBNode α) : RBNode α :=
  match zoom cut t with
  | (nil, _) => t -- TODO: profile whether it would be better to use `path.fill nil` here
  | (node c a x b, path) => path.fill (node c a (f x) b)

/--
`alter cut f t` simultaneously handles inserting, erasing and replacing an element
using a function `f : Option α → Option α`. It is passed the result of `t.find? cut`
and can either return `none` to remove the element or `some a` to replace/insert
the element with `a` (which must have the same ordering properties as the original element).

The element is used linearly if `t` is unshared.
-/
@[specialize] def alter (cut : α → Ordering) (f : Option α → Option α) (t : RBNode α) : RBNode α :=
  match zoom cut t with
  | (nil, path) =>
    match f none with
    | none => t -- TODO: profile whether it would be better to use `path.fill nil` here
    | some y => path.insertNew y
  | (node c a x b, path) =>
    match f (some x) with
    | none => path.del (a.append b) c
    | some y => path.fill (node c a y b)

/--
The ordering invariant of a red-black tree, which is a binary search tree.
This says that every element of a left subtree is less than the root, and
every element in the right subtree is greater than the root, where the
less than relation `x < y` is understood to mean `cmp x y = .lt`.

Because we do not assume that `cmp` is lawful when stating this property,
we write it in such a way that if `cmp` is not lawful then the condition holds trivially.
That way we can prove the ordering invariants without assuming `cmp` is lawful.
-/
def Ordered (cmp : α → α → Ordering) : RBNode α → Prop
  | nil => True
  | node _ a x b => a.All (cmpLT cmp · x) ∧ b.All (cmpLT cmp x ·) ∧ a.Ordered cmp ∧ b.Ordered cmp

-- This is in the Slow namespace because it is `O(n^2)` where a `O(n)` algorithm exists
-- (see `isOrdered_iff` in `Data.RBMap.Lemmas`). Prefer `isOrdered` or the other instance.
@[nolint docBlame] scoped instance Slow.instDecidableOrdered (cmp) [TransCmp cmp] :
    ∀ t : RBNode α, Decidable (Ordered cmp t)
  | nil => inferInstanceAs (Decidable True)
  | node _ a _ b =>
    haveI := instDecidableOrdered cmp a
    haveI := instDecidableOrdered cmp b
    inferInstanceAs (Decidable (And ..))

/--
The red-black balance invariant. `Balanced t c n` says that the color of the root node is `c`,
and the black-height (the number of black nodes on any path from the root) of the tree is `n`.
Additionally, every red node must have black children.
-/
inductive Balanced : RBNode α → RBColor → Nat → Prop where
  /-- A nil node is balanced with black-height 0, and it is considered black. -/
  | protected nil : Balanced nil black 0
  /-- A red node is balanced with black-height `n`
  if its children are both black with with black-height `n`. -/
  | protected red : Balanced x black n → Balanced y black n → Balanced (node red x v y) red n
  /-- A black node is balanced with black-height `n + 1`
  if its children both have black-height `n`. -/
  | protected black : Balanced x c₁ n → Balanced y c₂ n → Balanced (node black x v y) black (n + 1)

/--
The well-formedness invariant for a red-black tree. The first constructor is the real invariant,
and the others allow us to "cheat" in this file and define `insert` and `erase`,
which have more complex proofs that are delayed to `Batteries.Data.RBMap.Lemmas`.
-/
inductive WF [Ord α] : RBNode α → Prop
  /-- The actual well-formedness invariant: a red-black tree has the
  ordering and balance invariants. -/
  | mk : t.Ordered compare → t.Balanced c n → WF t
  /-- Inserting into a well-formed tree yields another well-formed tree.
  (See `Ordered.insert` and `Balanced.insert` for the actual proofs.) -/
  | insert : WF t → WF (t.insert compare a)
  /-- Erasing from a well-formed tree yields another well-formed tree.
  (See `Ordered.erase` and `Balanced.erase` for the actual proofs.) -/
  | erase : WF t → WF (t.erase cut)

end RBNode

open RBNode

/--
An `RBSet` is a self-balancing binary search tree.
The `cmp` function is the comparator that will be used for performing searches;
it should satisfy the requirements of `TransCmp` for it to have sensible behavior.
-/
def RBSet (α : Type u) [Ord α] : Type u := {t : RBNode α // t.WF}

/-- `O(1)`. Construct a new empty tree. -/
@[inline] def mkRBSet (α : Type u) [Ord α] : RBSet α := ⟨.nil, .mk ⟨⟩ .nil⟩

namespace RBSet

/-- `O(1)`. Construct a new empty tree. -/
@[inline] def empty [Ord α] : RBSet α := mkRBSet ..

instance (α : Type u) [Ord α] : EmptyCollection (RBSet α) := ⟨empty⟩

instance (α : Type u) [Ord α] : Inhabited (RBSet α) := ⟨∅⟩

/-- `O(1)`. Construct a new tree with one element `v`. -/
@[inline] def single [Ord α] (v : α) : RBSet α :=
  ⟨.node .red .nil v .nil, .mk ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩ (.red .nil .nil)⟩

/-- `O(n)`. Fold a function on the values from left to right (in increasing order). -/
@[inline] def foldl [Ord α] (f : σ → α → σ) (init : σ) (t : RBSet α) : σ := t.1.foldl f init

/-- `O(n)`. Fold a function on the values from right to left (in decreasing order). -/
@[inline] def foldr [Ord α] (f : α → σ → σ) (init : σ) (t : RBSet α) : σ := t.1.foldr f init

/-- `O(n)`. Fold a monadic function on the values from left to right (in increasing order). -/
@[inline] def foldlM [Ord α] [Monad m] (f : σ → α → m σ) (init : σ) (t : RBSet α) : m σ :=
  t.1.foldlM f init

/-- `O(n)`. Run monadic function `f` on each element of the tree (in increasing order). -/
@[inline] def forM [Ord α] [Monad m] (f : α → m PUnit) (t : RBSet α) : m PUnit := t.1.forM f

instance [Ord α] : ForIn m (RBSet α) α where
  forIn t := t.1.forIn

instance [Ord α] : ToStream (RBSet α) (RBNode.Stream α) := ⟨fun x => x.1.toStream .nil⟩

/-- `O(1)`. Is the tree empty? -/
@[inline] def isEmpty [Ord α] : RBSet α → Bool
  | ⟨nil, _⟩ => true
  | _        => false

/-- `O(n)`. Convert the tree to a list in ascending order. -/
@[inline] def toList [Ord α] (t : RBSet α) : List α := t.1.toList

/-- `O(log n)`. Returns the entry `a` such that `a ≤ k` for all keys in the RBSet. -/
@[inline] protected def min? [Ord α] (t : RBSet α) : Option α := t.1.min?

/-- `O(log n)`. Returns the entry `a` such that `a ≥ k` for all keys in the RBSet. -/
@[inline] protected def max? [Ord α] (t : RBSet α) : Option α := t.1.max?

@[deprecated (since := "2024-04-17")] protected alias min := RBSet.min?
@[deprecated (since := "2024-04-17")] protected alias max := RBSet.max?

instance [Repr α] [Ord α] : Repr (RBSet α) where
  reprPrec m prec := Repr.addAppParen ("RBSet.ofList " ++ repr m.toList) prec

/-- `O(log n)`. Insert element `v` into the tree. -/
@[inline] def insert [Ord α] (t : RBSet α) (v : α) : RBSet α := ⟨t.1.insert compare v, t.2.insert⟩

/--
Insert all elements from a collection into a `RBSet α cmp`.
-/
def insertMany [Ord α] [ForIn Id ρ α] (s : RBSet α) (as : ρ) : RBSet α := Id.run do
  let mut s := s
  for a in as do
    s := s.insert a
  return s

/--
`O(log n)`. Remove an element from the tree using a cut function.
The `cut` function is used to locate an element in the tree:
it returns `.gt` if we go too high and `.lt` if we go too low;
if it returns `.eq` we will remove the element.
(The function `cmp k` for some key `k` is a valid cut function, but we can also use cuts that
are not of this form as long as they are suitably monotonic.)
-/
@[inline] def erase [Ord α] (t : RBSet α) (cut : α → Ordering) : RBSet α :=
  ⟨t.1.erase cut, t.2.erase⟩

/-- `O(log n)`. Find an element in the tree using a cut function. -/
@[inline] def findP? [Ord α] (t : RBSet α) (cut : α → Ordering) : Option α := t.1.find? cut

/-- `O(log n)`. Returns an element in the tree equivalent to `x` if one exists. -/
@[inline] def find? [Ord α] (t : RBSet α) (x : α) : Option α := t.1.find? (compare x)

/-- `O(log n)`. Find an element in the tree, or return a default value `v₀`. -/
@[inline] def findPD [Ord α] (t : RBSet α) (cut : α → Ordering) (v₀ : α) : α := (t.findP? cut).getD v₀

/--
`O(log n)`. `upperBoundP cut` retrieves the smallest entry comparing `gt` or `eq` under `cut`,
if it exists. If multiple keys in the map return `eq` under `cut`, any of them may be returned.
-/
@[inline] def upperBoundP? [Ord α] (t : RBSet α) (cut : α → Ordering) : Option α := t.1.upperBound? cut

/--
`O(log n)`. `upperBound? k` retrieves the largest entry smaller than or equal to `k`,
if it exists.
-/
@[inline] def upperBound? [Ord α] (t : RBSet α) (k : α) : Option α := t.upperBoundP? (compare k)

/--
`O(log n)`. `lowerBoundP cut` retrieves the largest entry comparing `lt` or `eq` under `cut`,
if it exists. If multiple keys in the map return `eq` under `cut`, any of them may be returned.
-/
@[inline] def lowerBoundP? [Ord α] (t : RBSet α) (cut : α → Ordering) : Option α := t.1.lowerBound? cut

/--
`O(log n)`. `lowerBound? k` retrieves the largest entry smaller than or equal to `k`,
if it exists.
-/
@[inline] def lowerBound? [Ord α] (t : RBSet α) (k : α) : Option α := t.lowerBoundP? (compare k)

/-- `O(log n)`. Returns true if the given cut returns `eq` for something in the RBSet. -/
@[inline] def containsP [Ord α] (t : RBSet α) (cut : α → Ordering) : Bool := (t.findP? cut).isSome

/-- `O(log n)`. Returns true if the given key `a` is in the RBSet. -/
@[inline] def contains [Ord α] (t : RBSet α) (a : α) : Bool := (t.find? a).isSome

/-- `O(n log n)`. Build a tree from an unsorted list by inserting them one at a time. -/
@[inline] def ofList [Ord α] (l : List α) : RBSet α :=
  l.foldl (fun r p => r.insert p) (mkRBSet α)

/-- `O(n log n)`. Build a tree from an unsorted array by inserting them one at a time. -/
@[inline] def ofArray [Ord α] (l : Array α) : RBSet α :=
  l.foldl (fun r p => r.insert p) (mkRBSet α)

/-- `O(n)`. Returns true if the given predicate is true for all items in the RBSet. -/
@[inline] def all [Ord α] (t : RBSet α) (p : α → Bool) : Bool := t.1.all p

/-- `O(n)`. Returns true if the given predicate is true for any item in the RBSet. -/
@[inline] def any [Ord α] (t : RBSet α) (p : α → Bool) : Bool := t.1.any p

/--
Asserts that `t₁` and `t₂` have the same number of elements in the same order,
and `R` holds pairwise between them. The tree structure is ignored.
-/
@[inline] def all₂ [Ord α] [Ord β] (R : α → β → Bool) (t₁ : RBSet α) (t₂ : RBSet β) : Bool :=
  t₁.1.all₂ R t₂.1

/-- True if `x` is an element of `t` "exactly", i.e. up to equality, not the `cmp` relation. -/
def EMem [Ord α] (x : α) (t : RBSet α) : Prop := t.1.EMem x

/-- True if the specified `cut` matches at least one element of of `t`. -/
def MemP [Ord α] (cut : α → Ordering) (t : RBSet α) : Prop := t.1.MemP cut

/-- True if `x` is equivalent to an element of `t`. -/
def Mem [Ord α] (x : α) (t : RBSet α) : Prop := MemP (compare x) t

instance [Ord α] : Membership α (RBSet α) where
  mem t x := Mem x t

-- These instances are put in a special namespace because they are usually not what users want
-- when deciding membership in a RBSet, since this does a naive linear search through the tree.
-- The real `O(log n)` instances are defined in `Data.RBMap.Lemmas`.
@[nolint docBlame] scoped instance Slow.instDecidableEMem [DecidableEq α] [Ord α] {t : RBSet α} :
    Decidable (EMem x t) := inferInstanceAs (Decidable (Any ..))

@[nolint docBlame] scoped instance Slow.instDecidableMemP [Ord α] {t : RBSet α} :
    Decidable (MemP cut t) := inferInstanceAs (Decidable (Any ..))

@[nolint docBlame] scoped instance Slow.instDecidableMem [Ord α] {t : RBSet α} :
    Decidable (Mem x t) := inferInstanceAs (Decidable (Any ..))

/--
Returns true if `t₁` and `t₂` are equal as sets (assuming `cmp` and `==` are compatible),
ignoring the internal tree structure.
-/
instance [BEq α] [Ord α] : BEq (RBSet α) where
  beq a b := a.all₂ (· == ·) b

/-- `O(n)`. The number of items in the RBSet. -/
def size [Ord α] (m : RBSet α) : Nat := m.1.size

/-- `O(log n)`. Returns the minimum element of the tree, or panics if the tree is empty. -/
@[inline] def min! [Inhabited α] [Ord α] (t : RBSet α) : α := t.min?.getD (panic! "tree is empty")

/-- `O(log n)`. Returns the maximum element of the tree, or panics if the tree is empty. -/
@[inline] def max! [Inhabited α] [Ord α] (t : RBSet α) : α := t.max?.getD (panic! "tree is empty")

/--
`O(log n)`. Attempts to find the value with key `k : α` in `t` and panics if there is no such key.
-/
@[inline] def findP! [Inhabited α] [Ord α] (t : RBSet α) (cut : α → Ordering) : α :=
  (t.findP? cut).getD (panic! "key is not in the tree")

/--
`O(log n)`. Attempts to find the value with key `k : α` in `t` and panics if there is no such key.
-/
@[inline] def find! [Inhabited α] [Ord α] (t : RBSet α) (k : α) : α :=
  (t.find? k).getD (panic! "key is not in the tree")

/-- The predicate asserting that the result of `modifyP` is safe to construct. -/
class ModifyWF [Ord α] (t : RBSet α) (cut : α → Ordering) (f : α → α) : Prop where
  /-- The resulting tree is well formed. -/
  wf : (t.1.modify cut f).WF

/--
`O(log n)`. In-place replace an element found by `cut`.
This takes the element out of the tree while `f` runs,
so it uses the element linearly if `t` is unshared.

The `ModifyWF` assumption is required because `f` may change
the ordering properties of the element, which would break the invariants.
-/
def modifyP [Ord α] (t : RBSet α) (cut : α → Ordering) (f : α → α)
    [wf : ModifyWF t cut f] : RBSet α := ⟨t.1.modify cut f, wf.wf⟩

/-- The predicate asserting that the result of `alterP` is safe to construct. -/
class AlterWF [Ord α] (t : RBSet α) (cut : α → Ordering) (f : Option α → Option α) : Prop where
  /-- The resulting tree is well formed. -/
  wf : (t.1.alter cut f).WF

/--
`O(log n)`. `alterP cut f t` simultaneously handles inserting, erasing and replacing an element
using a function `f : Option α → Option α`. It is passed the result of `t.findP? cut`
and can either return `none` to remove the element or `some a` to replace/insert
the element with `a` (which must have the same ordering properties as the original element).

The element is used linearly if `t` is unshared.

The `AlterWF` assumption is required because `f` may change
the ordering properties of the element, which would break the invariants.
-/
def alterP [Ord α] (t : RBSet α) (cut : α → Ordering) (f : Option α → Option α)
    [wf : AlterWF t cut f] : RBSet α := ⟨t.1.alter cut f, wf.wf⟩

/--
`O(n₂ * log (n₁ + n₂))`. Merges the maps `t₁` and `t₂`.
If equal keys exist in both, the key from `t₂` is preferred.
-/
def union [Ord α] (t₁ t₂ : RBSet α) : RBSet α :=
  t₂.foldl .insert t₁

instance [Ord α] : Union (RBSet α) := ⟨RBSet.union⟩

/--
`O(n₂ * log (n₁ + n₂))`. Merges the maps `t₁` and `t₂`. If equal keys exist in both,
then use `mergeFn a₁ a₂` to produce the new merged value.
-/
def mergeWith [Ord α] (mergeFn : α → α → α) (t₁ t₂ : RBSet α) : RBSet α :=
  t₂.foldl (init := t₁) fun t₁ a₂ =>
    t₁.insert <| match t₁.find? a₂ with | some a₁ => mergeFn a₁ a₂ | none => a₂

/--
`O(n₁ * log (n₁ + n₂))`. Intersects the maps `t₁` and `t₂`
using `mergeFn a b` to produce the new value.
-/
def intersectWith [Ord α] [Ord β] [Ord γ] (cmp : α → β → Ordering) (mergeFn : α → β → γ)
    (t₁ : RBSet α) (t₂ : RBSet β) : RBSet γ :=
  t₁.foldl (init := ∅) fun acc a =>
    match t₂.findP? (cmp a) with
    | some b => acc.insert <| mergeFn a b
    | none => acc

/-- `O(n * log n)`. Constructs the set of all elements satisfying `p`. -/
def filter [Ord α] (t : RBSet α) (p : α → Bool) : RBSet α :=
  t.foldl (init := ∅) fun acc a => bif p a then acc.insert a else acc

/--
`O(n * log n)`. Map a function on every value in the set.
If the function is monotone, consider using the more efficient `RBSet.mapMonotone` instead.
-/
def map [Ord α] [Ord β] (t : RBSet α) (f : α → β) : RBSet β :=
  t.foldl (init := ∅) fun acc a => acc.insert <| f a

/--
`O(n₁ * (log n₁ + log n₂))`. Constructs the set of all elements of `t₁` that are not in `t₂`.
-/
def sdiff [Ord α] (t₁ t₂ : RBSet α) : RBSet α := t₁.filter (!t₂.contains ·)

instance [Ord α] : SDiff (Batteries.RBSet α) := ⟨RBSet.sdiff⟩

end RBSet

/- TODO(Leo): define dRBMap -/

open scoped Ordering

/--
An `RBMap` is a self-balancing binary search tree, used to store a key-value map.
The `cmp` function is the comparator that will be used for performing searches;
it should satisfy the requirements of `TransCmp` for it to have sensible behavior.
-/
def RBMap (α : Type u) (β : Type v) [Ord α] : Type (max u v) := RBSet (α × β)

/-- `O(1)`. Construct a new empty map. -/
@[inline] def mkRBMap (α : Type u) (β : Type v) [Ord α] : RBMap α β :=
  mkRBSet ..

/-- `O(1)`. Construct a new empty map. -/
@[inline] def RBMap.empty {α : Type u} {β : Type v} [Ord α] : RBMap α β :=
  mkRBMap ..

instance (α : Type u) (β : Type v) [Ord α] : EmptyCollection (RBMap α β) :=
  ⟨RBMap.empty⟩

instance (α : Type u) (β : Type v) [Ord α] : Inhabited (RBMap α β) := ⟨∅⟩

/-- `O(1)`. Construct a new tree with one key-value pair `k, v`. -/
@[inline] def RBMap.single [Ord α] (k : α) (v : β) : RBMap α β :=
  RBSet.single (k, v)

namespace RBMap
variable {α : Type u} {β : Type v} {σ : Type w}

/-- `O(n)`. Fold a function on the values from left to right (in increasing order). -/
@[inline] def foldl [Ord α] (f : σ → α → β → σ) : (init : σ) → RBMap α β → σ
  | b, ⟨t, _⟩ => t.foldl (fun s (a, b) => f s a b) b

/-- `O(n)`. Fold a function on the values from right to left (in decreasing order). -/
@[inline] def foldr [Ord α] (f : α → β → σ → σ) : (init : σ) → RBMap α β → σ
  | b, ⟨t, _⟩ => t.foldr (fun (a, b) s => f a b s) b

/-- `O(n)`. Fold a monadic function on the values from left to right (in increasing order). -/
@[inline] def foldlM [Ord α] [Monad m] (f : σ → α → β → m σ) : (init : σ) → RBMap α β → m σ
  | b, ⟨t, _⟩ => t.foldlM (fun s (a, b) => f s a b) b

/-- `O(n)`. Run monadic function `f` on each element of the tree (in increasing order). -/
@[inline] def forM [Ord α] [Monad m] (f : α → β → m PUnit) (t : RBMap α β) : m PUnit :=
  t.1.forM (fun (a, b) => f a b)

instance [Ord α] : ForIn m (RBMap α β) (α × β) := inferInstanceAs (ForIn _ (RBSet ..) _)

instance [Ord α] : ToStream (RBMap α β) (RBNode.Stream (α × β)) :=
  inferInstanceAs (ToStream (RBSet ..) _)

/-- `O(n)`. Constructs the array of keys of the map. -/
@[inline] def keysArray [Ord α] (t : RBMap α β) : Array α :=
  t.1.foldl (init := #[]) (·.push ·.1)

/-- `O(n)`. Constructs the list of keys of the map. -/
@[inline] def keysList [Ord α] (t : RBMap α β) : List α :=
  t.1.foldr (init := []) (·.1 :: ·)

/--
An "iterator" over the keys of the map. This is a trivial wrapper over the underlying map,
but it comes with a small API to use it in a `for` loop or convert it to an array or list.
-/
def Keys (α β) [Ord α] := RBMap α β

/--
The keys of the map. This is an `O(1)` wrapper operation, which
can be used in `for` loops or converted to an array or list.
-/
@[inline] def keys [Ord α] (t : RBMap α β) : Keys α β := t

@[inline, inherit_doc keysArray] def Keys.toArray := @keysArray

@[inline, inherit_doc keysList] def Keys.toList := @keysList

instance [Ord α] : CoeHead (Keys α β) (Array α) := ⟨keysArray⟩

instance [Ord α] : CoeHead (Keys α β) (List α) := ⟨keysList⟩

instance [Ord α] : ForIn m (Keys α β) α where
  forIn t init f := t.val.forIn init (f ·.1)

instance [Ord α] : ForM m (Keys α β) α where
  forM t f := t.val.forM (f ·.1)

/-- The result of `toStream` on a `Keys`. -/
def Keys.Stream (α β) := RBNode.Stream (α × β)

/-- A stream over the iterator. -/
def Keys.toStream [Ord α] (t : Keys α β) : Keys.Stream α β := t.1.toStream

/-- `O(1)` amortized, `O(log n)` worst case: Get the next element from the stream. -/
def Keys.Stream.next? (t : Stream α β) : Option (α × Stream α β) :=
  match inline (RBNode.Stream.next? t) with
  | none => none
  | some ((a, _), t) => some (a, t)

instance [Ord α] : ToStream (Keys α β) (Keys.Stream α β) := ⟨Keys.toStream⟩
instance : Stream (Keys.Stream α β) α := ⟨Keys.Stream.next?⟩

/-- `O(n)`. Constructs the array of values of the map. -/
@[inline] def valuesArray [Ord α] (t : RBMap α β) : Array β :=
  t.1.foldl (init := #[]) (·.push ·.2)

/-- `O(n)`. Constructs the list of values of the map. -/
@[inline] def valuesList [Ord α] (t : RBMap α β) : List β :=
  t.1.foldr (init := []) (·.2 :: ·)

/--
An "iterator" over the values of the map. This is a trivial wrapper over the underlying map,
but it comes with a small API to use it in a `for` loop or convert it to an array or list.
-/
def Values (α β) [Ord α] := RBMap α β

/--
The "keys" of the map. This is an `O(1)` wrapper operation, which
can be used in `for` loops or converted to an array or list.
-/
@[inline] def values [Ord α] (t : RBMap α β) : Values α β := t

@[inline, inherit_doc valuesArray] def Values.toArray := @valuesArray

@[inline, inherit_doc valuesList] def Values.toList := @valuesList

instance [Ord α] : CoeHead (Values α β) (Array β) := ⟨valuesArray⟩

instance [Ord α] : CoeHead (Values α β) (List β) := ⟨valuesList⟩

instance [Ord α] : ForIn m (Values α β) β where
  forIn t init f := t.val.forIn init (f ·.2)

instance [Ord α] : ForM m (Values α β) β where
  forM t f := t.val.forM (f ·.2)

/-- The result of `toStream` on a `Values`. -/
def Values.Stream (α β) := RBNode.Stream (α × β)

/-- A stream over the iterator. -/
def Values.toStream [Ord α] (t : Values α β) : Values.Stream α β := t.1.toStream

/-- `O(1)` amortized, `O(log n)` worst case: Get the next element from the stream. -/
def Values.Stream.next? (t : Stream α β) : Option (β × Stream α β) :=
  match inline (RBNode.Stream.next? t) with
  | none => none
  | some ((_, b), t) => some (b, t)

instance [Ord α] : ToStream (Values α β) (Values.Stream α β) := ⟨Values.toStream⟩
instance : Stream (Values.Stream α β) β := ⟨Values.Stream.next?⟩

/-- `O(1)`. Is the tree empty? -/
@[inline] def isEmpty [Ord α] : RBMap α β → Bool := RBSet.isEmpty

/-- `O(n)`. Convert the tree to a list in ascending order. -/
@[inline] def toList [Ord α] : RBMap α β → List (α × β) := RBSet.toList

/-- `O(log n)`. Returns the key-value pair `(a, b)` such that `a ≤ k` for all keys in the RBMap. -/
@[inline] protected def min? [Ord α] : RBMap α β → Option (α × β) := RBSet.min?

/-- `O(log n)`. Returns the key-value pair `(a, b)` such that `a ≥ k` for all keys in the RBMap. -/
@[inline] protected def max? [Ord α] : RBMap α β → Option (α × β) := RBSet.max?

@[deprecated (since := "2024-04-17")] protected alias min := RBMap.min?
@[deprecated (since := "2024-04-17")] protected alias max := RBMap.max?

instance [Repr α] [Repr β] [Ord α] : Repr (RBMap α β) where
  reprPrec m prec := Repr.addAppParen ("RBMap.ofList " ++ repr m.toList) prec

/-- `O(log n)`. Insert key-value pair `(k, v)` into the tree. -/
@[inline] def insert [Ord α] (t : RBMap α β) (k : α) (v : β) : RBMap α β := RBSet.insert t (k, v)

/-- `O(log n)`. Remove an element `k` from the map. -/
@[inline] def erase [Ord α] (t : RBMap α β) (k : α) : RBMap α β := RBSet.erase t (compare k ·.1)

/-- `O(n log n)`. Build a tree from an unsorted list by inserting them one at a time. -/
@[inline] def ofList [Ord α] (l : List (α × β)) : RBMap α β :=
  RBSet.ofList l

/-- `O(n log n)`. Build a tree from an unsorted array by inserting them one at a time. -/
@[inline] def ofArray [Ord α] (l : Array (α × β)) : RBMap α β :=
  RBSet.ofArray l

/-- `O(log n)`. Find an entry in the tree with key equal to `k`. -/
@[inline] def findEntry? [Ord α] (t : RBMap α β) (k : α) : Option (α × β) := t.findP? (compare k ·.1)

/-- `O(log n)`. Find the value corresponding to key `k`. -/
@[inline] def find? [Ord α] (t : RBMap α β) (k : α) : Option β := t.findEntry? k |>.map (·.2)

/-- `O(log n)`. Find the value corresponding to key `k`, or return `v₀` if it is not in the map. -/
@[inline] def findD [Ord α] (t : RBMap α β) (k : α) (v₀ : β) : β := (t.find? k).getD v₀

/--
`O(log n)`. `lowerBound? k` retrieves the key-value pair of the largest key
smaller than or equal to `k`, if it exists.
-/
@[inline] def lowerBound? [Ord α] (t : RBMap α β) (k : α) : Option (α × β) :=
   RBSet.lowerBoundP? t (compare k ·.1)

/-- `O(log n)`. Returns true if the given key `a` is in the RBMap. -/
@[inline] def contains [Ord α] (t : RBMap α β) (a : α) : Bool := (t.findEntry? a).isSome

/-- `O(n)`. Returns true if the given predicate is true for all items in the RBMap. -/
@[inline] def all [Ord α] (t : RBMap α β) (p : α → β → Bool) : Bool := RBSet.all t fun (a, b) => p a b

/-- `O(n)`. Returns true if the given predicate is true for any item in the RBMap. -/
@[inline] def any [Ord α] (t : RBMap α β) (p : α → β → Bool) : Bool := RBSet.any t fun (a, b) => p a b

/--
Asserts that `t₁` and `t₂` have the same number of elements in the same order,
and `R` holds pairwise between them. The tree structure is ignored.
-/
@[inline] def all₂ [Ord α] [Ord γ] (R : α × β → γ × δ → Bool) (t₁ : RBMap α β) (t₂ : RBMap γ δ) : Bool :=
  RBSet.all₂ R t₁ t₂

/-- Asserts that `t₁` and `t₂` have the same set of keys (up to equality). -/
@[inline] def eqKeys [Ord α] (t₁ : RBMap α β) (t₂ : RBMap α γ) : Bool :=
  t₁.all₂ (compare ·.1 ·.1 = .eq) t₂

/--
Returns true if `t₁` and `t₂` have the same keys and values
(assuming `cmp` and `==` are compatible), ignoring the internal tree structure.
-/
instance [BEq α] [BEq β] [Ord α] : BEq (RBMap α β) := inferInstanceAs (BEq (RBSet ..))

/-- `O(n)`. The number of items in the RBMap. -/
def size [Ord α] : RBMap α β → Nat := RBSet.size

/-- `O(log n)`. Returns the minimum element of the map, or panics if the map is empty. -/
@[inline] def min! [Inhabited α] [Inhabited β] [Ord α] : RBMap α β → α × β := RBSet.min!

/-- `O(log n)`. Returns the maximum element of the map, or panics if the map is empty. -/
@[inline] def max! [Inhabited α] [Inhabited β] [Ord α] : RBMap α β → α × β := RBSet.max!

/-- Attempts to find the value with key `k : α` in `t` and panics if there is no such key. -/
@[inline] def find! [Ord α] [Inhabited β] (t : RBMap α β) (k : α) : β :=
  (t.find? k).getD (panic! "key is not in the map")

/--
`O(n₂ * log (n₁ + n₂))`. Merges the maps `t₁` and `t₂`, if a key `a : α` exists in both,
then use `mergeFn a b₁ b₂` to produce the new merged value.
-/
def mergeWith [Ord α] (mergeFn : α → β → β → β) (t₁ t₂ : RBMap α β) : RBMap α β :=
  RBSet.mergeWith (fun (_, b₁) (a, b₂) => (a, mergeFn a b₁ b₂)) t₁ t₂

/--
`O(n₁ * log (n₁ + n₂))`. Intersects the maps `t₁` and `t₂`
using `mergeFn a b` to produce the new value.
-/
def intersectWith [Ord α] (mergeFn : α → β → γ → δ) (t₁ : RBMap α β) (t₂ : RBMap α γ): RBMap α δ :=
  RBSet.intersectWith (compare ·.1 ·.1) (fun (a, b₁) (_, b₂) => (a, mergeFn a b₁ b₂)) t₁ t₂

/-- `O(n * log n)`. Constructs the set of all elements satisfying `p`. -/
def filter [Ord α] (t : RBMap α β) (p : α → β → Bool) : RBMap α β :=
  RBSet.filter t fun (a, b) => p a b

/--
`O(n₁ * (log n₁ + log n₂))`. Constructs the set of all elements of `t₁` that are not in `t₂`.
-/
def sdiff [Ord α] (t₁ t₂ : RBMap α β) : RBMap α β := t₁.filter fun a _ => !t₂.contains a

end RBMap
end Batteries
open Batteries

@[inherit_doc RBMap.ofList]
abbrev List.toRBMap [Ord α] (l : List (α × β)) : RBMap α β :=
  RBMap.ofList l
