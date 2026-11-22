/-
  Definitions shared by all files.

  A subset of `α` is a predicate `α → Prop`. A relation `le : α → α → Prop` stands for a
  quasi-order on the subset `{x | le x x}` (the domain); the neighbourhood of `x` is
  `{y | le x y}` and the open sets are the up-sets. The interior operator of `le` sends `S`
  to the set of `x` with `le x x` whose neighbourhood lies in `S`.
-/
universe u

namespace CommutingPreorders

/-- Subsets of `α`, as predicates. -/
abbrev SetOf (α : Type u) := α → Prop

/-- Inclusion of subsets. -/
def SubsetOf {α : Type u} (l r : SetOf α) : Prop := ∀ x, l x → r x

/-- Intersection of two subsets. -/
def meet {α : Type u} (l r : SetOf α) : SetOf α := fun x => l x ∧ r x

/-- The whole set. -/
def top {α : Type u} : SetOf α := fun _ => True

/-- The interior operator of a relation: `intr le S = {x | le x x ∧ ∀ y, le x y → y ∈ S}`. -/
def intr {α : Type u} (le : α → α → Prop) (S : SetOf α) : SetOf α :=
  fun x => le x x ∧ ∀ y, le x y → S y

/-- The interior operator is contracting. -/
theorem intr_subset {α : Type u} (le : α → α → Prop) (S : SetOf α) (x : α)
    (h : intr le S x) : S x :=
  h.2 x h.1

end CommutingPreorders
