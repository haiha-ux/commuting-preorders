import CommutingPreorders.Basic

/-
  The witness lemma. No transitivity is used, so the statement holds for arbitrary
  relations on arbitrary (finite or infinite) types.
-/
universe u

namespace CommutingPreorders

/-- `x` is `le`-maximal: `x` lies in the domain and its neighbourhood is `{x}`. -/
def IsMax {α : Type u} (le : α → α → Prop) (x : α) : Prop :=
  le x x ∧ ∀ y, le x y → y = x

/-- `z` is `le`-minimal: every `w` with `le w z` equals `z` (vacuous outside the domain). -/
def IsMin {α : Type u} (le : α → α → Prop) (z : α) : Prop :=
  ∀ w, le w z → w = z

/-- A witness `x ∈ Max_A`, `z ∈ Min_B`, `x ≠ z`, `x ≤_B y`, `y ≤_A z` forces non-commutation;
    the subset `S = {u | u ≠ z}` separates the two composites at `x`. -/
theorem witness_noncommute {α : Type u} (leA leB : α → α → Prop)
    (hdomB : ∀ a b, leB a b → leB a a)
    (x y z : α) (hx : IsMax leA x) (hz : IsMin leB z) (hxz : x ≠ z)
    (hxy : leB x y) (hyz : leA y z) :
    ∃ S : SetOf α, intr leA (intr leB S) ≠ intr leB (intr leA S) := by
  refine ⟨fun u => u ≠ z, ?_⟩
  intro heq
  -- x ∈ B(S): x is in the domain of B and x ≤_B z would force x = z.
  have hxBS : intr leB (fun u => u ≠ z) x :=
    ⟨hdomB x y hxy, fun w hw hwz => hxz (hz x (by subst hwz; exact hw))⟩
  -- x ∈ A(B(S)): the neighbourhood of x in A is {x}.
  have hxA : intr leA (intr leB (fun u => u ≠ z)) x :=
    ⟨hx.1, fun u hu => by have hux := hx.2 u hu; subst hux; exact hxBS⟩
  -- x ∉ B(A(S)): y is in the B-neighbourhood of x, but z lies in the A-neighbourhood of y.
  have hxB : intr leB (intr leA (fun u => u ≠ z)) x := Eq.mp (congrFun heq x) hxA
  exact (hxB.2 y hxy).2 z hyz rfl

end CommutingPreorders
