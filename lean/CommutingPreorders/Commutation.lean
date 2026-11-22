import CommutingPreorders.Basic
import CommutingPreorders.Representation

/-
  The commutation criterion. `CondC leA leB` is the condition C(A -> B) of the paper:
  for every `x` with `N_A(x)` non-empty and contained in `U_B`, and every `y ∈ N_B(x)`,
  `N_A(y)` is non-empty and contained in the union of `N_B(t)` over `t ∈ N_A(x)`.
  No transitivity is needed for `commute_iff_relcomp`.
-/
universe u

namespace CommutingPreorders

variable {α : Type u}

def CondC (leA leB : α → α → Prop) : Prop :=
  ∀ x, leA x x → (∀ t, leA x t → leB t t) → ∀ y, leB x y →
    leA y y ∧ ∀ z, leA y z → ∃ t, leA x t ∧ leB t z

theorem commute_iff_relcomp (leA leB : α → α → Prop) :
    (∀ S, intr leA (intr leB S) = intr leB (intr leA S)) ↔ CondC leA leB ∧ CondC leB leA := by
  have fwd : ∀ (la lb : α → α → Prop),
      (∀ S, intr la (intr lb S) = intr lb (intr la S)) → CondC la lb := by
    intro la lb hc x hx hN y hxy
    have hxA : intr la (intr lb (fun w => ∃ t, la x t ∧ lb t w)) x :=
      ⟨hx, fun u hu => ⟨hN u hu, fun w hw => ⟨u, hu, hw⟩⟩⟩
    have hxB := Eq.mp (congrFun (hc fun w => ∃ t, la x t ∧ lb t w) x) hxA
    exact hxB.2 y hxy
  have bwd : ∀ (la lb : α → α → Prop), CondC la lb → ∀ S x,
      intr la (intr lb S) x → intr lb (intr la S) x := by
    intro la lb hC S x ⟨hx, h⟩
    have hbb : lb x x := (h x hx).1
    refine ⟨hbb, fun y hy => ?_⟩
    obtain ⟨hyy, hz⟩ := hC x hx (fun t ht => (h t ht).1) y hy
    exact ⟨hyy, fun z hyz => let ⟨t, ht, htz⟩ := hz z hyz; (h t ht).2 z htz⟩
  constructor
  · intro hc
    exact ⟨fwd leA leB hc, fwd leB leA fun S => (hc S).symm⟩
  · rintro ⟨hAB, hBA⟩ S
    funext x
    exact propext ⟨bwd leA leB hAB S x, bwd leB leA hBA S x⟩

/-- Reflexive case (`U = Ω`): commutation is the usual commutation of relations. -/
theorem commute_iff_relcomp_refl (leA leB : α → α → Prop)
    (rA : ∀ x, leA x x) (rB : ∀ x, leB x x) :
    (∀ S, intr leA (intr leB S) = intr leB (intr leA S)) ↔
      (∀ x y z, leB x y → leA y z → ∃ t, leA x t ∧ leB t z) ∧
      (∀ x y z, leA x y → leB y z → ∃ t, leB x t ∧ leA t z) := by
  rw [commute_iff_relcomp]
  constructor
  · rintro ⟨hAB, hBA⟩
    exact ⟨fun x y z hy hz => (hAB x (rA x) (fun t _ => rB t) y hy).2 z hz,
           fun x y z hy hz => (hBA x (rB x) (fun t _ => rA t) y hy).2 z hz⟩
  · rintro ⟨hAB, hBA⟩
    exact ⟨fun x _ _ y hy => ⟨rA y, fun z hz => hAB x y z hy hz⟩,
           fun x _ _ y hy => ⟨rB y, fun z hz => hBA x y z hy hz⟩⟩

/-- Two interior operators on a type with a finite list of elements commute iff the condition
    C holds in both directions for their quasi-orders `interiorLe`. -/
theorem commute_iff_preorder (univ : List α) (hu : ∀ x, x ∈ univ)
    (A B : SetOf α → SetOf α)
    (cA : ∀ S, SubsetOf (A S) S) (mA : ∀ l r, A (meet l r) = meet (A l) (A r))
    (iA : ∀ S, A (A S) = A S)
    (cB : ∀ S, SubsetOf (B S) S) (mB : ∀ l r, B (meet l r) = meet (B l) (B r))
    (iB : ∀ S, B (B S) = B S) :
    (∀ S, A (B S) = B (A S)) ↔
      CondC (interiorLe A) (interiorLe B) ∧ CondC (interiorLe B) (interiorLe A) := by
  rw [← commute_iff_relcomp]
  have eA := interior_is_intr univ hu A cA mA iA
  have eB := interior_is_intr univ hu B cB mB iB
  constructor
  · intro h S
    rw [← eA, ← eB, ← eA, ← eB]; exact h S
  · intro h S
    rw [eA, eB, eA, eB]; exact h S

end CommutingPreorders
