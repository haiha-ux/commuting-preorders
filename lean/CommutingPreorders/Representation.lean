import CommutingPreorders.Basic

/-
  Representation of interior operators by relations.

  `interior_is_intr`: on a type with a finite list of all its elements, an operator that is
  contracting, meet-preserving and idempotent is `intr` of the relation `interiorLe`, where
  `x ≤ y` means that `x` lies in `A(top)` and `y` belongs to every fixed point of `A` that
  contains `x`.
  `intr_is_interior`: conversely, `intr` of a transitive relation with `le x y → le y y` is
  contracting, meet-preserving and idempotent.
-/
universe u

namespace CommutingPreorders

variable {α : Type u}

/-- A meet-preserving operator sends a fixed point contained in `T` into `A(T)`. -/
theorem interior_greatest_fixed
    (A : SetOf α → SetOf α)
    (preserves_meet : ∀ l r, A (meet l r) = meet (A l) (A r))
    (F T : SetOf α) (hF : A F = F) (hFT : SubsetOf F T) :
    SubsetOf F (A T) := by
  intro x hx
  have meet_eq : meet F T = F := by
    funext p
    apply propext
    exact ⟨fun h => h.1, fun h => ⟨h, hFT p h⟩⟩
  have h1 : A (meet F T) x := by
    rw [meet_eq, hF]
    exact hx
  have h2 : meet (A F) (A T) x := by
    rw [← preserves_meet]
    exact h1
  exact h2.2

/-- `x ≤_A y` iff `x ∈ A(top)` and `y` lies in every fixed point of `A` containing `x`. -/
def interiorLe (A : SetOf α → SetOf α) : α → α → Prop :=
  fun x y => A top x ∧ ∀ S, A S = S → S x → S y

theorem interior_is_intr (univ : List α) (hu : ∀ x, x ∈ univ)
    (A : SetOf α → SetOf α)
    (contractive : ∀ S, SubsetOf (A S) S)
    (preserves_meet : ∀ l r, A (meet l r) = meet (A l) (A r))
    (idem : ∀ S, A (A S) = A S) (S : SetOf α) :
    A S = intr (interiorLe A) S := by
  funext x
  apply propext
  constructor
  · intro hx
    have hxt : A top x :=
      interior_greatest_fixed A preserves_meet (A S) top (idem S) (fun _ _ => True.intro) x hx
    exact ⟨⟨hxt, fun _ _ h => h⟩,
      fun y hy => contractive S y (hy.2 (A S) (idem S) hx)⟩
  · rintro ⟨⟨hxt, _⟩, h⟩
    -- Intersect finitely many fixed points containing x, discarding every y with ¬ x ≤_A y.
    have key : ∀ l : List α, ∃ G : SetOf α, A G = G ∧ G x ∧
        ∀ y, y ∈ l → ¬ G y ∨ interiorLe A x y := by
      intro l
      induction l with
      | nil => exact ⟨A top, idem top, hxt, fun _ hy => nomatch hy⟩
      | cons y l ih =>
        obtain ⟨G, hG, hGx, hl⟩ := ih
        by_cases hle : interiorLe A x y
        · refine ⟨G, hG, hGx, fun z hz => ?_⟩
          rcases List.mem_cons.mp hz with rfl | hz
          · exact Or.inr hle
          · exact hl z hz
        · obtain ⟨F, hF, hFx, hFy⟩ : ∃ F, A F = F ∧ F x ∧ ¬ F y :=
            Classical.byContradiction fun hn =>
              hle ⟨hxt, fun F hF hFx => Classical.byContradiction fun hFy => hn ⟨F, hF, hFx, hFy⟩⟩
          refine ⟨meet G F, ?_, ⟨hGx, hFx⟩, fun z hz => ?_⟩
          · rw [preserves_meet, hG, hF]
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact Or.inl fun hm => hFy hm.2
            · exact (hl z hz).imp (fun hn hm => hn hm.1) id
    obtain ⟨G, hG, hGx, hl⟩ := key univ
    have hGS : SubsetOf G S := fun y hy =>
      match hl y (hu y) with
      | Or.inl hn => absurd hy hn
      | Or.inr hle => h y hle
    exact interior_greatest_fixed A preserves_meet G S hG hGS x hGx

/-- `intr le` is an interior operator when `le x y → le y y` and `le` is transitive.
    Contraction and meet preservation use neither hypothesis; idempotence uses both. -/
theorem intr_is_interior (le : α → α → Prop)
    (hr : ∀ x y, le x y → le y y) (htr : ∀ x y z, le x y → le y z → le x z) :
    (∀ S, SubsetOf (intr le S) S) ∧
    (∀ l r, intr le (meet l r) = meet (intr le l) (intr le r)) ∧
    (∀ S, intr le (intr le S) = intr le S) := by
  refine ⟨fun S x h => intr_subset le S x h, fun l r => ?_, fun S => ?_⟩
  · funext x
    apply propext
    exact ⟨fun ⟨hx, h⟩ => ⟨⟨hx, fun y hy => (h y hy).1⟩, ⟨hx, fun y hy => (h y hy).2⟩⟩,
           fun ⟨⟨hx, h1⟩, ⟨_, h2⟩⟩ => ⟨hx, fun y hy => ⟨h1 y hy, h2 y hy⟩⟩⟩
  · funext x
    apply propext
    exact ⟨fun ⟨hx, h⟩ => ⟨hx, fun y hy => (h y hy).2 y (hr x y hy)⟩,
           fun ⟨hx, h⟩ => ⟨hx, fun y hy => ⟨hr x y hy, fun z hz => h z (htr x y z hy hz)⟩⟩⟩

end CommutingPreorders
