import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-! Elementary finite probability bounds used by the short-degree distinguisher.
No geometric facts are assumed or declared in this module. -/

namespace IsogenyAttack

open scoped BigOperators

/-- A finite probability law, with real-valued masses. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  mass_sum : ∑ x, mass x = 1

namespace FiniteLaw

variable {α β τ : Type*} [Fintype α]

/-- Normalize finite nonnegative weights with a positive total. -/
noncomputable def ofWeights (w : α → ℝ) (hnonneg : ∀ x, 0 ≤ w x)
    (hpos : 0 < ∑ x, w x) : FiniteLaw α where
  mass x := w x / ∑ y, w y
  mass_nonneg x := div_nonneg (hnonneg x) (le_of_lt hpos)
  mass_sum := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpos)

@[simp] theorem ofWeights_mass (w : α → ℝ) (hnonneg : ∀ x, 0 ≤ w x)
    (hpos : 0 < ∑ x, w x) (x : α) :
    (ofWeights w hnonneg hpos).mass x = w x / ∑ y, w y := rfl

/-- Probability of an event. -/
noncomputable def eventMass (P : FiniteLaw α) (E : α → Prop) : ℝ := by
  classical
  exact ∑ x, if E x then P.mass x else 0

/-- Rewrite with any chosen decision procedure for the event. -/
theorem eventMass_eq_sum (P : FiniteLaw α) (E : α → Prop) [DecidablePred E] :
    P.eventMass E = ∑ x, if E x then P.mass x else 0 := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

@[simp] theorem eventMass_false (P : FiniteLaw α) :
    P.eventMass (fun _ => False) = 0 := by
  simp [eventMass]

@[simp] theorem eventMass_true (P : FiniteLaw α) :
    P.eventMass (fun _ => True) = 1 := by
  simpa [eventMass] using P.mass_sum

theorem eventMass_nonneg (P : FiniteLaw α) (E : α → Prop) :
    0 ≤ P.eventMass E := by
  classical
  exact Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact P.mass_nonneg x
    · exact le_rfl

theorem eventMass_mono (P : FiniteLaw α) {E F : α → Prop}
    (h : ∀ x, E x → F x) : P.eventMass E ≤ P.eventMass F := by
  classical
  apply Finset.sum_le_sum
  intro x _
  split_ifs with he hf
  · exact le_rfl
  · exact False.elim (hf (h x he))
  · exact P.mass_nonneg x
  · exact le_rfl

theorem eventMass_le_one (P : FiniteLaw α) (E : α → Prop) :
    P.eventMass E ≤ 1 := by
  simpa using P.eventMass_mono (E := E) (F := fun _ => True) (fun _ _ => trivial)

theorem eventMass_congr (P : FiniteLaw α) {E F : α → Prop}
    (h : ∀ x, E x ↔ F x) : P.eventMass E = P.eventMass F := by
  classical
  unfold eventMass
  apply Finset.sum_congr rfl
  intro x _
  simp only [h x]

/-- A deterministic transformation that preserves public degree preserves every
threshold test on that degree. No distributional approximation is needed. -/
theorem degree_preserving_event (P : FiniteLaw α) (push : α → β)
    (degreeBefore : α → ℕ) (degreeAfter : β → ℕ) (L : ℕ)
    (hdegree : ∀ x, degreeAfter (push x) = degreeBefore x) :
    P.eventMass (fun x => degreeAfter (push x) ≤ L) =
      P.eventMass (fun x => degreeBefore x ≤ L) := by
  apply P.eventMass_congr
  intro x
  rw [hdegree x]

/-- Summing the point masses over a finite set is an event probability. -/
theorem eventMass_mem [DecidableEq α] (P : FiniteLaw α) (S : Finset α) :
    P.eventMass (fun x => x ∈ S) = ∑ x ∈ S, P.mass x := by
  classical
  rw [eventMass_eq_sum]
  calc
    (∑ x, if x ∈ S then P.mass x else 0) =
        ∑ x ∈ S, if x ∈ S then P.mass x else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro x _ hx
      exact if_neg hx
    _ = ∑ x ∈ S, P.mass x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact if_pos hx

/-- Distinct favorable outcomes give a lower bound by their total mass. -/
theorem favorable_injection_bound [Fintype β] (P : FiniteLaw α)
    (E : α → Prop) (i : β → α) (hi : Function.Injective i)
    (q : β → ℝ) (haccept : ∀ b, E (i b))
    (hmass : ∀ b, q b ≤ P.mass (i b)) :
    ∑ b, q b ≤ P.eventMass E := by
  classical
  calc
    ∑ b, q b ≤ ∑ b, P.mass (i b) := Finset.sum_le_sum fun b _ => hmass b
    _ = ∑ x ∈ Finset.univ.image i, P.mass x := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact hi hxy
    _ = P.eventMass (fun x => x ∈ Finset.univ.image i) :=
      (P.eventMass_mem _).symm
    _ ≤ P.eventMass E := P.eventMass_mono fun x hx => by
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
      exact haccept b

/-- Exact partition of a finite law by the value of a target map. -/
theorem target_set_mass [Fintype τ] [DecidableEq τ]
    (P : FiniteLaw α) (target : α → τ) (S : Finset τ) :
    P.eventMass (fun x => target x ∈ S) =
      ∑ t ∈ S, P.eventMass (fun x => target x = t) := by
  classical
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.sum_ite_eq', eq_comm]
  split_ifs <;> rfl

/-- If an accepted outcome can reach only a specified set of targets, and
all target marginal masses are at most `a`, its probability is at most
`a * S.card`. This also covers outcomes encoding a failure symbol. -/
theorem target_support_bound [Fintype τ] [DecidableEq τ]
    (P : FiniteLaw α) (E : α → Prop) (target : α → τ) (S : Finset τ)
    (a : ℝ) (hsupport : ∀ x, E x → target x ∈ S)
    (hpoint : ∀ t ∈ S, P.eventMass (fun x => target x = t) ≤ a) :
    P.eventMass E ≤ a * (S.card : ℝ) := by
  calc
    P.eventMass E ≤ P.eventMass (fun x => target x ∈ S) :=
      P.eventMass_mono hsupport
    _ = ∑ t ∈ S, P.eventMass (fun x => target x = t) := P.target_set_mass target S
    _ ≤ ∑ _t ∈ S, a := Finset.sum_le_sum fun t ht => hpoint t ht
    _ = a * (S.card : ℝ) := by simp [mul_comm]

/-- The difference of acceptance probabilities lower-bounds the usual
absolute distinguishing advantage. -/
theorem gap_le_abs {x y g : ℝ} (h : g ≤ x - y) : g ≤ |x - y| :=
  h.trans (le_abs_self _)

/-- A test's advantage over a fair guess is half its signed event gap. -/
theorem fair_bit_success (x y : ℝ) :
    (x + (1 - y)) / 2 - 1 / 2 = (x - y) / 2 := by ring

end FiniteLaw
end IsogenyAttack
