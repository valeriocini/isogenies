import IsogenyAttack.LegendreCurve
import IsogenyAttack.Probability
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Uniform Legendre-parameter laws and their exact geometric fiber bound. -/

namespace IsogenyAttack
open scoped BigOperators

namespace FiniteLaw

/-- Uniform law on a nonempty finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  mass _ := 1 / (Fintype.card α : ℝ)
  mass_nonneg _ := by positivity
  mass_sum := by
    have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
    simp [h]

/-- Deterministic pushforward of a finite law. -/
noncomputable def pushForward {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (f : α → β) : FiniteLaw β where
  mass b := P.eventMass (fun a => f a = b)
  mass_nonneg b := P.eventMass_nonneg _
  mass_sum := by
    classical
    simpa using (P.target_set_mass f Finset.univ).symm

theorem uniform_event {α : Type*} [Fintype α] [Nonempty α] (E : α → Prop) [DecidablePred E] :
    (uniform α).eventMass E = (Fintype.card {a // E a} : ℝ) / Fintype.card α := by
  classical
  rw [eventMass_eq_sum]
  simp only [uniform]
  rw [← Finset.sum_filter]
  simp [Fintype.card_subtype, div_eq_mul_inv]

end FiniteLaw

namespace Legendre
variable {K : Type*} [Field K]

/-- The degree-six fiber bound for any injectively indexed finite parameter set. -/
theorem j_fiber_card_type_le_six {α : Type*} [Fintype α]
    (f : α → K) (hf : Function.Injective f) (j : K) (h256 : (256 : K) ≠ 0)
    (h : ∀ a, f a ≠ 0 ∧ f a ≠ 1 ∧ jInvariant (f a) = j) :
    Fintype.card α ≤ 6 := by
  by_contra hc
  have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (fiberPolynomial j) hf (fun a => fiberPolynomial_root (h a).1 (h a).2.1 (h a).2.2)
    (lt_of_le_of_lt (fiberPolynomial_natDegree_le j) (Nat.lt_of_not_ge hc))
  exact fiberPolynomial_ne_zero j h256 hzero

/-- Uniformly chosen distinct nonsingular Legendre parameters put at most
6/card(alpha) probability on any j-invariant. -/
theorem uniform_j_mass_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → K) (hf : Function.Injective f) (h256 : (256 : K) ≠ 0)
    (hgood : ∀ a, f a ≠ 0 ∧ f a ≠ 1) (j : K) :
    (FiniteLaw.uniform α).eventMass (fun a => jInvariant (f a) = j) ≤
      6 / (Fintype.card α : ℝ) := by
  classical
  rw [FiniteLaw.uniform_event]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hcard : Fintype.card {a // jInvariant (f a) = j} ≤ 6 :=
    j_fiber_card_type_le_six (fun a : {a // jInvariant (f a) = j} => f a.val)
      (fun a b hab => Subtype.ext (hf hab)) j h256
      (fun a => ⟨(hgood a.val).1, (hgood a.val).2, a.property⟩)
  exact_mod_cast hcard

/-- Over an algebraically closed field, a separable Hasse polynomial has exactly
n distinct roots. This uses the actual explicit polynomial defined above. -/
theorem hasse_root_count [DecidableEq K] [IsAlgClosed K] (n : ℕ)
    (hsep : (hassePolynomial (K := K) n).Separable) :
    (hassePolynomial (K := K) n).roots.toFinset.card = n := by
  classical
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
    IsAlgClosed.card_roots_eq_natDegree, hassePolynomial_natDegree]

end Legendre
end IsogenyAttack
