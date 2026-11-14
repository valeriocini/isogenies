import IsogenyAttack.Vendor.Iut.Torsion.Count

/-!
Geometric torsion in the characteristic is detected by the actual division
polynomials. These statements use the proved elliptic-curve group law and
apply even when the integer acts as zero in the ground field.
-/

namespace IsogenyAttack.CharacteristicTorsion

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  {W : Affine K} [W.IsElliptic] (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)

include ha₁ ha₃

/-- The squared division polynomial is nonzero for every positive integer,
including multiples of the characteristic. -/
theorem divisionPolynomial_ne_zero (n : ℕ) (hn : n ≠ 0) : W.ΨSq n ≠ 0 := by
  have hd : (W.Φ n).degree ≠ 0 := by
    rw [degree_eq_natDegree (W.Φ_ne_zero n), W.natDegree_Φ]
    simpa using (pow_ne_zero 2 hn)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (W.Φ n) hd
  intro hzero
  have hne := Iut.Torsion.ΨSq_ne_zero_of_Φ_eq_zero ha₁ ha₃ n hn hx
  exact hne (by simp [hzero])

/-- Trivial geometric n-torsion is equivalent to the division polynomial
having no geometric root. -/
theorem trivial_torsion_iff_no_roots (n : ℕ) :
    (∀ P : W.Point, n • P = 0 → P = 0) ↔
      ∀ x : K, (W.ΨSq n).eval x ≠ 0 := by
  constructor
  · intro h x hx
    obtain ⟨y, hxy⟩ := Iut.Torsion.exists_point ha₁ ha₃ x
    exact Point.some_ne_zero hxy
      (h _ ((Iut.Torsion.smul_eq_zero_iff_ΨSq ha₁ ha₃ hxy n).mpr hx))
  · intro h P hP
    rcases P with _ | ⟨x, y, hxy⟩
    · rfl
    · exact False.elim (h x
        ((Iut.Torsion.smul_eq_zero_iff_ΨSq ha₁ ha₃ hxy n).mp hP))

/-- An exact polynomial criterion for trivial geometric n-torsion. Unlike
the prime-to-characteristic torsion-count theorem, n need not be invertible. -/
theorem trivial_torsion_iff_constant (n : ℕ) :
    (∀ P : W.Point, n • P = 0 → P = 0) ↔
      ∃ c : K, c ≠ 0 ∧ W.ΨSq n = C c := by
  rw [trivial_torsion_iff_no_roots ha₁ ha₃]
  constructor
  · intro h
    have hdeg : (W.ΨSq n).degree ≤ 0 := by
      by_contra hd
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (W.ΨSq n) (ne_of_gt (lt_of_not_ge hd))
      exact h x hx
    refine ⟨(W.ΨSq n).coeff 0, ?_, eq_C_of_degree_le_zero hdeg⟩
    have hx := h 0
    simpa only [coeff_zero_eq_eval_zero] using hx
  · rintro ⟨c, hc, heq⟩ x
    simpa only [heq, eval_C] using hc

/-- With n positive, it suffices to establish that the division polynomial
has degree zero; its nonvanishing is a theorem about the actual curve. -/
theorem trivial_torsion_iff_natDegree_zero (n : ℕ) (hn : n ≠ 0) :
    (∀ P : W.Point, n • P = 0 → P = 0) ↔
      (W.ΨSq n).natDegree = 0 := by
  rw [trivial_torsion_iff_constant ha₁ ha₃]
  constructor
  · rintro ⟨c, hc, heq⟩
    simp [heq]
  · intro h
    have heq := eq_C_of_natDegree_eq_zero h
    refine ⟨(W.ΨSq n).coeff 0, ?_, heq⟩
    intro hc
    exact divisionPolynomial_ne_zero ha₁ ha₃ n hn (heq.trans (by rw [hc, C_0]))

end IsogenyAttack.CharacteristicTorsion
