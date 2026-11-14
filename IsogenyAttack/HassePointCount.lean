import IsogenyAttack.HasseCriterion
import IsogenyAttack.HasseCoefficientIteration
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! The Hasse coefficient as the actual rational-point count modulo the
characteristic. All points are Mathlib Weierstrass points, including infinity. -/
namespace IsogenyAttack.Legendre
open Polynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

lemma sum_pow_nonzero (i : ℕ) (hi : i ≠ 0) :
    (∑ x : K, x^i) = if Fintype.card K-1 ∣ i then -1 else 0 := by
  let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
  have he : univ.map φ = univ \ {(0 : K)} := by
    ext x
    simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk,
      true_and, mem_sdiff, mem_singleton, φ]
    constructor
    · rintro ⟨a, rfl⟩
      exact Units.ne_zero a
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  calc
    (∑ x : K, x^i) = ∑ x ∈ univ \ {(0 : K)}, x^i := by
      rw [← sum_sdiff ({0} : Finset K).subset_univ,
        sum_singleton, zero_pow hi, add_zero]
    _ = ∑ x : Kˣ, (x^i : K) := by simp [φ, ← he, univ.sum_map φ]
    _ = _ := FiniteField.sum_pow_units K i

/-- Below twice q−1, the only nonzero power sum is the (q−1)-st. -/
lemma sum_pow_lt_twice_card_sub_one (i : ℕ) (hi : i < 2*(Fintype.card K-1)) :
    (∑ x : K, x^i) = if i=Fintype.card K-1 then -1 else 0 := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  by_cases hi0 : i=0
  · subst i
    simp [show ¬0=Fintype.card K-1 by omega]
  · rw [sum_pow_nonzero i hi0]
    congr 1
    apply propext
    constructor
    · rintro ⟨d, hd⟩
      have hdpos : 0<d := by
        apply Nat.pos_of_ne_zero
        intro hd0
        simp only [hd0, mul_zero] at hd
        exact hi0 hd
      have hdlt : d<2 := by nlinarith
      have : d=1 := by omega
      simpa [this] using hd
    · intro h; rw [h]

/-- Summing evaluations extracts minus the q−1 coefficient in this degree range. -/
theorem sum_eval_eq_neg_coeff (f : K[X])
    (hf : f.natDegree < 2*(Fintype.card K-1)) :
    (∑ x : K, f.eval x) = -f.coeff (Fintype.card K-1) := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  simp_rw [eval_eq_sum_range' hf]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hsum : ∀ i ∈ range (2*(Fintype.card K-1)),
      (∑ x : K, x^i) = if i=Fintype.card K-1 then -1 else 0 :=
    fun i hi => sum_pow_lt_twice_card_sub_one i (mem_range.mp hi)
  simp_rw [Finset.sum_congr rfl (fun i hi => congrArg (f.coeff i * ·) (hsum i hi))]
  simp [show Fintype.card K-1 < 2*(Fintype.card K-1) by omega]

omit [Fintype K] [DecidableEq K] in
lemma cubicRHS_natDegree_le (W : WeierstrassCurve K) : (cubicRHS W).natDegree ≤ 3 := by
  unfold cubicRHS
  compute_degree!

/-- The exact integer point count as a sum of quadratic characters. -/
theorem card_point_eq_quadraticChar (W : WeierstrassCurve K) [W.IsElliptic]
    (h1 : W.a₁=0) (h3 : W.a₃=0) (hchar : ringChar K ≠ 2) :
    (Nat.card W.toAffine.Point : ℤ) = Fintype.card K + 1 +
      ∑ x : K, quadraticChar K ((cubicRHS W).eval x) := by
  classical
  have heq : ∀ x y : K, W.toAffine.Equation x y ↔ y^2=(cubicRHS W).eval x := by
    intro x y
    rw [WeierstrassCurve.Affine.equation_iff']
    simp [h1, h3, cubicRHS, sub_eq_zero]
  have hc : Nat.card W.toAffine.Point =
      (∑ x : K, Fintype.card {y : K // y^2=(cubicRHS W).eval x}) + 1 := by
    rw [Nat.card_congr W.toAffine.pointEquiv]
    change Nat.card (Option {xy : K×K // W.toAffine.Equation xy.1 xy.2}) = _
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_congr
      (Equiv.subtypeProdEquivSigmaSubtype (fun x y : K => W.toAffine.Equation x y))]
    rw [Fintype.card_sigma]
    congr 1
    apply sum_congr rfl
    intro x _
    exact Fintype.card_congr (Equiv.subtypeEquivProp (funext fun y => propext (heq x y)))
  rw [hc]
  push_cast
  have hs : ∀ x : K, (Fintype.card {y : K // y^2=(cubicRHS W).eval x} : ℤ) =
      quadraticChar K ((cubicRHS W).eval x)+1 := by
    intro x
    simpa only [Set.toFinset_card, Nat.card_eq_fintype_card, Set.coe_ofPred] using
      quadraticChar_card_sqrts hchar ((cubicRHS W).eval x)
  simp_rw [hs]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
  ring

/-- The point count reduced in the base field is 1 minus the middle
coefficient of the (q−1)/2-th power of the actual Weierstrass cubic. -/
theorem card_point_cast_eq_one_sub_coefficient (W : WeierstrassCurve K) [W.IsElliptic]
    (h1 : W.a₁=0) (h3 : W.a₃=0) (hchar : ringChar K ≠ 2) :
    (Nat.card W.toAffine.Point : K) = 1 -
      ((cubicRHS W)^((Fintype.card K-1)/2)).coeff (Fintype.card K-1) := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hodd := FiniteField.odd_card_of_char_ne_two hchar
  have hhalf : Fintype.card K/2 = (Fintype.card K-1)/2 := by omega
  have hc := congrArg (fun z : ℤ => (z : K)) (card_point_eq_quadraticChar W h1 h3 hchar)
  push_cast at hc
  rw [FiniteField.cast_card_eq_zero, zero_add] at hc
  simp_rw [quadraticChar_eq_pow_of_char_ne_two' hchar, hhalf, ← eval_pow] at hc
  have hd : ((cubicRHS W)^((Fintype.card K-1)/2)).natDegree < 2*(Fintype.card K-1) := by
    calc
      _ ≤ 3*((Fintype.card K-1)/2) := by
        exact (natDegree_pow_le).trans (by
          simpa only [Nat.mul_comm] using Nat.mul_le_mul_left
            ((Fintype.card K-1)/2) (cubicRHS_natDegree_le W))
      _ < _ := by omega
  rw [sum_eval_eq_neg_coeff _ hd] at hc
  simpa only [sub_eq_add_neg] using hc

/-- The exact divisibility criterion required by the supersingular trace
theorem: p divides q+1−#E precisely when the q-Hasse coefficient vanishes. -/
theorem characteristic_dvd_pointTrace_iff (p : ℕ) [CharP K p]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (h1 : W.a₁=0) (h3 : W.a₃=0) (hchar : ringChar K ≠ 2) :
    (p : ℤ) ∣ ((Fintype.card K : ℤ)+1-Nat.card W.toAffine.Point) ↔
      ((cubicRHS W)^((Fintype.card K-1)/2)).coeff (Fintype.card K-1) = 0 := by
  rw [← CharP.intCast_eq_zero_iff K p]
  push_cast
  rw [FiniteField.cast_card_eq_zero, card_point_cast_eq_one_sub_coefficient W h1 h3 hchar]
  ring_nf

/-- Over every finite field of odd characteristic, the ordinary Hasse
coefficient vanishes exactly when the actual Frobenius trace is divisible by p.
No assertion about p-torsion is assumed in the point-count calculation. -/
theorem characteristic_dvd_pointTrace_iff_hasseCoefficient (p : ℕ)
    [CharP K p] [Fact p.Prime] (hp : 2 < p)
    (W : WeierstrassCurve K) [W.IsElliptic] (h1 : W.a₁=0) (h3 : W.a₃=0) :
    (p : ℤ) ∣ ((Fintype.card K : ℤ)+1-Nat.card W.toAffine.Point) ↔
      hasseCoefficient p W = 0 := by
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K p]; omega
  rw [characteristic_dvd_pointTrace_iff p W h1 h3 hchar]
  obtain ⟨r, _, hr⟩ := FiniteField.card K p
  rw [hr]
  exact hasseCoefficient_primePower_zero_iff p r hp r.pos
    (cubicRHS W) (cubicRHS_natDegree_le W)

end IsogenyAttack.Legendre
