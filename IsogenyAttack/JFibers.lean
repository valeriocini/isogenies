import IsogenyAttack.StationaryGeometry
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Exact geometric fibers of the Legendre j-invariant. -/
namespace IsogenyAttack.Legendre
open Polynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K]

@[simp] lemma fiberPolynomial_eval_zero (j : K) : (fiberPolynomial j).eval 0 = 256 := by
  simp [fiberPolynomial]
@[simp] lemma fiberPolynomial_eval_one (j : K) : (fiberPolynomial j).eval 1 = 256 := by
  simp [fiberPolynomial]

lemma fiberRoot_ne_zero {j t : K} (h256 : (256 : K) ≠ 0)
    (ht : (fiberPolynomial j).IsRoot t) : t ≠ 0 := by
  intro h; exact h256 (by simpa [h, IsRoot] using ht)
lemma fiberRoot_ne_one {j t : K} (h256 : (256 : K) ≠ 0)
    (ht : (fiberPolynomial j).IsRoot t) : t ≠ 1 := by
  intro h; exact h256 (by simpa [h, IsRoot] using ht)

lemma fiberPolynomial_isRoot_iff {j t : K} (h256 : (256 : K) ≠ 0) :
    (fiberPolynomial j).IsRoot t ↔ t ≠ 0 ∧ t ≠ 1 ∧ jInvariant t = j := by
  constructor
  · intro ht
    have ht0 := fiberRoot_ne_zero h256 ht
    have ht1 := fiberRoot_ne_one h256 ht
    refine ⟨ht0, ht1, ?_⟩
    have hd : t^2*(t-1)^2 ≠ 0 := mul_ne_zero (pow_ne_zero _ ht0)
      (pow_ne_zero _ (sub_ne_zero.mpr ht1))
    apply (div_eq_iff hd).mpr
    simp only [IsRoot, fiberPolynomial, eval_sub, eval_mul, eval_C,
      eval_pow, eval_X, eval_add, eval_one] at ht
    linear_combination ht
  · rintro ⟨ht0,ht1,hj⟩
    exact fiberPolynomial_root ht0 ht1 hj

/-- The exceptional j=1728 fiber is the square of a cubic. -/
lemma fiberPolynomial_1728 : fiberPolynomial (1728 : K) =
    C 64 * ((X+1)*(X-2)*(C 2*X-1))^2 := by
  unfold fiberPolynomial
  simp only [map_ofNat]
  ring

/-- Clearing a derivative relation eliminates j and identifies every possible
ramification parameter of the Legendre j-map. -/
lemma fiberPolynomial_derivative_relation (j : K) :
    X*(X-1)*derivative (fiberPolynomial j) -
      C 2*(C 2*X-1)*fiberPolynomial j =
    C 256*(X^2-X+1)^2*(C 2*X-1)*(X-2)*(X+1) := by
  unfold fiberPolynomial
  simp [derivative_mul, derivative_pow]
  simp only [map_ofNat]
  ring

lemma fiberPolynomial_no_repeated_root {j t : K} (h256 : (256 : K) ≠ 0)
    (hj0 : j ≠ 0) (hj1728 : j ≠ 1728) (ht : (fiberPolynomial j).IsRoot t) :
    ¬ (derivative (fiberPolynomial j)).IsRoot t := by
  intro hdt
  have ht0 := fiberRoot_ne_zero h256 ht
  have ht1 := fiberRoot_ne_one h256 ht
  have hD : t^2*(t-1)^2 ≠ 0 := mul_ne_zero (pow_ne_zero _ ht0)
    (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  have hroot := ht
  simp only [IsRoot, fiberPolynomial, eval_sub, eval_mul, eval_C,
    eval_pow, eval_X, eval_add, eval_one] at hroot
  have hq : t^2-t+1 ≠ 0 := by
    intro hq0
    have hjD : j*(t^2*(t-1)^2) = 0 := by
      rw [hq0] at hroot
      linear_combination -hroot
    exact hj0 ((mul_eq_zero.mp hjD).resolve_right hD)
  have hrel := congrArg (fun f : K[X] => f.eval t) (fiberPolynomial_derivative_relation j)
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one, eval_ofNat] at hrel
  have hft : (fiberPolynomial j).eval t = 0 := ht
  have hdf : (derivative (fiberPolynomial j)).eval t = 0 := hdt
  rw [hft,hdf] at hrel
  have hex : (2*t-1)*(t-2)*(t+1) = 0 := by
    have hprod : (256*(t^2-t+1)^2)*((2*t-1)*(t-2)*(t+1)) = 0 := by
      linear_combination -hrel
    exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero h256 (pow_ne_zero _ hq))
  have h1728 : (fiberPolynomial (1728 : K)).eval t = 0 := by
    rw [fiberPolynomial_1728]
    simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one, eval_sub, eval_ofNat]
    have heq : (t+1)*(t-2)*(2*t-1) = 0 := by linear_combination hex
    rw [heq]
    simp
  simp only [fiberPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    eval_add, eval_one] at h1728
  have hjD : (j-1728)*(t^2*(t-1)^2) = 0 := by linear_combination h1728-hroot
  exact hj1728 (sub_eq_zero.mp ((mul_eq_zero.mp hjD).resolve_right hD))

/-- Every nonexceptional j-fiber has six distinct parameters. -/
theorem fiberPolynomial_separable [IsAlgClosed K] {j : K} (h256 : (256 : K) ≠ 0)
    (hj0 : j ≠ 0) (hj1728 : j ≠ 1728) : (fiberPolynomial j).Separable := by
  change IsCoprime (fiberPolynomial j) (derivative (fiberPolynomial j))
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K]
  intro t
  by_cases ht : (fiberPolynomial j).eval t = 0
  · right
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, IsRoot] using
      fiberPolynomial_no_repeated_root h256 hj0 hj1728 ht
  · left
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using ht

theorem generic_j_fiber_card [DecidableEq K] [IsAlgClosed K] {j : K}
    (h256 : (256 : K) ≠ 0) (hj0 : j ≠ 0) (hj1728 : j ≠ 1728) :
    (fiberPolynomial j).roots.toFinset.card = 6 := by
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots
    (fiberPolynomial_separable h256 hj0 hj1728)),
    IsAlgClosed.card_roots_eq_natDegree, fiberPolynomial_natDegree j h256]

/-- The quadratic defining the j=0 Legendre parameters. -/
noncomputable def equianharmonicPolynomial : K[X] := X^2-X+1

lemma equianharmonic_ne_zero : equianharmonicPolynomial (K := K) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : K[X] => f.coeff 2) h
  simp only [equianharmonicPolynomial, coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one] at hc
  norm_num at hc

lemma equianharmonic_natDegree : (equianharmonicPolynomial (K := K)).natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold equianharmonicPolynomial; compute_degree!
  · simp only [equianharmonicPolynomial, coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
    norm_num

lemma equianharmonic_separable [IsAlgClosed K] (h3 : (3 : K) ≠ 0) :
    (equianharmonicPolynomial (K := K)).Separable := by
  change IsCoprime _ _
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K]
  intro t
  by_cases ht : t^2-t+1 = 0
  · right
    intro hd
    simp [equianharmonicPolynomial, derivative_pow] at hd
    apply h3
    linear_combination 4*ht-(2*t-1)*hd
  · left
    simpa [equianharmonicPolynomial] using ht

/-- The j=0 sextic has exactly the same distinct roots as its quadratic factor. -/
lemma zero_fiber_roots [DecidableEq K] (h256 : (256 : K) ≠ 0) :
    (fiberPolynomial (0 : K)).roots.toFinset =
      (equianharmonicPolynomial (K := K)).roots.toFinset := by
  ext t
  simp only [Multiset.mem_toFinset, mem_roots (fiberPolynomial_ne_zero 0 h256),
    mem_roots equianharmonic_ne_zero, IsRoot]
  simp [fiberPolynomial, equianharmonicPolynomial, h256]

/-- Over characteristic other than two and three, j=0 has two parameters. -/
theorem zero_j_fiber_card [DecidableEq K] [IsAlgClosed K]
    (h256 : (256 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (fiberPolynomial (0 : K)).roots.toFinset.card = 2 := by
  rw [zero_fiber_roots h256, Multiset.toFinset_card_of_nodup
    (Polynomial.nodup_roots (equianharmonic_separable h3)),
    IsAlgClosed.card_roots_eq_natDegree, equianharmonic_natDegree]

lemma twice_sub_one_eq_zero_iff {t : K} (h2 : (2 : K) ≠ 0) :
    2*t-1=0 ↔ t=(2 : K)⁻¹ := by
  constructor
  · intro h
    apply (mul_left_cancel₀ h2)
    rw [mul_inv_cancel₀ h2]
    linear_combination h
  · intro h
    rw [h, mul_inv_cancel₀ h2]
    ring

lemma exceptional_fiber_roots [DecidableEq K] (h2 : (2 : K) ≠ 0) :
    (fiberPolynomial (1728 : K)).roots.toFinset = {-1, 2, (2 : K)⁻¹} := by
  have h256 : (256 : K) ≠ 0 := by
    have h := pow_ne_zero 8 h2
    norm_num at h
    exact h
  have h64 : (64 : K) ≠ 0 := by
    have h := pow_ne_zero 6 h2
    norm_num at h
    exact h
  ext t
  rw [Multiset.mem_toFinset, mem_roots (fiberPolynomial_ne_zero 1728 h256)]
  change (fiberPolynomial (1728 : K)).eval t = 0 ↔ _
  rw [fiberPolynomial_1728]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X,
    eval_one, eval_sub, eval_ofNat, mem_insert, mem_singleton]
  simp only [mul_eq_zero, h64, false_or, pow_eq_zero_iff (by decide : 2 ≠ 0),
    add_eq_zero_iff_eq_neg, sub_eq_zero, twice_sub_one_eq_zero_iff h2]
  tauto

theorem exceptional_j_fiber_card [DecidableEq K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (fiberPolynomial (1728 : K)).roots.toFinset.card = 3 := by
  rw [exceptional_fiber_roots h2]
  have h12 : (-1 : K) ≠ 2 := by intro h; apply h3; linear_combination -h
  have h1i : (-1 : K) ≠ (2 : K)⁻¹ := by
    intro h
    have he := congrArg (fun x : K => 2*x) h
    rw [mul_inv_cancel₀ h2] at he
    apply h3
    linear_combination -he
  have h2i : (2 : K) ≠ (2 : K)⁻¹ := by
    intro h
    have he := congrArg (fun x : K => 2*x) h
    rw [mul_inv_cancel₀ h2] at he
    apply h3
    linear_combination he
  simp [h12,h1i,h2i]

end IsogenyAttack.Legendre
