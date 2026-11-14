import IsogenyAttack.CurveAutomorphisms
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Actual Montgomery equations and exact fibers of their j-invariant. -/
namespace IsogenyAttack.Montgomery
open Polynomial Finset
variable {K : Type*} [Field K]

def curve (A : K) : WeierstrassCurve K := ⟨0,A,0,1,0⟩

@[simp] theorem curve_c4 (A : K) : (curve A).c₄ = 16*(A^2-3) := by
  simp only [curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

@[simp] theorem curve_discriminant (A : K) : (curve A).Δ = 16*(A^2-4) := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem curve_isElliptic {A : K} (h2 : (2 : K) ≠ 0) (hA : A^2 ≠ 4) :
    (curve A).IsElliptic := by
  constructor
  rw [curve_discriminant]
  apply isUnit_iff_ne_zero.mpr
  have h16 : (16 : K) ≠ 0 := by convert pow_ne_zero 4 h2 using 1; norm_num
  exact mul_ne_zero h16 (sub_ne_zero.mpr hA)

noncomputable def jInvariant (A : K) := 256*(A^2-3)^3/(A^2-4)

theorem curve_jInvariant (A : K) [(curve A).IsElliptic] : (curve A).j = jInvariant A := by
  have hΔ := (curve A).isUnit_Δ.ne_zero
  rw [curve_discriminant] at hΔ
  have h16 := left_ne_zero_of_mul hΔ
  have hA := right_ne_zero_of_mul hΔ
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    curve_discriminant, curve_c4]
  unfold jInvariant
  field_simp
  ring

noncomputable def fiberPolynomial (j : K) : K[X] := C 256*(X^2-C 3)^3-C j*(X^2-C 4)

lemma fiberPolynomial_natDegree (j : K) (h256 : (256 : K) ≠ 0) :
    (fiberPolynomial j).natDegree = 6 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold fiberPolynomial; compute_degree!
  · have he : fiberPolynomial j = C 256*X^6-C 2304*X^4+C (6912-j)*X^2+C (4*j-6912) := by
      unfold fiberPolynomial
      simp only [map_sub, map_mul, map_ofNat]
      ring
    rw [he]
    norm_num only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C]
    simpa using h256

lemma fiberPolynomial_ne_zero (j : K) (h256 : (256 : K) ≠ 0) :
    fiberPolynomial j ≠ 0 := by
  intro h
  have hd := fiberPolynomial_natDegree j h256
  rw [h, natDegree_zero] at hd
  omega

lemma fiberRoot_nonsingular {j A : K} (h256 : (256 : K) ≠ 0)
    (ht : (fiberPolynomial j).IsRoot A) : A^2 ≠ 4 := by
  intro hA
  norm_num [fiberPolynomial, IsRoot, hA, h256] at ht

lemma fiberPolynomial_isRoot_iff {j A : K} (h256 : (256 : K) ≠ 0) :
    (fiberPolynomial j).IsRoot A ↔ A^2 ≠ 4 ∧ jInvariant A = j := by
  constructor
  · intro ht
    have hn := fiberRoot_nonsingular h256 ht
    refine ⟨hn, ?_⟩
    apply (div_eq_iff (sub_ne_zero.mpr hn)).mpr
    simp only [IsRoot, fiberPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X] at ht
    linear_combination ht
  · rintro ⟨hn,hj⟩
    have he := (div_eq_iff (sub_ne_zero.mpr hn)).mp hj
    simp only [IsRoot, fiberPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination he

lemma fiberPolynomial_1728 : fiberPolynomial (1728 : K) =
    C 64*(X*(C 2*X^2-C 9))^2 := by
  unfold fiberPolynomial
  simp only [map_ofNat]
  ring

lemma fiberPolynomial_derivative_relation (j : K) :
    (X^2-C 4)*derivative (fiberPolynomial j)-C 2*X*fiberPolynomial j =
      C 512*X*(X^2-C 3)^2*(C 2*X^2-C 9) := by
  unfold fiberPolynomial
  simp [derivative_mul, derivative_pow]
  simp only [map_ofNat]
  ring

lemma fiberPolynomial_no_repeated_root {j A : K} (h2 : (2 : K) ≠ 0)
    (hj0 : j ≠ 0) (hj1728 : j ≠ 1728) (ht : (fiberPolynomial j).IsRoot A) :
    ¬ (derivative (fiberPolynomial j)).IsRoot A := by
  have h256 : (256 : K) ≠ 0 := by convert pow_ne_zero 8 h2 using 1; norm_num
  have h512 : (512 : K) ≠ 0 := by convert pow_ne_zero 9 h2 using 1; norm_num
  intro hdt
  have hA : A^2-4 ≠ 0 := sub_ne_zero.mpr (fiberRoot_nonsingular h256 ht)
  have hroot := ht
  simp only [IsRoot, fiberPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hroot
  have hq : A^2-3 ≠ 0 := by
    intro hq0
    have hz : j*(A^2-4)=0 := by rw [hq0] at hroot; linear_combination -hroot
    exact hj0 ((mul_eq_zero.mp hz).resolve_right hA)
  have hr := congrArg (fun f : K[X] => f.eval A) (fiberPolynomial_derivative_relation j)
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hr
  have hft : (fiberPolynomial j).eval A = 0 := ht
  have hdf : (derivative (fiberPolynomial j)).eval A = 0 := hdt
  rw [hft,hdf] at hr
  have hex : A*(2*A^2-9)=0 := by
    have hz : (512*(A^2-3)^2)*(A*(2*A^2-9))=0 := by linear_combination -hr
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h512 (pow_ne_zero _ hq))
  have h1728 : (fiberPolynomial (1728 : K)).eval A = 0 := by
    rw [fiberPolynomial_1728]
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub]
    rw [hex]
    simp
  simp only [fiberPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X] at h1728
  have hz : (j-1728)*(A^2-4)=0 := by linear_combination h1728-hroot
  exact hj1728 (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hA))

lemma fiberPolynomial_separable [IsAlgClosed K] {j : K}
    (h2 : (2 : K) ≠ 0) (hj0 : j ≠ 0) (hj1728 : j ≠ 1728) :
    (fiberPolynomial j).Separable := by
  change IsCoprime _ _
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K]
  intro A
  by_cases ht : (fiberPolynomial j).eval A = 0
  · right
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, IsRoot] using
      fiberPolynomial_no_repeated_root h2 hj0 hj1728 ht
  · left
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using ht

theorem generic_j_fiber_card [DecidableEq K] [IsAlgClosed K] {j : K}
    (h2 : (2 : K) ≠ 0) (hj0 : j ≠ 0) (hj1728 : j ≠ 1728) :
    (fiberPolynomial j).roots.toFinset.card = 6 := by
  have h256 : (256 : K) ≠ 0 := by convert pow_ne_zero 8 h2 using 1; norm_num
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots
    (fiberPolynomial_separable h2 hj0 hj1728)),
    IsAlgClosed.card_roots_eq_natDegree, fiberPolynomial_natDegree j h256]

noncomputable def zeroFiberFactor : K[X] := X^2-C 3
noncomputable def exceptionalFiberFactor : K[X] := X*(C 2*X^2-C 9)

lemma zeroFiberFactor_natDegree : (zeroFiberFactor (K := K)).natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold zeroFiberFactor; compute_degree!
  · simp [zeroFiberFactor]
lemma exceptionalFiberFactor_natDegree (h2 : (2 : K) ≠ 0) :
    (exceptionalFiberFactor (K := K)).natDegree = 3 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold exceptionalFiberFactor; compute_degree!
  · simp [exceptionalFiberFactor, h2]

lemma zeroFiberFactor_separable [IsAlgClosed K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (zeroFiberFactor (K := K)).Separable := by
  change IsCoprime _ _
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K]
  intro A
  by_cases ht : A^2-3=0
  · right
    intro hd
    simp [zeroFiberFactor, derivative_pow, h2] at hd
    rw [hd] at ht
    simp [h3] at ht
  · left
    simpa [zeroFiberFactor] using ht

lemma exceptionalFiberFactor_separable [IsAlgClosed K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (exceptionalFiberFactor (K := K)).Separable := by
  have h9 : (9 : K) ≠ 0 := by convert pow_ne_zero 2 h3 using 1; norm_num
  have h18 : (18 : K) ≠ 0 := by convert mul_ne_zero h2 h9 using 1; norm_num
  change IsCoprime _ _
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K]
  intro A
  by_cases ht : A*(2*A^2-9)=0
  · right
    intro hd
    simp [exceptionalFiberFactor, derivative_mul, derivative_pow] at hd
    rcases mul_eq_zero.mp ht with hA | hA
    · rw [hA] at hd
      simp [h9] at hd
    · apply h18
      linear_combination hd-3*hA
  · left
    simpa [exceptionalFiberFactor] using ht

theorem zero_j_fiber_card [DecidableEq K] [IsAlgClosed K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (fiberPolynomial (0 : K)).roots.toFinset.card = 2 := by
  have h256 : (256 : K) ≠ 0 := by convert pow_ne_zero 8 h2 using 1; norm_num
  have hq : zeroFiberFactor (K := K) ≠ 0 := by
    intro h; have hd := zeroFiberFactor_natDegree (K := K); rw [h, natDegree_zero] at hd; omega
  have hr : (fiberPolynomial (0 : K)).roots.toFinset =
      (zeroFiberFactor (K := K)).roots.toFinset := by
    ext A
    simp only [Multiset.mem_toFinset, mem_roots (fiberPolynomial_ne_zero 0 h256),
      mem_roots hq, IsRoot]
    simp [fiberPolynomial, zeroFiberFactor, h256]
  rw [hr, Multiset.toFinset_card_of_nodup (nodup_roots (zeroFiberFactor_separable h2 h3)),
    IsAlgClosed.card_roots_eq_natDegree, zeroFiberFactor_natDegree]

theorem exceptional_j_fiber_card [DecidableEq K] [IsAlgClosed K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (fiberPolynomial (1728 : K)).roots.toFinset.card = 3 := by
  have h256 : (256 : K) ≠ 0 := by convert pow_ne_zero 8 h2 using 1; norm_num
  have h64 : (64 : K) ≠ 0 := by convert pow_ne_zero 6 h2 using 1; norm_num
  have hq : exceptionalFiberFactor (K := K) ≠ 0 := by
    intro h; have hd := exceptionalFiberFactor_natDegree h2; rw [h, natDegree_zero] at hd; omega
  have hr : (fiberPolynomial (1728 : K)).roots.toFinset =
      (exceptionalFiberFactor (K := K)).roots.toFinset := by
    ext A
    simp only [Multiset.mem_toFinset, mem_roots (fiberPolynomial_ne_zero 1728 h256),
      mem_roots hq, IsRoot]
    rw [fiberPolynomial_1728]
    simp [exceptionalFiberFactor, h64, mul_eq_zero]
  rw [hr, Multiset.toFinset_card_of_nodup (nodup_roots (exceptionalFiberFactor_separable h2 h3)),
    IsAlgClosed.card_roots_eq_natDegree, exceptionalFiberFactor_natDegree h2]

end IsogenyAttack.Montgomery
