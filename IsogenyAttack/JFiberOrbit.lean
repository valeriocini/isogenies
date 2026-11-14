import IsogenyAttack.JFibers
import IsogenyAttack.HasseSymmetry

/-! The full Legendre j-fiber is the six anharmonic transforms; in particular
Hasse vanishing is invariant on nonsingular Legendre representatives of a j-class. -/
namespace IsogenyAttack.Legendre
open Polynomial
variable {K : Type*} [Field K]

/-- The exact factorization of a denominator-cleared fiber equation. -/
lemma j_cross_factorization (a t : K) :
    a^2*(a-1)^2*(t^2-t+1)^3 - (a^2-a+1)^3*t^2*(t-1)^2 =
      (t-a)*(t+a-1)*(a*t-1)*((a-1)*t+1)*(a*t-a+1)*((a-1)*t-a) := by ring

/-- Equality of j-invariants forces one of the six classical transforms.
The statement remains valid at exceptional j-values, where some coincide. -/
theorem same_j_six {a t : K} (h256 : (256 : K) ≠ 0)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hj : jInvariant t = jInvariant a) :
    t=a ∨ t=1-a ∨ t=a⁻¹ ∨ t=(1-a)⁻¹ ∨ t=(a-1)/a ∨ t=a/(a-1) := by
  have hDa : a^2*(a-1)^2 ≠ 0 := mul_ne_zero (pow_ne_zero _ ha0)
    (pow_ne_zero _ (sub_ne_zero.mpr ha1))
  have hDt : t^2*(t-1)^2 ≠ 0 := mul_ne_zero (pow_ne_zero _ ht0)
    (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  have hcross := (div_eq_div_iff hDt hDa).mp hj
  have hpoly : a^2*(a-1)^2*(t^2-t+1)^3 - (a^2-a+1)^3*t^2*(t-1)^2 = 0 := by
    apply (mul_eq_zero.mp (show 256 *
      (a^2*(a-1)^2*(t^2-t+1)^3 - (a^2-a+1)^3*t^2*(t-1)^2) = 0 by
        linear_combination hcross)).resolve_left h256
  rw [j_cross_factorization] at hpoly
  simp only [mul_eq_zero, or_assoc] at hpoly
  rcases hpoly with h | h | h | h | h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right; left
    linear_combination h
  · right; right; left
    apply mul_left_cancel₀ ha0
    rw [mul_inv_cancel₀ ha0]
    linear_combination h
  · right; right; right; left
    have h1a : 1-a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
    apply mul_left_cancel₀ h1a
    rw [mul_inv_cancel₀ h1a]
    linear_combination -h
  · right; right; right; right; left
    apply (eq_div_iff ha0).mpr
    linear_combination h
  · right; right; right; right; right
    apply (eq_div_iff (sub_ne_zero.mpr ha1)).mpr
    linear_combination h

/-- Hasse vanishing depends only on j among nonsingular Legendre curves. -/
theorem same_j_hasse_root (p : ℕ) [CharP K p] [Fact p.Prime]
    {n : ℕ} (hp : p=2*n+1) {a t : K} (h256 : (256 : K) ≠ 0)
    (ha : (hassePolynomial (K := K) n).IsRoot a)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hj : jInvariant t = jInvariant a) :
    (hassePolynomial (K := K) n).IsRoot t := by
  have ha0 : a ≠ 0 := by intro h; simp [h, IsRoot] at ha
  have ha1 : a ≠ 1 := by
    intro h
    have heval : (hassePolynomial (K := K) n).eval 1 = 0 := by simpa [h, IsRoot] using ha
    rw [hassePolynomial_eval_one_sign p hp] at heval
    exact (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) heval
  obtain ⟨hr, hi, hir, hlast, hpenult⟩ := hasse_root_anharmonic_orbit p hp ha
  rcases same_j_six h256 ha0 ha1 ht0 ht1 hj with h | h | h | h | h | h
  · exact h.symm ▸ ha
  · exact h.symm ▸ hr
  · exact h.symm ▸ hi
  · exact h.symm ▸ hir
  · exact h.symm ▸ hpenult
  · exact h.symm ▸ hlast

/-- For a j-class represented by a Hasse root, every root of its sextic fiber
is again a Hasse root; this proves the set equality used in the exact mass law. -/
theorem fiber_root_is_hasse_root (p : ℕ) [CharP K p] [Fact p.Prime]
    {n : ℕ} (hp : p=2*n+1) {a t : K} (h256 : (256 : K) ≠ 0)
    (ha : (hassePolynomial (K := K) n).IsRoot a)
    (ht : (fiberPolynomial (jInvariant a)).IsRoot t) :
    (hassePolynomial (K := K) n).IsRoot t := by
  obtain ⟨ht0,ht1,hj⟩ := (fiberPolynomial_isRoot_iff h256).mp ht
  exact same_j_hasse_root p hp h256 ha ht0 ht1 hj

end IsogenyAttack.Legendre
