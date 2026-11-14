import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! The response-degree cutoff in the source: the least power of two at least `√p`.
Its integer formulation avoids any numerical approximation to logarithms. -/
namespace IsogenyAttack.ResponseCutoff

/-- The least exponent `e` such that `p ≤ 4^e`. -/
def exponent (p : ℕ) : ℕ := Nat.clog 4 p

/-- The least power of two whose square is at least `p`. -/
def bound (p : ℕ) : ℕ := 2 ^ exponent p

theorem exponent_le_iff (p e : ℕ) : exponent p ≤ e ↔ p ≤ 4^e :=
  Nat.clog_le_iff_le_pow (by decide)

theorem bound_sq (p : ℕ) : (bound p)^2 = 4^exponent p := by
  unfold bound
  rw [← pow_mul, mul_comm (exponent p) 2, pow_mul]
  norm_num

theorem prime_le_bound_sq (p : ℕ) : p ≤ (bound p)^2 := by
  rw [bound_sq]
  exact Nat.le_pow_clog (by decide) p

theorem prime_lt_bound_sq (p : ℕ) (hp : p.Prime) (hp4 : 4 < p) :
    p < (bound p)^2 := by
  apply lt_of_le_of_ne (prime_le_bound_sq p)
  intro he
  rw [bound_sq] at he
  have h := (hp.pow_eq_iff).mp he.symm
  omega

theorem bound_sq_lt_four_mul (p : ℕ) (hp : 1 < p) :
    (bound p)^2 < 4*p := by
  rw [bound_sq]
  have he : 0 < exponent p := Nat.clog_pos (by decide) hp
  have hpred : 4^(exponent p - 1) < p := Nat.pow_pred_clog_lt_self (by decide) hp
  have heq : exponent p = (exponent p - 1) + 1 := by omega
  calc
    4^exponent p = 4 * 4^(exponent p - 1) := by
      conv_lhs => rw [heq]
      rw [pow_succ, mul_comm]
    _ < 4*p := by omega

theorem bound_lt_prime (p : ℕ) (hp : 4 < p) : bound p < p := by
  have h := bound_sq_lt_four_mul p (by omega)
  nlinarith

/-- Exactly the strict cutoff inequality used in the attack certificate. -/
theorem bound_sq_lt_four_mul_real (p : ℕ) (hp : 1 < p) :
    (bound p : ℝ)^2 < 4*(p : ℝ) := by
  exact_mod_cast bound_sq_lt_four_mul p hp

theorem bounds (p : ℕ) (hp : p.Prime) (hp4 : 4 < p) :
    p < (bound p)^2 ∧ (bound p)^2 < 4*p ∧ bound p < p :=
  ⟨prime_lt_bound_sq p hp hp4, bound_sq_lt_four_mul p (by omega), bound_lt_prime p hp4⟩

/-- The integer definition is exactly the logarithmic cutoff printed in the source. -/
theorem bound_eq_logarithmic (p : ℕ) (hp : 0 < p) :
    bound p = 2 ^ ⌈Real.logb 2 (Real.sqrt p)⌉₊ := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hl : Real.logb 2 (Real.sqrt p) = Real.logb 4 p := by
    rw [Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hpR]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 2
      norm_num at h ⊢
      exact h
    simp only [Real.logb, h4]
    ring
  rw [hl, show ⌈Real.logb 4 (p : ℝ)⌉₊ = Nat.clog 4 p from
    Real.natCeil_logb_natCast 4 p]
  rfl

theorem bound_pos (p : ℕ) : 0 < bound p := pow_pos (by decide) _

/-- A simple polynomial lower bound on the characteristic suffices for the threshold
used with security parameter `n+784`. -/
theorem threshold_growth (p n : ℕ) (hp : 64*(n+784)^4 ≤ p) :
    8*(n+784)^2 ≤ bound p := by
  have h := prime_le_bound_sq p
  have he : (8*(n+784)^2)^2 = 64*(n+784)^4 := by ring
  rw [← he] at hp
  nlinarith

theorem polynomial_le_exponential (n : ℕ) (hn : 64 ≤ n) :
    64*(n+784)^4 ≤ 2^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hstep : (n+1+784)^4 ≤ 2*(n+784)^4 := by
      nlinarith only [Nat.zero_le n, Nat.zero_le (n^2), Nat.zero_le (n^3),
        Nat.zero_le (n^4)]
    calc
      64*(n+1+784)^4 ≤ 2*(64*(n+784)^4) := by omega
      _ ≤ 2*2^n := Nat.mul_le_mul_left 2 ih
      _ = 2^(n+1) := by rw [pow_succ, mul_comm]

/-- Exponential characteristic growth supplies both quantitative hypotheses of the
eventual attack theorem, with an explicit starting index. -/
theorem eventual_parameters (p : ℕ → ℕ) (hp : ∀ n, 2^n ≤ p n) :
    ∃ N : ℕ, ∀ n ≥ N,
      8*(n+784)^2 ≤ bound (p n) ∧ (bound (p n) : ℝ)^2 < 4*(p n : ℝ) := by
  refine ⟨64, fun n hn => ?_⟩
  have hg := (polynomial_le_exponential n hn).trans (hp n)
  refine ⟨threshold_growth (p n) n hg, bound_sq_lt_four_mul_real (p n) ?_⟩
  nlinarith [Nat.zero_le n, Nat.zero_le (n^2), Nat.zero_le (n^3), Nat.zero_le (n^4)]

end IsogenyAttack.ResponseCutoff
