import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Explicit finite constants for the short-component distinguisher. All divisions in
probability bounds are real; `threshold` uses natural-number floor division.
-/
namespace IsogenyAttack

/-- The public test threshold. -/
def threshold (B s : ℕ) : ℕ := B / (4 * s ^ 2)

/-- The cutoff and target mass hypotheses turn the target-support count into
an upper bound with an absolute constant. -/
theorem target_constant {p B L S : ℝ}
    (hp : 49 ≤ p) (hB : 0 < B) (hcut : B ^ 2 < 4 * p)
    (hS : S ≤ 12 * L ^ 2 / (p - 1)) :
    S ≤ 49 * L ^ 2 / B ^ 2 := by
  have hp1 : 0 < p - 1 := by linarith
  have hb2 : 0 < B ^ 2 := sq_pos_of_pos hB
  apply hS.trans
  apply (div_le_div_iff₀ hp1 hb2).2
  have hcoef : 12 * B ^ 2 ≤ 49 * (p - 1) := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hcoef)]

/-- Finite event-probability gap, before selecting the threshold. -/
theorem finite_gap {p B L M U S : ℝ}
    (hp : 49 ≤ p) (hB : 0 < B) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hcut : B ^ 2 < 4 * p)
    (hU : M * L * (L + 1) / (8 * B ^ 2) ≤ U)
    (hS : S ≤ 12 * L ^ 2 / (p - 1)) :
    (M / 8 - 49) * L ^ 2 / B ^ 2 ≤ U - S := by
  have ht := target_constant hp hB hcut hS
  have hb2 : 0 < B ^ 2 := sq_pos_of_pos hB
  have hlo : M * L ^ 2 / (8 * B ^ 2) ≤ U := by
    apply le_trans _ hU
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 8 * B ^ 2)).2
    nlinarith [mul_nonneg hM hL]
  have heq : (M / 8 - 49) * L ^ 2 / B ^ 2 =
      M * L ^ 2 / (8 * B ^ 2) - 49 * L ^ 2 / B ^ 2 := by ring
  rw [heq]
  linarith

/-- Natural division supplies both the safe original-degree bound and the
factor-two lower bound for the threshold. -/
theorem threshold_bounds {B s : ℕ} (hs : 1 ≤ s) (hB : 8 * s ^ 2 ≤ B) :
    1 ≤ threshold B s ∧ s ^ 2 * threshold B s < B ∧
      (B : ℝ) / (8 * (s : ℝ) ^ 2) ≤ (threshold B s : ℝ) := by
  have hspos : 0 < s := by omega
  have hd : 0 < 4 * s ^ 2 := by positivity
  have hdB : 4 * s ^ 2 ≤ B := by omega
  have hL : 1 ≤ B / (4 * s ^ 2) := (Nat.le_div_iff_mul_le hd).2 (by simpa)
  have hup := Nat.div_mul_le_self B (4 * s ^ 2)
  have hlo := Nat.lt_mul_div_succ B hd
  have hmul : s ^ 2 * (B / (4 * s ^ 2)) < B := by
    have hx : 0 < s ^ 2 * (B / (4 * s ^ 2)) := Nat.mul_pos (by positivity) hL
    nlinarith
  have hnat : B ≤ 8 * s ^ 2 * (B / (4 * s ^ 2)) := by nlinarith
  refine ⟨hL, hmul, ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < (8 : ℝ) * s ^ 2)).2
  exact_mod_cast (show B ≤ B / (4 * s ^ 2) * (8 * s ^ 2) by nlinarith [hnat])

/-- Explicit inverse-cubic gap, using only finite inequalities. -/
theorem inverse_cubic_gap {p B : ℝ} {s : ℕ} {L U S : ℝ}
    (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 0 < B)
    (hcut : B ^ 2 < 4 * p) (hL : B / (8 * (s : ℝ) ^ 2) ≤ L)
    (hU : (s : ℝ) * L * (L + 1) / (8 * B ^ 2) ≤ U)
    (hS : S ≤ 12 * L ^ 2 / (p - 1)) :
    1 / (1024 * (s : ℝ) ^ 3) ≤ U - S := by
  have hsR : (784 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hLpos : 0 ≤ L := (le_of_lt (by positivity : 0 < B / (8 * (s : ℝ) ^ 2))).trans hL
  have hg := finite_gap hp hB hLpos (le_of_lt hspos) hcut hU hS
  apply le_trans _ hg
  have hcoef : (s : ℝ) / 16 ≤ (s : ℝ) / 8 - 49 := by linarith
  have hsquare : (B / (8 * (s : ℝ) ^ 2)) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (by positivity) hL 2
  have hprod : (s : ℝ) / 16 * (B / (8 * (s : ℝ) ^ 2)) ^ 2 ≤
      ((s : ℝ) / 8 - 49) * L ^ 2 := by
    calc
      _ ≤ (s : ℝ) / 16 * L ^ 2 := mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg L)
  have hb0 : B ≠ 0 := ne_of_gt hB
  have hs0 : (s : ℝ) ≠ 0 := ne_of_gt hspos
  have heq : (s : ℝ) / 16 * (B / (8 * (s : ℝ) ^ 2)) ^ 2 / B ^ 2 =
      1 / (1024 * (s : ℝ) ^ 3) := by field_simp; ring
  rw [← heq]
  exact div_le_div_of_nonneg_right hprod (sq_nonneg B)

end IsogenyAttack
