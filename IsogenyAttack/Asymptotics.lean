import IsogenyAttack.Bounds

namespace IsogenyAttack

/-- A standard eventual inverse-polynomial definition of negligibility.
Using n+1 avoids a special convention at the security parameter zero. -/
def IsNegligible (a : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, |a n| ≤ 1 / ((n : ℝ) + 1) ^ k

/-- The explicit bound supplied by the attack is non-negligible.
The eventual index allows arbitrary behavior at the finitely many small
parameters where the cutoff hypotheses have not yet started to hold. -/
theorem not_negligible_of_attack_bound {a : ℕ → ℝ}
    (h : ∃ N : ℕ, ∀ n ≥ N,
      1 / (1024 * ((n : ℝ) + 784) ^ 3) ≤ a n) : ¬ IsNegligible a := by
  intro hneg
  obtain ⟨N, hN⟩ := h
  obtain ⟨N', hN'⟩ := hneg 4
  let C : ℕ := 1024 * 784 ^ 3
  let n : ℕ := max N N' + C
  have hn : N ≤ n := by dsimp [n]; omega
  have hn' : N' ≤ n := by dsimp [n]; omega
  have hC : (0 : ℝ) < C := by norm_num [C]
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hshift : (n : ℝ) + 784 ≤ 784 * ((n : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hcube := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ n + 784) hshift 3
  have hden : 1024 * ((n : ℝ) + 784) ^ 3 ≤ (C : ℝ) * ((n : ℝ) + 1) ^ 3 := by
    dsimp [C]
    nlinarith
  have hlower : 1 / ((C : ℝ) * ((n : ℝ) + 1) ^ 3) ≤ |a n| :=
    (one_div_le_one_div_of_le (by positivity) hden).trans
      ((hN n hn).trans (le_abs_self _))
  have hboth := hlower.trans (hN' n hn')
  have hprod : ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) ≤
      ((n : ℝ) + 1) ^ 3 * (C : ℝ) := by
    have hcross := (div_le_div_iff₀ (mul_pos hC (pow_pos hx 3)) (pow_pos hx 4)).mp hboth
    nlinarith
  have hxc := (mul_le_mul_iff_right₀ (pow_pos hx 3)).mp hprod
  have hnat : C ≤ n := by dsimp [n]; omega
  have hreal : (C : ℝ) ≤ n := by exact_mod_cast hnat
  linarith

end IsogenyAttack
