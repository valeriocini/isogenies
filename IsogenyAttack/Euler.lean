import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# A finite majorant for the printed-weight Euler product

The local factor at 2 equals 2. For every integer n ≥ 3 its factor is bounded
by `(n-1)^2 / (n*(n-2))`. The product of these latter factors telescopes;
comparison with all integers, rather than just primes, bounds every finite
Euler product by 4. The final lemma sums the local geometric series exactly.
-/

namespace IsogenyAttack

noncomputable def eulerFactor (n : ℕ) : ℝ :=
  1 + 1 / ((n : ℝ)^2 - n - 1)

noncomputable def telescopingFactor (n : ℕ) : ℝ :=
  ((n : ℝ) - 1)^2 / ((n : ℝ) * (n - 2))

lemma eulerFactor_two : eulerFactor 2 = 2 := by
  norm_num [eulerFactor]

lemma eulerFactor_one_le {n : ℕ} (hn : 2 ≤ n) : 1 ≤ eulerFactor n := by
  have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ)^2 - n - 1 := by nlinarith
  simp only [eulerFactor]
  exact le_add_of_nonneg_right (by positivity)

lemma eulerFactor_le_telescoping {n : ℕ} (hn : 3 ≤ n) :
    eulerFactor n ≤ telescopingFactor n := by
  have h : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ)^2 - n - 1 := by nlinarith
  have ht : 0 < (n : ℝ) * (n - 2) := by nlinarith
  unfold eulerFactor telescopingFactor
  have he : 1 + 1 / ((n : ℝ)^2 - n - 1) =
      ((n : ℝ)^2 - n) / ((n : ℝ)^2 - n - 1) := by
    apply (eq_div_iff hd.ne').2
    rw [add_mul, one_mul, div_mul_cancel₀ _ hd.ne']
    ring
  rw [he, div_le_div_iff₀ hd ht]
  nlinarith

lemma eulerProduct_range_le (N : ℕ) :
    (∏ i ∈ Finset.range (N+1), eulerFactor (i+2)) ≤
      4 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := by
  induction N with
  | zero => norm_num [eulerFactor]
  | succ N ih =>
    rw [Finset.prod_range_succ]
    have h0 := eulerFactor_one_le (n := N+1+2) (by omega)
    have he := eulerFactor_le_telescoping (n := N+1+2) (by omega)
    have hpos : 0 ≤ 4 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := by positivity
    calc
      _ ≤ (4 * ((N : ℝ) + 1) / ((N : ℝ) + 2)) * eulerFactor (N+1+2) :=
        mul_le_mul_of_nonneg_right ih (by linarith)
      _ ≤ (4 * ((N : ℝ) + 1) / ((N : ℝ) + 2)) * telescopingFactor (N+1+2) :=
        mul_le_mul_of_nonneg_left he hpos
      _ = _ := by
        unfold telescopingFactor
        push_cast
        field_simp
        ring

lemma eulerProduct_range_le_four (N : ℕ) :
    (∏ i ∈ Finset.range (N+1), eulerFactor (i+2)) ≤ 4 := by
  apply (eulerProduct_range_le N).trans
  apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) + 2)).2
  nlinarith

/-- Uniform bound for every finite subproduct; primality is not needed. -/
lemma eulerProduct_finset_le_four (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    (∏ p ∈ P, eulerFactor p) ≤ 4 := by
  let N := P.sup id
  have hsub : P ⊆ Finset.Ico 2 (N+3) := by
    intro p hp
    have hpN : p ≤ N := Finset.le_sup (f := id) hp
    exact Finset.mem_Ico.mpr ⟨hP p hp, by omega⟩
  calc
    _ ≤ ∏ p ∈ Finset.Ico 2 (N+3), eulerFactor p := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      · intro p hp
        exact le_trans (by norm_num) (eulerFactor_one_le (hP p hp))
      · intro p hp _
        exact eulerFactor_one_le (Finset.mem_Ico.mp hp).1
    _ ≤ 4 := by
      rw [Finset.prod_Ico_eq_prod_range]
      simpa [Nat.add_sub_cancel, add_comm] using eulerProduct_range_le_four N

lemma eulerProduct_primes_le_four (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, eulerFactor p) ≤ 4 :=
  eulerProduct_finset_le_four P (fun p hp => (hP p hp).two_le)

noncomputable def primePowerTerm (p a : ℕ) : ℝ :=
  if a = 0 then 1 else ((p : ℝ)+1)^(a-1) / (p : ℝ)^(2*a)

/-- Local Dirichlet series for the convolution factor, including exponent zero. -/
lemma hasSum_primePowerTerm {p : ℕ} (hp : 2 ≤ p) :
    HasSum (primePowerTerm p) (eulerFactor p) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp2 : 0 < (p : ℝ)^2 := by positivity
  have hr0 : 0 ≤ ((p : ℝ)+1) / (p : ℝ)^2 := by positivity
  have hr1 : ((p : ℝ)+1) / (p : ℝ)^2 < 1 := by
    apply (div_lt_one hp2).2
    nlinarith
  have hgeo := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 / (p : ℝ)^2)
  have htail : HasSum (fun a => primePowerTerm p (a+1))
      (1 / ((p : ℝ)^2 - p - 1)) := by
    convert hgeo using 1
    · funext a
      simp only [primePowerTerm, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte, Nat.add_sub_cancel]
      rw [div_pow, mul_add, mul_one, pow_add, pow_mul]
      field_simp
    · have hd : (p : ℝ)^2 - p - 1 ≠ 0 := by nlinarith
      field_simp
      ring
  apply (hasSum_nat_add_iff' 1).mp
  simpa [primePowerTerm, eulerFactor] using htail

end IsogenyAttack
