import IsogenyAttack.TargetSampler

/-!
The fixed-source attack lifts to a random public key/challenge by averaging its
SIGNED gap. Averaging only absolute gaps would be incorrect. This module proves
the exact finite-experiment identities independently of any geometric model.
-/
namespace IsogenyAttack
namespace FiniteLaw
open scoped BigOperators

/-- Acceptance in a two-stage finite experiment is the weighted sum of
conditional acceptance probabilities. -/
theorem dependentBind_eventMass {ι : Type*} [Fintype ι]
    (P : FiniteLaw ι) (α : ι → Type*) [∀ i, Fintype (α i)]
    (Q : ∀ i, FiniteLaw (α i)) (E : (Sigma α) → Prop) :
    (P.dependentBind α Q).eventMass E =
      ∑ i, P.mass i * (Q i).eventMass (fun x => E ⟨i,x⟩) := by
  classical
  rw [eventMass_eq_sum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [eventMass_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E ⟨i,x⟩ <;> simp [dependentBind, h]

/-- A uniform lower bound on signed conditional gaps survives arbitrary
common randomization of the public context. -/
theorem dependentBind_signed_gap {ι : Type*} [Fintype ι]
    (P : FiniteLaw ι) (α β : ι → Type*)
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (U : ∀ i, FiniteLaw (α i)) (S : ∀ i, FiniteLaw (β i))
    (EU : (Sigma α) → Prop) (ES : (Sigma β) → Prop) (δ : ℝ)
    (h : ∀ i, δ ≤ (U i).eventMass (fun x => EU ⟨i,x⟩) -
      (S i).eventMass (fun x => ES ⟨i,x⟩)) :
    δ ≤ (P.dependentBind α U).eventMass EU -
      (P.dependentBind β S).eventMass ES := by
  rw [dependentBind_eventMass, dependentBind_eventMass, ← Finset.sum_sub_distrib]
  calc
    δ = ∑ i, P.mass i * δ := by rw [← Finset.sum_mul, P.mass_sum, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_sub] using mul_le_mul_of_nonneg_left (h i) (P.mass_nonneg i)

end FiniteLaw

/-- The stronger signed form of the previous certificate. The public context
can later be randomized without losing the lower bound. -/
theorem attack_correct_signed {α τ : Type*} [Fintype α] [Fintype τ]
    {B s : ℕ} (S : FiniteLaw α)
    (target : α → τ) (codomain : HNF → τ)
    (componentS : α → Option HNF) (observedU : BoundedKernel B → Option ℕ)
    (p : ℝ) (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * p)
    (htarget : ∀ x k, componentS x = some k → target x = codomain k)
    (hpoint : ∀ t, S.eventMass (fun x => target x = t) ≤ 12 / (p - 1))
    (hobserved : ∀ k : BoundedKernel B, k.val.degree < B →
      observedU k = some k.val.cyclicDegree) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      (printedLaw B (cutoff_positive hs hB)).eventMass
          (fun k => publicTest B s (observedU k) = true) -
        S.eventMass (fun x => publicTest B s ((componentS x).map HNF.degree) = true) := by
  have hBpos := cutoff_positive hs hB
  obtain ⟨_, hinterior, hfloor⟩ := threshold_bounds (by omega : 1 ≤ s) hB
  apply inverse_cubic_gap hs hp (by exact_mod_cast hBpos) hcut hfloor
  · apply degree_first_publicTest_lower _ observedU (normalizer B) hBpos
      (normalizer_pos hBpos) (normalizer_le_four_mul_square B) hinterior hobserved
    intro k _
    exact printedLaw_mass B hBpos k
  · apply target_first_upper S _ target codomain p _ (by linarith) _ hpoint
    intro x hx
    cases hc : componentS x with
    | none => simp [hc] at hx
    | some k =>
      refine ⟨k, ?_, htarget x k hc⟩
      simpa [hc] using hx

/-- Explicit public-key/challenge averaging of the attack. No independence
between the sampled public context and its simulated hint is assumed. -/
theorem randomized_context_attack {ι α τ : Type*}
    [Fintype ι] [Fintype α] [Fintype τ] {B s : ℕ}
    (P : FiniteLaw ι) (S : ι → FiniteLaw α)
    (target : ι → α → τ) (codomain : ι → HNF → τ)
    (componentS : ι → α → Option HNF)
    (observedU : ι → BoundedKernel B → Option ℕ)
    (p : ℝ) (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * p)
    (htarget : ∀ i x k, componentS i x = some k → target i x = codomain i k)
    (hpoint : ∀ i t, (S i).eventMass (fun x => target i x = t) ≤ 12 / (p - 1))
    (hobserved : ∀ i k, k.val.degree < B →
      observedU i k = some k.val.cyclicDegree) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      (P.dependentBind (fun _ => BoundedKernel B)
        (fun _ => printedLaw B (cutoff_positive hs hB))).eventMass
          (fun x => publicTest B s (observedU x.1 x.2) = true) -
      (P.dependentBind (fun _ => α) S).eventMass
        (fun x => publicTest B s ((componentS x.1 x.2).map HNF.degree) = true) := by
  apply P.dependentBind_signed_gap
  intro i
  exact attack_correct_signed (S i) (target i) (codomain i) (componentS i)
    (observedU i) p hs hp hB hcut (htarget i) (hpoint i) (hobserved i)

end IsogenyAttack
