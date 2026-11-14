import IsogenyAttack.Kernels
import IsogenyAttack.Probability
import IsogenyAttack.Bounds
import IsogenyAttack.Weights
import IsogenyAttack.Sampler
import IsogenyAttack.Normalizer

/-!
The short-degree distinguisher, assembled from concrete HNF kernel codes and
finite probability laws. The target law is arbitrary subject to the displayed
target-mass and reachability hypotheses. These are the explicit geometric
interface, not hidden axioms about elliptic curves.
-/

namespace IsogenyAttack

open scoped BigOperators

/-- The public bit computed by the attack. -/
def shortDegree (L : ℕ) (x : HNF) : Prop := x.cyclicDegree ≤ L

/-- Executable attack: reject failures; compare the public degree with the
integer threshold. No curve or isogeny operation is performed by this program. -/
def publicTest (B s : ℕ) (degree : Option ℕ) : Bool :=
  match degree with
  | none => false
  | some c => decide (c ≤ threshold B s)

@[simp] theorem publicTest_none (B s : ℕ) : publicTest B s none = false := rfl

@[simp] theorem publicTest_some (B s c : ℕ) :
    publicTest B s (some c) = true ↔ c ≤ threshold B s := by
  simp [publicTest]

theorem publicTest_spec (B s : ℕ) (degree : Option ℕ) :
    publicTest B s degree = true ↔ ∃ c, degree = some c ∧ c ≤ threshold B s := by
  cases degree <;> simp

/-- Only the support of the accepted targets matters. A failure outcome may be
included in `α`, provided it does not satisfy the acceptance event. -/
theorem target_first_upper {α τ : Type*} [Fintype α] [Fintype τ]
    (S : FiniteLaw α) (E : α → Prop) (target : α → τ) (codomain : HNF → τ)
    (p : ℝ) (L : ℕ) (hp : 1 < p)
    (hsupport : ∀ x, E x → ∃ k : HNF, k.degree ≤ L ∧ target x = codomain k)
    (hpoint : ∀ t, S.eventMass (fun x => target x = t) ≤ 12 / (p - 1)) :
    S.eventMass E ≤ 12 * (L : ℝ) ^ 2 / (p - 1) := by
  classical
  let targets : Finset τ := Finset.univ.image (fun k : BoundedKernel L => codomain k.val)
  have hc : targets.card ≤ L ^ 2 :=
    (Finset.card_image_le.trans (by simpa using HNF.bounded_card_le L))
  have hsub : ∀ x, E x → target x ∈ targets := by
    intro x hx
    obtain ⟨k, hk, htarget⟩ := hsupport x hx
    exact Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_univ _, htarget.symm⟩
  calc
    S.eventMass E ≤ (12 / (p - 1)) * (targets.card : ℝ) :=
      S.target_support_bound E target targets _ hsub (fun t _ => hpoint t)
    _ ≤ (12 / (p - 1)) * (L : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast hc
      · positivity
    _ = 12 * (L : ℝ) ^ 2 / (p - 1) := by ring

/-- Every favorable scalar lift is a valid interior outcome of the sampler. -/
def favorableOutcome {M L B : ℕ} (hinterior : M ^ 2 * L < B)
    (x : LiftIndex M L) : BoundedKernel B :=
  ⟨liftIndexMap x, (liftIndexMap_interior hinterior x).le⟩

theorem favorableOutcome_injective {M L B : ℕ} (hinterior : M ^ 2 * L < B) :
    Function.Injective (favorableOutcome hinterior) := by
  intro x y h
  exact liftIndexMap_injective M L (congrArg Subtype.val h)

/-- Lower bound with every sampling hypothesis visible. Only interior atom
masses are needed; endpoint completions do not enter the proof. -/
theorem degree_first_event_lower {B M L : ℕ} (U : FiniteLaw (BoundedKernel B))
    (E : BoundedKernel B → Prop)
    (Z : ℝ) (_hB : 0 < B) (hZ : 0 < Z)
    (hZupper : Z ≤ 4 * (B : ℝ) ^ 2) (hinterior : M ^ 2 * L < B)
    (haccept : ∀ x : LiftIndex M L, E (favorableOutcome hinterior x))
    (hmass : ∀ k : BoundedKernel B, k.val.degree < B →
      U.mass k = (printedWeight k.val.degree : ℝ) /
        (Z * (kernelCount k.val.degree : ℝ))) :
    (M : ℝ) * L * (L + 1) / (8 * (B : ℝ) ^ 2) ≤
      U.eventMass E := by
  classical
  have hf := U.favorable_injection_bound
    E (favorableOutcome hinterior)
    (favorableOutcome_injective hinterior)
    (fun _ : LiftIndex M L => 1 / (4 * (B : ℝ) ^ 2))
    haccept (by
      intro x
      rw [hmass _ (liftIndexMap_interior hinterior x)]
      have hd : 0 < (liftIndexMap x).degree :=
        Nat.mul_pos (liftIndexMap x).a_pos (liftIndexMap x).e_pos
      have hc : (0 : ℝ) < kernelCount (liftIndexMap x).degree := by
        exact_mod_cast kernelCount_pos hd
      have hw : (kernelCount (liftIndexMap x).degree : ℝ) ≤
          printedWeight (liftIndexMap x).degree := by
        have hnat : kernelCount (liftIndexMap x).degree ≤
            printedWeight (liftIndexMap x).degree := by
          rw [kernelCount_eq_sigma]
          exact sigmaOne_le_printedWeight _
        exact_mod_cast hnat
      calc
        1 / (4 * (B : ℝ) ^ 2) ≤ 1 / Z := one_div_le_one_div_of_le hZ hZupper
        _ ≤ _ := by
          dsimp [favorableOutcome]
          apply (div_le_div_iff₀ hZ (mul_pos hZ hc)).2
          nlinarith [mul_le_mul_of_nonneg_left hw hZ.le])
  have hcard : (2 : ℝ) * Fintype.card (LiftIndex M L) =
      (M : ℝ) * L * (L + 1) := by
    exact_mod_cast liftIndex_card_twice M L
  have heq : (∑ _x : LiftIndex M L, 1 / (4 * (B : ℝ) ^ 2)) =
      (M : ℝ) * L * (L + 1) / (8 * (B : ℝ) ^ 2) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hcard]
    ring
  rw [heq] at hf
  exact hf

/-- Specialization to the degree event. -/
theorem degree_first_lower {B M L : ℕ} (U : FiniteLaw (BoundedKernel B))
    (Z : ℝ) (hB : 0 < B) (hZ : 0 < Z)
    (hZupper : Z ≤ 4 * (B : ℝ) ^ 2) (hinterior : M ^ 2 * L < B)
    (hmass : ∀ k : BoundedKernel B, k.val.degree < B →
      U.mass k = (printedWeight k.val.degree : ℝ) /
        (Z * (kernelCount k.val.degree : ℝ))) :
    (M : ℝ) * L * (L + 1) / (8 * (B : ℝ) ^ 2) ≤
      U.eventMass (fun k => shortDegree L k.val) :=
  degree_first_event_lower U _ Z hB hZ hZupper hinterior
    (fun x => liftIndexMap_short x) hmass

/-- The same lower bound for the executable test, allowing any degree or failure
at the problematic endpoint. The observation law is prescribed only inside it. -/
theorem degree_first_publicTest_lower {B s : ℕ} (U : FiniteLaw (BoundedKernel B))
    (observed : BoundedKernel B → Option ℕ)
    (Z : ℝ) (hB : 0 < B) (hZ : 0 < Z)
    (hZupper : Z ≤ 4 * (B : ℝ) ^ 2)
    (hinterior : s ^ 2 * threshold B s < B)
    (hobserved : ∀ k : BoundedKernel B, k.val.degree < B →
      observed k = some k.val.cyclicDegree)
    (hmass : ∀ k : BoundedKernel B, k.val.degree < B →
      U.mass k = (printedWeight k.val.degree : ℝ) /
        (Z * (kernelCount k.val.degree : ℝ))) :
    (s : ℝ) * threshold B s * (threshold B s + 1) / (8 * (B : ℝ) ^ 2) ≤
      U.eventMass (fun k => publicTest B s (observed k) = true) := by
  apply degree_first_event_lower U _ Z hB hZ hZupper hinterior _ hmass
  intro x
  rw [hobserved _ (liftIndexMap_interior hinterior x), publicTest_some]
  exact liftIndexMap_short x

/-- Finite signed gap for the actual threshold test on the encoded kernels. -/
theorem short_degree_gap {α τ : Type*} [Fintype α] [Fintype τ]
    {B M L : ℕ} (U : FiniteLaw (BoundedKernel B)) (S : FiniteLaw α)
    (E : α → Prop) (target : α → τ) (codomain : HNF → τ)
    (p Z : ℝ) (hp : 49 ≤ p) (hB : 0 < B) (hcut : (B : ℝ) ^ 2 < 4 * p)
    (hZ : 0 < Z) (hZupper : Z ≤ 4 * (B : ℝ) ^ 2)
    (hinterior : M ^ 2 * L < B)
    (hsupport : ∀ x, E x → ∃ k : HNF, k.degree ≤ L ∧ target x = codomain k)
    (hpoint : ∀ t, S.eventMass (fun x => target x = t) ≤ 12 / (p - 1))
    (hmass : ∀ k : BoundedKernel B, k.val.degree < B →
      U.mass k = (printedWeight k.val.degree : ℝ) /
        (Z * (kernelCount k.val.degree : ℝ))) :
    ((M : ℝ) / 8 - 49) * (L : ℝ) ^ 2 / (B : ℝ) ^ 2 ≤
      U.eventMass (fun k => shortDegree L k.val) - S.eventMass E := by
  apply finite_gap hp (by exact_mod_cast hB) (by positivity) (by positivity) hcut
  · exact degree_first_lower U Z hB hZ hZupper hinterior hmass
  · exact target_first_upper S E target codomain p L (by linarith) hsupport hpoint

/-- Explicit inverse-polynomial advantage, with the threshold computed using
natural-number floor division. -/
theorem short_degree_inverse_cubic {α τ : Type*} [Fintype α] [Fintype τ]
    {B s : ℕ} (U : FiniteLaw (BoundedKernel B)) (S : FiniteLaw α)
    (E : α → Prop) (target : α → τ) (codomain : HNF → τ)
    (p Z : ℝ) (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * p)
    (hZ : 0 < Z) (hZupper : Z ≤ 4 * (B : ℝ) ^ 2)
    (hsupport : ∀ x, E x → ∃ k : HNF,
      k.degree ≤ threshold B s ∧ target x = codomain k)
    (hpoint : ∀ t, S.eventMass (fun x => target x = t) ≤ 12 / (p - 1))
    (hmass : ∀ k : BoundedKernel B, k.val.degree < B →
      U.mass k = (printedWeight k.val.degree : ℝ) /
        (Z * (kernelCount k.val.degree : ℝ))) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      |U.eventMass (fun k => shortDegree (threshold B s) k.val) - S.eventMass E| := by
  have hspos : 0 < s := by omega
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) hB
  obtain ⟨_, hinterior, hfloor⟩ := threshold_bounds (by omega : 1 ≤ s) hB
  apply FiniteLaw.gap_le_abs
  apply inverse_cubic_gap hs hp (by exact_mod_cast hBpos) hcut hfloor
  · exact degree_first_lower U Z hBpos hZ hZupper hinterior hmass
  · exact target_first_upper S E target codomain p _ (by linarith) hsupport hpoint

theorem degreeNormalizer_printed_eq_normalizer (B : ℕ) :
    degreeNormalizer (fun d => (printedWeight d : ℝ)) B = normalizer B := by
  unfold degreeNormalizer normalizer
  congr 1

/-- The exact, normalized degree-first sampler for the printed W-weight. -/
noncomputable def printedLaw (B : ℕ) (hB : 0 < B) : FiniteLaw (BoundedKernel B) :=
  degreeFirstLaw B (fun d => (printedWeight d : ℝ))
    (fun _ _ => Nat.cast_nonneg _)
    (by rw [degreeNormalizer_printed_eq_normalizer]; exact normalizer_pos hB)
    (fun _ hd => kernelCount_pos (Finset.mem_Icc.mp hd).1)

@[simp] theorem printedLaw_mass (B : ℕ) (hB : 0 < B) (k : BoundedKernel B) :
    (printedLaw B hB).mass k = (printedWeight k.val.degree : ℝ) /
      (normalizer B * (kernelCount k.val.degree : ℝ)) := by
  simp [printedLaw, degreeNormalizer_printed_eq_normalizer]

theorem cutoff_positive {B s : ℕ} (hs : 784 ≤ s) (hB : 8 * s ^ 2 ≤ B) : 0 < B := by
  have hspos : 0 < s := by omega
  exact lt_of_lt_of_le (by positivity) hB

/-- Main certificate. The W-weight law is constructed and normalized here;
there are no assumed weight estimates, favorable probabilities, or gap bounds.
The only source-specific hypotheses say which targets accepted short components
can reach, bound the target marginals, and expose the degree on valid interior
outputs. Endpoint observations may be any degree or failure.
-/
theorem publicTest_advantage {α τ : Type*} [Fintype α] [Fintype τ]
    {B s : ℕ} (S : FiniteLaw α)
    (target : α → τ) (codomain : HNF → τ)
    (observedS : α → Option ℕ) (observedU : BoundedKernel B → Option ℕ)
    (p : ℝ) (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * p)
    (hsupport : ∀ x, publicTest B s (observedS x) = true → ∃ k : HNF,
      k.degree ≤ threshold B s ∧ target x = codomain k)
    (hpoint : ∀ t, S.eventMass (fun x => target x = t) ≤ 12 / (p - 1))
    (hobserved : ∀ k : BoundedKernel B, k.val.degree < B →
      observedU k = some k.val.cyclicDegree) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      |(printedLaw B (cutoff_positive hs hB)).eventMass
          (fun k => publicTest B s (observedU k) = true) -
        S.eventMass (fun x => publicTest B s (observedS x) = true)| := by
  have hBpos := cutoff_positive hs hB
  obtain ⟨_, hinterior, hfloor⟩ := threshold_bounds (by omega : 1 ≤ s) hB
  apply FiniteLaw.gap_le_abs
  apply inverse_cubic_gap hs hp (by exact_mod_cast hBpos) hcut hfloor
  · apply degree_first_publicTest_lower _ observedU (normalizer B) hBpos
      (normalizer_pos hBpos) (normalizer_le_four_mul_square B) hinterior hobserved
    intro k _
    exact printedLaw_mass B hBpos k
  · exact target_first_upper S _ target codomain p _ (by linarith) hsupport hpoint

/-- Final correctness theorem with a structural source interface: every
successful target-first output carries a component whose codomain is its
sampled target. Its degree is what the executable test reads. The geometric
interpretation of HNF codes and the stationary marginal bound remain explicit.
-/
theorem attack_correct {α τ : Type*} [Fintype α] [Fintype τ]
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
      |(printedLaw B (cutoff_positive hs hB)).eventMass
          (fun k => publicTest B s (observedU k) = true) -
        S.eventMass (fun x => publicTest B s ((componentS x).map HNF.degree) = true)| := by
  apply publicTest_advantage S target codomain
    (fun x => (componentS x).map HNF.degree) observedU p hs hp hB hcut _ hpoint hobserved
  intro x hx
  cases hc : componentS x with
  | none => simp [hc] at hx
  | some k =>
    refine ⟨k, ?_, htarget x k hc⟩
    simpa [hc] using hx

end IsogenyAttack
