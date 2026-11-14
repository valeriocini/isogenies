import IsogenyAttack.Attack

/-!
The exact target-first sampler in the arithmetic kernel model. A target is drawn
first and never rejected. Conditional on that target, a connecting kernel is
uniform; an empty connecting fiber produces failure. Both normalization and the
unchanged target marginal are theorems of the concrete sampler.
-/

namespace IsogenyAttack
open scoped BigOperators

namespace FiniteLaw

/-- Uniformly choose an element of a finite type, or fail if the type is empty. -/
noncomputable def uniformOrFailure (α : Type*) [Fintype α] : FiniteLaw (Option α) where
  mass x := match x with
    | none => if Fintype.card α = 0 then 1 else 0
    | some _ => 1 / (Fintype.card α : ℝ)
  mass_nonneg x := by
    cases x
    · split_ifs <;> norm_num
    · positivity
  mass_sum := by
    classical
    rw [Fintype.sum_option]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    by_cases h : Fintype.card α = 0
    · simp [h]
    · simp [h, ne_of_gt (show (0 : ℝ) < Fintype.card α by exact_mod_cast Nat.pos_of_ne_zero h)]

@[simp] theorem uniformOrFailure_none (α : Type*) [Fintype α] :
    (uniformOrFailure α).mass none = if Fintype.card α = 0 then 1 else 0 := rfl

@[simp] theorem uniformOrFailure_some {α : Type*} [Fintype α] (a : α) :
    (uniformOrFailure α).mass (some a) = 1 / (Fintype.card α : ℝ) := rfl

/-- Sample the first coordinate and then sample its dependent conditional law. -/
noncomputable def dependentBind {τ : Type*} [Fintype τ]
    (μ : FiniteLaw τ) (β : τ → Type*) [∀ t, Fintype (β t)]
    (Q : ∀ t, FiniteLaw (β t)) : FiniteLaw (Sigma β) where
  mass x := μ.mass x.1 * (Q x.1).mass x.2
  mass_nonneg x := mul_nonneg (μ.mass_nonneg _) ((Q _).mass_nonneg _)
  mass_sum := by
    rw [Fintype.sum_sigma]
    calc
      (∑ t, ∑ b, μ.mass t * (Q t).mass b) = ∑ t, μ.mass t := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← Finset.mul_sum, (Q t).mass_sum, mul_one]
      _ = 1 := μ.mass_sum

/-- Conditioning in the second step never reweights the first draw. -/
theorem dependentBind_marginal {τ : Type*} [Fintype τ]
    (μ : FiniteLaw τ) (β : τ → Type*) [∀ t, Fintype (β t)]
    (Q : ∀ t, FiniteLaw (β t)) (t : τ) :
    (dependentBind μ β Q).eventMass (fun x => x.1 = t) = μ.mass t := by
  classical
  rw [eventMass_eq_sum, Fintype.sum_sigma]
  have hinner : ∀ a : τ,
      (∑ b : β a, if a = t then (dependentBind μ β Q).mass ⟨a,b⟩ else 0) =
        if a = t then μ.mass a else 0 := by
    intro a
    by_cases h : a = t
    · subst a
      simp only [if_true, dependentBind]
      rw [← Finset.mul_sum, (Q t).mass_sum, mul_one]
    · simp [h]
  simp_rw [hinner]
  simp

end FiniteLaw

/-- Connecting HNFs of original degree strictly below the response cutoff.
The codomain argument is evaluated on the primitive component. The identification
of this codomain with the actual quotient elliptic curve is not asserted here. -/
def ConnectingKernel {τ : Type*} (B : ℕ) (codomain : HNF → τ) (t : τ) :=
  { k : BoundedKernel (B - 1) // codomain k.val.strip = t }

noncomputable instance connectingKernelFintype {τ : Type*} (B : ℕ)
    (codomain : HNF → τ) (t : τ) : Fintype (ConnectingKernel B codomain t) := by
  classical
  unfold ConnectingKernel
  infer_instance

/-- The sampled target is retained even if its connecting fiber is empty. -/
abbrev TargetOutcome {τ : Type*} (B : ℕ) (codomain : HNF → τ) :=
  Sigma fun t : τ => Option (ConnectingKernel B codomain t)

noncomputable def targetFirstLaw {τ : Type*} [Fintype τ]
    (μ : FiniteLaw τ) (B : ℕ) (codomain : HNF → τ) :
    FiniteLaw (TargetOutcome B codomain) :=
  μ.dependentBind (fun t => Option (ConnectingKernel B codomain t))
    (fun t => FiniteLaw.uniformOrFailure (ConnectingKernel B codomain t))

/-- Exact target marginal, without reachability or postselection assumptions. -/
theorem targetFirstLaw_marginal {τ : Type*} [Fintype τ]
    (μ : FiniteLaw τ) (B : ℕ) (codomain : HNF → τ) (t : τ) :
    (targetFirstLaw μ B codomain).eventMass (fun x => x.1 = t) = μ.mass t :=
  FiniteLaw.dependentBind_marginal μ _ _ t

/-- Exposed primitive component; a missing connector remains a failure. -/
def targetComponent {τ : Type*} {B : ℕ} {codomain : HNF → τ}
    (x : TargetOutcome B codomain) : Option HNF :=
  x.2.map (fun k => k.val.val.strip)

/-- Target preservation follows from membership in the connecting fiber. -/
theorem targetComponent_codomain {τ : Type*} {B : ℕ} {codomain : HNF → τ}
    (x : TargetOutcome B codomain) (k : HNF)
    (h : targetComponent x = some k) : x.1 = codomain k := by
  rcases x with ⟨t, x⟩
  cases x with
  | none => simp [targetComponent] at h
  | some a =>
    simp only [targetComponent, Option.map_some, Option.some.injEq] at h
    rw [← h]
    exact a.property.symm

/-- The conditional connecting-map law is exactly uniform on its fiber. -/
@[simp] theorem targetFirstLaw_some {τ : Type*} [Fintype τ]
    (μ : FiniteLaw τ) (B : ℕ) (codomain : HNF → τ) (t : τ)
    (k : ConnectingKernel B codomain t) :
    (targetFirstLaw μ B codomain).mass ⟨t, some k⟩ =
      μ.mass t / (Fintype.card (ConnectingKernel B codomain t) : ℝ) := by
  simp only [targetFirstLaw, FiniteLaw.dependentBind, FiniteLaw.uniformOrFailure]
  ring

/-- Failure does not delete or resample an unreachable target. -/
@[simp] theorem targetFirstLaw_none {τ : Type*} [Fintype τ]
    (μ : FiniteLaw τ) (B : ℕ) (codomain : HNF → τ) (t : τ) :
    (targetFirstLaw μ B codomain).mass ⟨t, none⟩ =
      if Fintype.card (ConnectingKernel B codomain t) = 0 then μ.mass t else 0 := by
  simp only [targetFirstLaw, FiniteLaw.dependentBind, FiniteLaw.uniformOrFailure]
  split_ifs <;> simp

/-- All selected connectors obey the source experiment's strict cutoff. -/
theorem connectingKernel_degree_lt {τ : Type*} {B : ℕ} {codomain : HNF → τ}
    {t : τ} (k : ConnectingKernel B codomain t) : k.val.val.degree < B := by
  have hp := k.val.val.degree_pos
  have hb := k.val.property
  omega

/-- Scalar stripping really exposes the cyclic degree in this model. -/
theorem targetComponent_degree {τ : Type*} {B : ℕ} {codomain : HNF → τ}
    (x : TargetOutcome B codomain) :
    (targetComponent x).map HNF.degree =
      x.2.map (fun k => k.val.val.cyclicDegree) := by
  rcases x with ⟨t, x⟩
  cases x <;> simp [targetComponent]

/-- Every successful exposed component is primitive. -/
theorem targetComponent_primitive {τ : Type*} {B : ℕ} {codomain : HNF → τ}
    (x : TargetOutcome B codomain) (k : HNF)
    (h : targetComponent x = some k) : k.content = 1 := by
  rcases x with ⟨t, x⟩
  cases x with
  | none => simp [targetComponent] at h
  | some a =>
    simp only [targetComponent, Option.map_some, Option.some.injEq] at h
    rw [← h, HNF.strip_content]

/-- The theorem specialized to the constructed target-first and degree-first
samplers. No arbitrary target marginal, target preservation, or public degree
hypothesis remains: only the genuinely geometric point-mass input for μ remains.
The codomain map still has to be identified with elliptic-curve quotient targets.
-/
theorem explicit_samplers_attack {τ : Type*} [Fintype τ]
    {B s : ℕ} (μ : FiniteLaw τ) (codomain : HNF → τ) (p : ℝ)
    (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * p)
    (hμ : ∀ t, μ.mass t ≤ 12 / (p - 1)) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      |(printedLaw B (cutoff_positive hs hB)).eventMass
          (fun k => publicTest B s (some k.val.cyclicDegree) = true) -
        (targetFirstLaw μ B codomain).eventMass
          (fun x => publicTest B s ((targetComponent x).map HNF.degree) = true)| := by
  apply attack_correct (targetFirstLaw μ B codomain) Sigma.fst codomain
    targetComponent (fun k => some k.val.cyclicDegree) p hs hp hB hcut
  · exact targetComponent_codomain
  · intro t
    rw [targetFirstLaw_marginal]
    exact hμ t
  · intro k _
    rfl

end IsogenyAttack
