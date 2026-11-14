import IsogenyAttack.EllipticKernels
import IsogenyAttack.TargetSampler
import IsogenyAttack.StationaryRootLaw
import IsogenyAttack.FiniteLawPushForward
import IsogenyAttack.Experiments

/-!
# Laws on actual elliptic-curve subgroups

The degree-by-degree torsion bases classify actual subgroups. Scalar stripping
is performed in the actual curve point group. When the stripped subgroup is
encoded again, its own degree's basis is used; no compatibility between bases
at different degrees is assumed.
-/
namespace IsogenyAttack

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section
open scoped Classical

/-- A bounded actual kernel, recording its order and the subgroup itself. -/
abbrev ActualKernel (G : Type*) [AddCommGroup G] (B : ℕ) :=
  Sigma fun d : DegreeIndex B => {S : AddSubgroup G // Nat.card S = d.val}

/-- Separate an HNF's actual degree from its code. -/
def boundedDegreeSigmaEquiv (B : ℕ) :
    BoundedKernel B ≃ Sigma (fun d : DegreeIndex B => {h : HNF // h.degree = d.val}) where
  toFun h := ⟨⟨h.val.degree, Finset.mem_Icc.mpr ⟨h.val.degree_pos,h.property⟩⟩,⟨h.val,rfl⟩⟩
  invFun h := ⟨h.2.val, by rw [h.2.property]; exact (Finset.mem_Icc.mp h.1.property).2⟩
  left_inv _ := rfl
  right_inv h := by
    rcases h with ⟨⟨d,hd⟩,⟨h,heq⟩⟩
    cases heq
    rfl

variable {K : Type*} [Field K] [NeZero (2 : K)] [IsAlgClosed K]
    {W : Affine K} [W.IsElliptic]

/-- Every degree used below is prime to the characteristic. -/
def ValidDegrees (K : Type*) [Field K] (B : ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → d ≤ B → (d : K) ≠ 0

/-- Classification of all actual kernels up to the cutoff. -/
def actualKernelEquiv (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) :
    ActualKernel W.Point B ≃ BoundedKernel B :=
  (Equiv.sigmaCongrRight fun d : DegreeIndex B =>
    ellipticKernelHNFEquiv ha₁ ha₃
      (hdeg d.val (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp d.property).2)).trans
    (boundedDegreeSigmaEquiv B).symm

/-- The code's degree is the actual order of its subgroup. -/
theorem actualKernelEquiv_degree (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) :
    (actualKernelEquiv ha₁ ha₃ B hdeg S).val.degree = S.1.val := by
  exact (ellipticKernelHNFEquiv ha₁ ha₃
    (hdeg S.1.val (Finset.mem_Icc.mp S.1.property).1 (Finset.mem_Icc.mp S.1.property).2) S.2).property

/-- Actual scalar-stripped subgroup, with no change-of-degree encoding assumption. -/
def actualStrip (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) : AddSubgroup W.Point :=
  S.2.val.map (nsmulAddMonoidHom (actualKernelEquiv ha₁ ha₃ B hdeg S).val.content)

/-- Stripping in the actual point group has the degree computed from its code. -/
theorem actualStrip_card (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) :
    Nat.card (actualStrip ha₁ ha₃ B hdeg S) =
      (actualKernelEquiv ha₁ ha₃ B hdeg S).val.cyclicDegree := by
  exact (elliptic_kernel_code_spec ha₁ ha₃
    (hdeg S.1.val (Finset.mem_Icc.mp S.1.property).1 (Finset.mem_Icc.mp S.1.property).2)
    S.2.val S.2.property).1

/-- The actual stripped subgroup is cyclic. -/
theorem actualStrip_cyclic (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) :
    IsAddCyclic (actualStrip ha₁ ha₃ B hdeg S) := by
  exact (elliptic_kernel_code_spec ha₁ ha₃
    (hdeg S.1.val (Finset.mem_Icc.mp S.1.property).1 (Finset.mem_Icc.mp S.1.property).2)
    S.2.val S.2.property).2.1

/-- A finite enumeration of the actual kernels, supplied by the proved equivalence. -/
@[reducible] def actualKernelFintype (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) : Fintype (ActualKernel W.Point B) :=
  Fintype.ofEquiv (BoundedKernel B) (actualKernelEquiv ha₁ ha₃ B hdeg).symm

/-- Degree-first sampling on actual subgroups. -/
def actualPrintedLaw (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) :
    @FiniteLaw (ActualKernel W.Point B) (actualKernelFintype ha₁ ha₃ B hdeg) := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  exact (printedLaw B hB).pushForward (actualKernelEquiv ha₁ ha₃ B hdeg).symm

/-- Stripping returns another actual bounded kernel. -/
def actualStripBounded (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) :
    ActualKernel W.Point B :=
  ⟨⟨Nat.card (actualStrip ha₁ ha₃ B hdeg S), Finset.mem_Icc.mpr ⟨by
      rw [actualStrip_card]
      exact (actualKernelEquiv ha₁ ha₃ B hdeg S).val.cyclicDegree_pos, by
      rw [actualStrip_card]
      exact (actualKernelEquiv ha₁ ha₃ B hdeg S).val.cyclicDegree_le_degree.trans
        (actualKernelEquiv ha₁ ha₃ B hdeg S).property⟩⟩,
    ⟨actualStrip ha₁ ha₃ B hdeg S,rfl⟩⟩

/-- Re-encode the actual stripped subgroup at its own degree. This is not
assumed to equal `HNF.strip` of its original code. -/
def recodedStrip (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) : HNF :=
  (actualKernelEquiv ha₁ ha₃ B hdeg (actualStripBounded ha₁ ha₃ B hdeg S)).val

@[simp] theorem recodedStrip_degree (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) :
    (recodedStrip ha₁ ha₃ B hdeg S).degree = Nat.card (actualStrip ha₁ ha₃ B hdeg S) :=
  actualKernelEquiv_degree ha₁ ha₃ B hdeg (actualStripBounded ha₁ ha₃ B hdeg S)

/-- Extend an actual subgroup target map to arithmetic codes, only to apply
the finite support bound. Codes outside the cutoff receive the bottom target. -/
def actualCodomainCode {τ : Type*} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ) (h : HNF) : τ :=
  if hh : h.degree ≤ B then
    codomain ((actualKernelEquiv ha₁ ha₃ B hdeg).symm ⟨h,hh⟩).2.val
  else codomain ⊥

/-- Re-encoding changes no subgroup and hence changes no target. -/
theorem actualCodomainCode_recodedStrip {τ : Type*} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ)
    (S : ActualKernel W.Point B) :
    actualCodomainCode ha₁ ha₃ B hdeg codomain (recodedStrip ha₁ ha₃ B hdeg S) =
      codomain (actualStrip ha₁ ha₃ B hdeg S) := by
  let e := actualKernelEquiv ha₁ ha₃ B hdeg
  let T := actualStripBounded ha₁ ha₃ B hdeg S
  have hb : (recodedStrip ha₁ ha₃ B hdeg S).degree ≤ B := (e T).property
  rw [actualCodomainCode, dif_pos hb]
  change codomain (e.symm (e T)).2.val = _
  rw [e.symm_apply_apply]
  rfl

/-- Actual connecting subgroups, with the target tested after actual scalar stripping. -/
abbrev ActualConnectingKernel {τ : Type*} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ) (t : τ) :=
  {S : ActualKernel W.Point B // S.1.val < B ∧ codomain (actualStrip ha₁ ha₃ B hdeg S) = t}

abbrev ActualTargetOutcome {τ : Type*} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ) :=
  Sigma fun t => Option (ActualConnectingKernel ha₁ ha₃ B hdeg codomain t)

@[reducible] def actualTargetFintype {τ : Type*} [Fintype τ] (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ) :
    Fintype (ActualTargetOutcome ha₁ ha₃ B hdeg codomain) := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  unfold ActualTargetOutcome ActualConnectingKernel
  infer_instance

/-- Target-first law: uniform on actual connecting subgroups; empty fibers fail. -/
def actualTargetFirstLaw {τ : Type*} [Fintype τ] (μ : FiniteLaw τ)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ) :
    @FiniteLaw (ActualTargetOutcome ha₁ ha₃ B hdeg codomain)
      (actualTargetFintype ha₁ ha₃ B hdeg codomain) := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  letI (t : τ) : Fintype (ActualConnectingKernel ha₁ ha₃ B hdeg codomain t) :=
    inferInstanceAs (Fintype {_S : ActualKernel W.Point B // _})
  exact μ.dependentBind (fun t => Option (ActualConnectingKernel ha₁ ha₃ B hdeg codomain t))
    (fun t => FiniteLaw.uniformOrFailure (ActualConnectingKernel ha₁ ha₃ B hdeg codomain t))

/-- The target is not resampled when a connecting fiber is empty. -/
theorem actualTargetFirstLaw_marginal {τ : Type*} [Fintype τ] (μ : FiniteLaw τ)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ) (t : τ) :
    letI := actualTargetFintype ha₁ ha₃ B hdeg codomain
    (actualTargetFirstLaw μ ha₁ ha₃ B hdeg codomain).eventMass (fun x => x.1 = t) = μ.mass t := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  exact FiniteLaw.dependentBind_marginal μ _ _ t

/-- The public subgroup-order observation in the actual target experiment. -/
def actualTargetDegree {τ : Type*} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ)
    (x : ActualTargetOutcome ha₁ ha₃ B hdeg codomain) : Option ℕ :=
  x.2.map fun S => Nat.card (actualStrip ha₁ ha₃ B hdeg S.val)

/-- An auxiliary arithmetic encoding of the actual observed subgroup. -/
def actualTargetCode {τ : Type*} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ)
    (x : ActualTargetOutcome ha₁ ha₃ B hdeg codomain) : Option HNF :=
  x.2.map fun S => recodedStrip ha₁ ha₃ B hdeg S.val

@[simp] theorem actualTargetCode_degree {τ : Type*} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ)
    (x : ActualTargetOutcome ha₁ ha₃ B hdeg codomain) :
    (actualTargetCode ha₁ ha₃ B hdeg codomain x).map HNF.degree =
      actualTargetDegree ha₁ ha₃ B hdeg codomain x := by
  rcases x with ⟨t,x⟩
  cases x <;> simp [actualTargetCode,actualTargetDegree]

/-- Target preservation follows from the actual fiber and the independent recoding. -/
theorem actualTargetCode_codomain {τ : Type*} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ)
    (x : ActualTargetOutcome ha₁ ha₃ B hdeg codomain) (h : HNF)
    (hx : actualTargetCode ha₁ ha₃ B hdeg codomain x = some h) :
    x.1 = actualCodomainCode ha₁ ha₃ B hdeg codomain h := by
  rcases x with ⟨t,x⟩
  cases x with
  | none => simp [actualTargetCode] at hx
  | some S =>
    simp only [actualTargetCode,Option.map_some,Option.some.injEq] at hx
    rw [← hx,actualCodomainCode_recodedStrip]
    exact S.property.2.symm

/-- Each actual subgroup of order d receives the required degree weight divided
by the proved sigma-one number of such subgroups. This also proves that the
sampling law itself is independent of the chosen torsion bases. -/
theorem actualPrintedLaw_mass (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) (S : ActualKernel W.Point B) :
    letI := actualKernelFintype ha₁ ha₃ B hdeg
    (actualPrintedLaw ha₁ ha₃ B hdeg hB).mass S =
      (printedWeight S.1.val : ℝ) / (normalizer B * (kernelCount S.1.val : ℝ)) := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  rw [actualPrintedLaw,FiniteLaw.pushForward_equiv_mass]
  simp only [Equiv.symm_symm,printedLaw_mass,actualKernelEquiv_degree]

/-- Acceptance probability computed from the actual stripped subgroup's order. -/
def actualPrintedAcceptance (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) (s : ℕ) : ℝ :=
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  (actualPrintedLaw ha₁ ha₃ B hdeg hB).eventMass
    (fun S => publicTest B s (some (Nat.card (actualStrip ha₁ ha₃ B hdeg S))) = true)

/-- Target acceptance also reads an actual subgroup's order, or failure. -/
def actualTargetAcceptance {τ : Type*} [Fintype τ] (μ : FiniteLaw τ)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ) (s : ℕ) : ℝ :=
  letI := actualTargetFintype ha₁ ha₃ B hdeg codomain
  (actualTargetFirstLaw μ ha₁ ha₃ B hdeg codomain).eventMass
    (fun x => publicTest B s (actualTargetDegree ha₁ ha₃ B hdeg codomain x) = true)

/-- Exact source-law transfer; the event is determined by genuine scalar images. -/
theorem actualPrintedAcceptance_eq (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) (s : ℕ) :
    actualPrintedAcceptance ha₁ ha₃ B hdeg hB s =
      (printedLaw B hB).eventMass (fun h => publicTest B s (some h.val.cyclicDegree) = true) := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  rw [actualPrintedAcceptance,actualPrintedLaw,FiniteLaw.pushForward_event]
  apply FiniteLaw.eventMass_congr
  intro h
  rw [actualStrip_card,Equiv.apply_symm_apply]

/-- The finite attack theorem for actual curve subgroups. The only target input
is a map from actual subgroups to targets and its sampled marginal law. No
compatibility of torsion bases across degrees, geometric torsion oracle,
subgroup count, or public-degree preservation is assumed.

Identifying `codomain` with an algebraic quotient isogeny's codomain, and the
law with the original experiment, remain separate geometric obligations. -/
theorem actual_kernel_samplers_attack {τ : Type*} [Fintype τ]
    (μ : FiniteLaw τ) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {B s : ℕ} (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ)
    (p : ℝ) (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8*s^2 ≤ B)
    (hcut : (B : ℝ)^2 < 4*p)
    (hμ : ∀ t, μ.mass t ≤ 12/(p-1)) :
    1/(1024*(s : ℝ)^3) ≤
      |actualPrintedAcceptance ha₁ ha₃ B hdeg (cutoff_positive hs hB) s -
        actualTargetAcceptance μ ha₁ ha₃ B hdeg codomain s| := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  letI := actualTargetFintype ha₁ ha₃ B hdeg codomain
  rw [actualPrintedAcceptance_eq]
  have h := attack_correct
    (actualTargetFirstLaw μ ha₁ ha₃ B hdeg codomain) Sigma.fst
    (actualCodomainCode ha₁ ha₃ B hdeg codomain)
    (actualTargetCode ha₁ ha₃ B hdeg codomain) (fun h => some h.val.cyclicDegree)
    p hs hp hB hcut
    (actualTargetCode_codomain ha₁ ha₃ B hdeg codomain)
    (fun t => (actualTargetFirstLaw_marginal μ ha₁ ha₃ B hdeg codomain t).trans_le (hμ t))
    (fun _ _ => rfl)
  simpa only [actualTargetCode_degree,actualTargetAcceptance] using h

/-- The actual-subgroup advantage has the same positive orientation for every
source curve, so the lower bound is preserved by averaging source contexts. -/
theorem actual_kernel_samplers_attack_signed {τ : Type*} [Fintype τ]
    (μ : FiniteLaw τ) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {B s : ℕ} (hdeg : ValidDegrees K B) (codomain : AddSubgroup W.Point → τ)
    (p : ℝ) (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8*s^2 ≤ B)
    (hcut : (B : ℝ)^2 < 4*p)
    (hμ : ∀ t, μ.mass t ≤ 12/(p-1)) :
    1/(1024*(s : ℝ)^3) ≤
      actualPrintedAcceptance ha₁ ha₃ B hdeg (cutoff_positive hs hB) s -
        actualTargetAcceptance μ ha₁ ha₃ B hdeg codomain s := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  letI := actualTargetFintype ha₁ ha₃ B hdeg codomain
  rw [actualPrintedAcceptance_eq]
  have h := attack_correct_signed
    (actualTargetFirstLaw μ ha₁ ha₃ B hdeg codomain) Sigma.fst
    (actualCodomainCode ha₁ ha₃ B hdeg codomain)
    (actualTargetCode ha₁ ha₃ B hdeg codomain) (fun h => some h.val.cyclicDegree)
    p hs hp hB hcut
    (actualTargetCode_codomain ha₁ ha₃ B hdeg codomain)
    (fun t => (actualTargetFirstLaw_marginal μ ha₁ ha₃ B hdeg codomain t).trans_le (hμ t))
    (fun _ _ => rfl)
  simpa only [actualTargetCode_degree,actualTargetAcceptance] using h

omit [NeZero (2 : K)] [IsAlgClosed K] in
/-- The quantitative cutoff ensures that all sampled orders are prime to
characteristic p. This is derived from the numeric hypotheses. -/
theorem validDegrees_of_cutoff (p B : ℕ) [CharP K p]
    (hp : 49 ≤ p) (hcut : (B : ℝ)^2 < 4*(p : ℝ)) : ValidDegrees K B := by
  have hBp : B < p := by
    by_contra hn
    have hle : (p : ℝ) ≤ (B : ℝ) := by exact_mod_cast (Nat.le_of_not_gt hn)
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast (show 4 ≤ p by omega)
    have hsq : (p : ℝ)^2 ≤ (B : ℝ)^2 := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hle
    nlinarith
  intro d hd hdB
  exact Legendre.small_natCast_ne_zero p hd (lt_of_le_of_lt hdB hBp)

/-- The explicit finite distinguishing theorem on actual elliptic-curve
subgroups and the constructed Hasse-coefficient target law. All counting,
scalar-stripping, target marginal, and point-mass inputs are proved.
The map from actual subgroups to target classes remains an explicit parameter;
this theorem does not call it a quotient-isogeny construction. -/
theorem actual_hasse_samplers_attack (p : ℕ) [CharP K p] [Fact p.Prime]
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8*s^2 ≤ B)
    (hcut : (B : ℝ)^2 < 4*(p : ℝ))
    (codomain : AddSubgroup W.Point → Legendre.HasseJClass (K := K) ((p-1)/2)) :
    let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
    1/(1024*(s : ℝ)^3) ≤
      |actualPrintedAcceptance ha₁ ha₃ B hdeg (cutoff_positive hs hB) s -
        actualTargetAcceptance (Legendre.hasseInvariantLaw (K := K) p (by omega))
          ha₁ ha₃ B hdeg codomain s| := by
  exact actual_kernel_samplers_attack
    (Legendre.hasseInvariantLaw (K := K) p (by omega)) ha₁ ha₃
    (validDegrees_of_cutoff p B hp hcut) codomain p hs (by exact_mod_cast hp) hB hcut
    (Legendre.hasseInvariantLaw_mass_le p (by omega))

/-- Signed actual-subgroup version of the Hasse-law attack theorem. -/
theorem actual_hasse_samplers_attack_signed (p : ℕ) [CharP K p] [Fact p.Prime]
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8*s^2 ≤ B)
    (hcut : (B : ℝ)^2 < 4*(p : ℝ))
    (codomain : AddSubgroup W.Point → Legendre.HasseJClass (K := K) ((p-1)/2)) :
    let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
    1/(1024*(s : ℝ)^3) ≤
      actualPrintedAcceptance ha₁ ha₃ B hdeg (cutoff_positive hs hB) s -
        actualTargetAcceptance (Legendre.hasseInvariantLaw (K := K) p (by omega))
          ha₁ ha₃ B hdeg codomain s := by
  exact actual_kernel_samplers_attack_signed
    (Legendre.hasseInvariantLaw (K := K) p (by omega)) ha₁ ha₃
    (validDegrees_of_cutoff p B hp hcut) codomain p hs (by exact_mod_cast hp) hB hcut
    (Legendre.hasseInvariantLaw_mass_le p (by omega))

end
end IsogenyAttack
