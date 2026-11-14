import IsogenyAttack.IsogenySampler
import IsogenyAttack.ActualKernelSampler

/-! The printed degree-first distribution on unadorned actual morphisms. -/
namespace IsogenyAttack.RawDegreeSampler
open WeierstrassCurve WeierstrassCurve.Affine TauCeti IsogenySampler

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [NeZero (2 : K)] [IsAlgClosed K]
    (W : Affine K) [W.IsElliptic]

abbrev DecoratedKernel (B : ℕ) :=
  Σ S : ActualKernel W.Point B, MontgomeryMapsWithKernel W S.2.val

/-- A degree, a Montgomery target coefficient, and a genuine isogeny. -/
abbrev Outcome (B : ℕ) := Σ d : DegreeIndex B, DegreeMaps W d.val

def kernel {B : ℕ} (φ : Outcome W B) : ActualKernel W.Point B :=
  ⟨φ.1, degreeMapKernel W φ.2⟩

def decoratedEquivOutcome (B : ℕ) : DecoratedKernel W B ≃ Outcome W B where
  toFun x := ⟨x.1.1, (degreeMapsEquivKernelMaps W x.1.1.val).symm ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, (degreeMapsEquivKernelMaps W x.1.val x.2).1⟩,
    (degreeMapsEquivKernelMaps W x.1.val x.2).2⟩
  left_inv x := by
    rcases x with ⟨⟨d, S⟩, φ⟩
    exact congrArg (fun y : Σ S : DegreeKernel W d.val,
      MontgomeryMapsWithKernel W S.val => (⟨⟨d, y.1⟩, y.2⟩ : DecoratedKernel W B))
      ((degreeMapsEquivKernelMaps W d.val).apply_symm_apply ⟨S, φ⟩)
  right_inv x := by
    rcases x with ⟨d, φ⟩
    simp

theorem decoratedEquivOutcome_kernel (B : ℕ) (x : DecoratedKernel W B) :
    kernel W (decoratedEquivOutcome W B x) = x.1 := by
  have h := congrArg (fun y : DecoratedKernel W B => y.1)
    ((decoratedEquivOutcome W B).symm_apply_apply x)
  exact h

local instance subgroupFinite {B : ℕ} (S : ActualKernel W.Point B) : Finite S.2.val := by
  apply Nat.finite_of_card_ne_zero
  rw [S.2.property]
  exact Nat.ne_of_gt (Finset.mem_Icc.mp S.1.property).1

variable {W}

@[reducible] def mapFiberFintype (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {B : ℕ} (S : ActualKernel W.Point B) : Fintype (MontgomeryMapsWithKernel W S.2.val) := by
  letI := montgomeryMapsWithKernel_finite W S.2.val h2 h3
  exact Fintype.ofFinite _

@[reducible] def outcomeFintype (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Fintype (Outcome W B) := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  letI : ∀ S : ActualKernel W.Point B, Fintype (MontgomeryMapsWithKernel W S.2.val) :=
    mapFiberFintype h2 h3
  exact Fintype.ofEquiv (DecoratedKernel W B) (decoratedEquivOutcome W B)

/-- Sample the printed degree-weighted actual kernel law and then uniformly
sample all twelve genuine morphisms with that kernel. -/
def decoratedLaw (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    letI := actualKernelFintype ha₁ ha₃ B hdeg
    letI : ∀ S : ActualKernel W.Point B, Fintype (MontgomeryMapsWithKernel W S.2.val) :=
      mapFiberFintype h2 h3
    FiniteLaw (DecoratedKernel W B) := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  letI : ∀ S : ActualKernel W.Point B, Fintype (MontgomeryMapsWithKernel W S.2.val) :=
    mapFiberFintype h2 h3
  letI : ∀ S : ActualKernel W.Point B, Nonempty (MontgomeryMapsWithKernel W S.2.val) :=
    fun S => montgomeryMapsWithKernel_nonempty W S.2.val h2 h3
  exact (actualPrintedLaw ha₁ ha₃ B hdeg hB).dependentBind
    (fun S => MontgomeryMapsWithKernel W S.2.val) (fun _ => FiniteLaw.uniform _)

/-- The law on raw outcomes, with no stored kernel. -/
def law (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    @FiniteLaw (Outcome W B) (outcomeFintype ha₁ ha₃ B hdeg h2 h3) := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  letI : ∀ S : ActualKernel W.Point B, Fintype (MontgomeryMapsWithKernel W S.2.val) :=
    mapFiberFintype h2 h3
  letI := outcomeFintype ha₁ ha₃ B hdeg h2 h3
  exact (decoratedLaw ha₁ ha₃ B hdeg hB h2 h3).pushForward (decoratedEquivOutcome W B)

/-- Every actual degree-d morphism has exactly the printed degree weight
divided by twelve times the proved number of order-d kernels. -/
theorem law_mass (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (φ : Outcome W B) :
    letI := outcomeFintype ha₁ ha₃ B hdeg h2 h3
    (law ha₁ ha₃ B hdeg hB h2 h3).mass φ =
      (printedWeight φ.1.val : ℝ) /
        (normalizer B * 12 * (kernelCount φ.1.val : ℝ)) := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  letI : ∀ S : ActualKernel W.Point B, Fintype (MontgomeryMapsWithKernel W S.2.val) :=
    mapFiberFintype h2 h3
  letI := outcomeFintype ha₁ ha₃ B hdeg h2 h3
  rw [law, FiniteLaw.pushForward_equiv_mass]
  change (actualPrintedLaw ha₁ ha₃ B hdeg hB).mass
      ((decoratedEquivOutcome W B).symm φ).1 *
    (1 / (Fintype.card (MontgomeryMapsWithKernel W
      ((decoratedEquivOutcome W B).symm φ).1.2.val) : ℝ)) = _
  rw [actualPrintedLaw_mass, Fintype.card_eq_nat_card, card_montgomeryMapsWithKernel W _ h2 h3]
  change (printedWeight φ.1.val : ℝ) /
    (normalizer B * (kernelCount φ.1.val : ℝ)) * (1 / 12) = _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Every event depending on the actual kernel has precisely its previously
proved actual-kernel probability. This transfers the attack bound unchanged. -/
theorem law_kernel_event (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (E : ActualKernel W.Point B → Prop) :
    letI := actualKernelFintype ha₁ ha₃ B hdeg
    letI := outcomeFintype ha₁ ha₃ B hdeg h2 h3
    (law ha₁ ha₃ B hdeg hB h2 h3).eventMass (fun φ => E (kernel W φ)) =
      (actualPrintedLaw ha₁ ha₃ B hdeg hB).eventMass E := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  letI : ∀ S : ActualKernel W.Point B, Fintype (MontgomeryMapsWithKernel W S.2.val) :=
    mapFiberFintype h2 h3
  letI := outcomeFintype ha₁ ha₃ B hdeg h2 h3
  rw [law, FiniteLaw.pushForward_event]
  simp_rw [decoratedEquivOutcome_kernel]
  rw [decoratedLaw, FiniteLaw.dependentBind_eventMass, FiniteLaw.eventMass_eq_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : E S <;> simp [h]

theorem law_kernel_mass (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (S : ActualKernel W.Point B) :
    letI := actualKernelFintype ha₁ ha₃ B hdeg
    letI := outcomeFintype ha₁ ha₃ B hdeg h2 h3
    ((law ha₁ ha₃ B hdeg hB h2 h3).pushForward (kernel W)).mass S =
      (actualPrintedLaw ha₁ ha₃ B hdeg hB).mass S := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  letI := outcomeFintype ha₁ ha₃ B hdeg h2 h3
  change (law ha₁ ha₃ B hdeg hB h2 h3).eventMass (fun φ => kernel W φ = S) = _
  rw [law_kernel_event ha₁ ha₃ B hdeg hB h2 h3 (fun T => T = S)]
  simp [FiniteLaw.eventMass_eq_sum]

end
end IsogenyAttack.RawDegreeSampler
