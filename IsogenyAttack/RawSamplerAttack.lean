import IsogenyAttack.RawDegreeSampler
import IsogenyAttack.RawTargetSampler
import IsogenyAttack.GenuineExperiments
import IsogenyAttack.ResponseCutoff
import IsogenyAttack.PublicObservation

/-! The signed attack bound for the raw-isogeny samplers. The two source
curves may differ: in Experiment 4 the degree-first source is the public curve,
whereas the target-first source is the challenge codomain. -/
namespace IsogenyAttack.RawSamplerAttack

open WeierstrassCurve WeierstrassCurve.Affine TauCeti
open scoped BigOperators

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
    {WU WS : Affine K} [WU.IsElliptic] [WS.IsElliptic]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

def degreeAcceptance (hp : 3 < p) (hu₁ : WU.a₁ = 0) (hu₃ : WU.a₃ = 0)
    (B s : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) : ℝ :=
  letI := RawDegreeSampler.outcomeFintype hu₁ hu₃ B hdeg (NeZero.ne (2 : K))
    (Legendre.small_natCast_ne_zero p (by decide) hp)
  (RawDegreeSampler.law hu₁ hu₃ B hdeg hB (NeZero.ne (2 : K))
    (Legendre.small_natCast_ne_zero p (by decide) hp)).eventMass
    (fun φ => (ArithmeticAttack.decision B s
      (genuineDegreeObservation hu₁ hu₃ B hdeg (RawDegreeSampler.kernel WU φ))).result = true)

def targetAcceptance (hp : 3 < p) (hs₁ : WS.a₁ = 0) (hs₃ : WS.a₃ = 0)
    (B s : ℕ) (hdeg : ValidDegrees K B) : ℝ :=
  letI := RawTargetSampler.outcomeFintype p hp hs₁ hs₃ B hdeg
  (RawTargetSampler.law p hp hs₁ hs₃ B hdeg).eventMass
    (fun φ => (ArithmeticAttack.decision B s
      (RawTargetSampler.observedDegree p hs₁ hs₃ B hdeg φ)).result = true)

/-- Complete raw-sampler probability bound, with independent arbitrary source
curves. Every sampled object is a genuine algebraic isogeny, and the target
coefficient is uniformly sampled from actual supersingular F_(p²) models. -/
theorem signed_gap_lower (hWS : WS.IsSupersingular p)
    (hu₁ : WU.a₁ = 0) (hu₃ : WU.a₃ = 0) (hs₁ : WS.a₁ = 0) (hs₃ : WS.a₃ = 0)
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8*s^2 ≤ B)
    (hcut : (B : ℝ)^2 < 4*(p : ℝ)) :
    let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
    1/(1024*(s : ℝ)^3) ≤
      degreeAcceptance p (by omega) hu₁ hu₃ B s hdeg (cutoff_positive hs hB) -
      targetAcceptance p (by omega) hs₁ hs₃ B s hdeg := by
  dsimp only
  let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
  letI := actualKernelFintype hu₁ hu₃ B hdeg
  letI := RawTargetSampler.outcomeFintype p (by omega) hs₁ hs₃ B hdeg
  unfold degreeAcceptance targetAcceptance
  rw [RawDegreeSampler.law_kernel_event hu₁ hu₃ B hdeg (cutoff_positive hs hB)
    (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (k := 3) (by decide) (by omega))
    (fun S => (ArithmeticAttack.decision B s
      (genuineDegreeObservation hu₁ hu₃ B hdeg S)).result = true),
    actualPrintedLaw, FiniteLaw.pushForward_event]
  simp only [ArithmeticAttack.decision_correct B s _ (by omega : 0 < s)]
  have h := attack_correct_signed
    (RawTargetSampler.law p (by omega) hs₁ hs₃ B hdeg)
    (fun x => FiniteMontgomerySampler.jMap p (by omega) x.1)
    (actualCodomainCode hs₁ hs₃ B hdeg (geometricTarget p (by omega) hWS))
    (RawTargetSampler.componentCode p hs₁ hs₃ B hdeg)
    (fun k => genuineDegreeObservation hu₁ hu₃ B hdeg
      ((actualKernelEquiv hu₁ hu₃ B hdeg).symm k))
    p hs (by exact_mod_cast hp) hB hcut
    (RawTargetSampler.componentCode_target p (by omega) hWS hs₁ hs₃ B hdeg)
    (fun t => (RawTargetSampler.target_marginal p (by omega) hs₁ hs₃ B hdeg t).trans_le
      (Legendre.hasseInvariantLaw_mass_le p (by omega) t))
    (by
      intro k hk
      rw [genuineDegreeObservation_interior, Equiv.apply_symm_apply]
      have hd := actualKernelEquiv_degree hu₁ hu₃ B hdeg
        ((actualKernelEquiv hu₁ hu₃ B hdeg).symm k)
      rw [Equiv.apply_symm_apply] at hd
      exact hd ▸ hk)
  simpa only [RawTargetSampler.componentCode_degree] using h

/-- Any common public-key/challenge law can choose two different source
curves. The signed bound survives that exact finite averaging. -/
theorem context_gap_lower {ι : Type*} [Fintype ι] (P : FiniteLaw ι)
    (U S : ι → GenuineExperiment.Source K p)
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8*s^2 ≤ B)
    (hcut : (B : ℝ)^2 < 4*(p : ℝ)) :
    let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
    1/(1024*(s : ℝ)^3) ≤
      ∑ i, P.mass i *
        (degreeAcceptance p (by omega) (U i).a₁_zero (U i).a₃_zero B s hdeg
          (cutoff_positive hs hB) -
         targetAcceptance p (by omega) (S i).a₁_zero (S i).a₃_zero B s hdeg) := by
  dsimp only
  calc
    _ = ∑ i, P.mass i * (1/(1024*(s : ℝ)^3)) := by
      rw [← Finset.sum_mul, P.mass_sum, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (P.mass_nonneg i)
      exact signed_gap_lower p (S i).supersingular (U i).a₁_zero (U i).a₃_zero
        (S i).a₁_zero (S i).a₃_zero hs hp hB hcut

end
end IsogenyAttack.RawSamplerAttack
