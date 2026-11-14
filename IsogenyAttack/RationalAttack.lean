import IsogenyAttack.RationalRawSampler
import IsogenyAttack.SourceEndpoint
import IsogenyAttack.PublicFullAttack

/-! The quantitative attack on the concrete rational-map experiments over
the quadratic finite field. Both probability laws are the actual rational-map
laws; their identification with geometric laws is proved, not assumed. -/

namespace IsogenyAttack.RationalAttack

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (p : ℕ) [Fact p.Prime] [CharP K p]
  [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

abbrev Parameter := FiniteMontgomerySampler.Parameters (K := K) p

/-- The literal source observation, retaining valid noncyclic raw degree-B
outcomes and rejecting exactly cyclic-component degree B. -/
def degreeObservation (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : Parameter (K := K) p) (B : ℕ) (hdeg : ValidDegrees K B)
    (φ : RationalRawSampler.Outcome p a B) : Option ℕ :=
  SourceEndpoint.sourceObservation rfl rfl B hdeg
    (RationalRawSampler.outcomeEquivRaw p hp hp4 a B hdeg φ)

/-- The target experiment observes the genuine cyclic component's degree;
failure in an empty connecting fiber remains failure. -/
def targetObservation (hp : 3 < p) (hp4 : p % 4 = 3)
    (x : Parameter (K := K) p) (B : ℕ) (hdeg : ValidDegrees K B)
    (φ : RationalMapSampler.QuadraticTargetOutcome p x B) : Option ℕ :=
  RawTargetSampler.observedDegree p rfl rfl B hdeg
    (RationalMapSampler.quadraticTargetOutcomeEquiv p (by omega) hp4 x B hdeg φ)

def degreeAcceptance (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : Parameter (K := K) p) (B s : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) : ℝ :=
  letI := RationalRawSampler.outcomeFintype p hp hp4 a B hdeg
  (RationalRawSampler.law p hp hp4 a B hdeg hB).eventMass
    (fun φ => publicTest B s (degreeObservation p hp hp4 a B hdeg φ) = true)

def targetAcceptance (hp : 3 < p) (hp4 : p % 4 = 3)
    (x : Parameter (K := K) p) (B s : ℕ) (hdeg : ValidDegrees K B) : ℝ :=
  letI := RationalMapSampler.quadraticTargetFintype p hp hp4 x B hdeg
  (RationalMapSampler.quadraticTargetLaw p hp hp4 x B hdeg).eventMass
    (fun φ => publicTest B s (targetObservation p hp hp4 x B hdeg φ) = true)

/-- Exact event transfer for the source-completed degree experiment. -/
theorem degreeAcceptance_eq_source (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : Parameter (K := K) p) (B s : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B)
    (hs : 0 < s) :
    degreeAcceptance p hp hp4 a B s hdeg hB =
      SourceEndpoint.degreeAcceptance (W := (RationalRawSampler.source p a).toAffine)
        p hp rfl rfl B s hdeg hB := by
  let := RationalRawSampler.geometricOutcomeFintype p hp a B hdeg
  let := RationalRawSampler.outcomeFintype p hp hp4 a B hdeg
  exact (RationalRawSampler.law_event p hp hp4 a B hdeg hB
    (fun φ => publicTest B s
      (SourceEndpoint.sourceObservation (W := (RationalRawSampler.source p a).toAffine)
        rfl rfl B hdeg φ) = true)).trans (by
    simp only [SourceEndpoint.degreeAcceptance, ArithmeticAttack.decision_correct B s _ hs])

/-- Exact event transfer for the target-first rational-map experiment. -/
theorem targetAcceptance_eq_raw (hp : 3 < p) (hp4 : p % 4 = 3)
    (x : Parameter (K := K) p) (B s : ℕ) (hdeg : ValidDegrees K B) (hs : 0 < s) :
    targetAcceptance p hp hp4 x B s hdeg =
      RawSamplerAttack.targetAcceptance (WS := (RationalRawSampler.source p x).toAffine)
        p hp rfl rfl B s hdeg := by
  let := RationalMapSampler.quadraticTargetFintype p hp hp4 x B hdeg
  let := RawTargetSampler.outcomeFintype
    (W := (RationalRawSampler.source p x).toAffine) p hp rfl rfl B hdeg
  exact (RationalMapSampler.quadraticTargetLaw_event p hp hp4 x B hdeg
    (fun φ => publicTest B s
      (RawTargetSampler.observedDegree (W := (RationalRawSampler.source p x).toAffine)
        p rfl rfl B hdeg φ) = true)).trans (by
    simp only [RawSamplerAttack.targetAcceptance, ArithmeticAttack.decision_correct B s _ hs])

/-- The explicit inverse-cubic signed gap for the two actual rational-map
laws over `𝔽_(p²)`, for any supersingular public and challenge Montgomery
parameters. Field descent, map multiplicities and sampler probabilities are
theorems upstream; none is a premise here. -/
theorem signed_gap_lower (a x : Parameter (K := K) p) (hp4 : p % 4 = 3)
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ)) :
    let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
    1 / (1024 * (s : ℝ) ^ 3) ≤
      degreeAcceptance p (by omega) hp4 a B s hdeg (cutoff_positive hs hB) -
        targetAcceptance p (by omega) hp4 x B s hdeg := by
  dsimp only
  rw [degreeAcceptance_eq_source p (by omega) hp4 a B s _ _ (by omega),
    targetAcceptance_eq_raw p (by omega) hp4 x B s _ (by omega)]
  exact SourceEndpoint.signed_gap_lower p
    (RationalRawSampler.source_supersingular p (by omega) x)
    rfl rfl rfl rfl hs hp hB hcut

/-- Arbitrary valid randomized public encodings preserve the same signed
gap for the executable decoder-plus-binary-test adversary. -/
theorem public_finite_attack (a x : Parameter (K := K) p) (hp4 : p % 4 = 3)
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ))
    (E : PublicObservation.PolynomialDegreeDecoder)
    (CU : PublicFullAttack.EncodingChannel E (degreeObservation p (by omega) hp4 a B
      (validDegrees_of_cutoff p B hp hcut)))
    (CS : PublicFullAttack.EncodingChannel E (targetObservation p (by omega) hp4 x B
      (validDegrees_of_cutoff p B hp hcut))) :
    let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
    letI := RationalRawSampler.outcomeFintype p (by omega) hp4 a B hdeg
    letI := RationalMapSampler.quadraticTargetFintype p (by omega) hp4 x B hdeg
    1 / (1024 * (s : ℝ) ^ 3) ≤
      PublicFullAttack.acceptance
        (RationalRawSampler.law p (by omega) hp4 a B hdeg (cutoff_positive hs hB))
        E (degreeObservation p (by omega) hp4 a B hdeg) CU B s -
      PublicFullAttack.acceptance
        (RationalMapSampler.quadraticTargetLaw p (by omega) hp4 x B hdeg)
        E (targetObservation p (by omega) hp4 x B hdeg) CS B s := by
  dsimp only
  let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
  let := RationalRawSampler.outcomeFintype p (by omega) hp4 a B hdeg
  let := RationalMapSampler.quadraticTargetFintype p (by omega) hp4 x B hdeg
  rw [PublicFullAttack.acceptance_eq _ _ _ _ _ _ (by omega),
    PublicFullAttack.acceptance_eq _ _ _ _ _ _ (by omega)]
  exact signed_gap_lower p a x hp4 hs hp hB hcut

end
end IsogenyAttack.RationalAttack
