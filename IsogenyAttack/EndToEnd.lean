import IsogenyAttack.PublicFullAttack
import IsogenyAttack.RawExperiments
import IsogenyAttack.HintContinuation
import IsogenyAttack.SourceEndpoint
import IsogenyAttack.TranscriptEncoding
import IsogenyAttack.PushedEncoding

/-! Final public attack theorem. Contexts contain the public key and first
challenge; arbitrary subsequent hint generation and representation randomness
can be included in the encoding channels. Only the first response is read. -/
namespace IsogenyAttack.EndToEnd

open WeierstrassCurve WeierstrassCurve.Affine TauCeti
open PublicObservation PublicFullAttack

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

/-- An actual supersingular finite-field Montgomery coefficient gives the
source used by the checked raw-isogeny experiments. -/
def source (hp : 3 < p) (a : FiniteMontgomerySampler.Parameters (K := K) p) :
    GenuineExperiment.Source K p where
  curve := RawTargetSampler.targetCurve p a
  elliptic := inferInstance
  supersingular := (FiniteMontgomerySampler.coefficient_isSupersingular_iff p
    (by omega) a.val a.property.1).mpr a.property.2
  a₁_zero := rfl
  a₃_zero := rfl

variable {ι : Type*} [Fintype ι]

def degreeObservation (hp : 3 < p)
    (A : ι → FiniteMontgomerySampler.Parameters (K := K) p)
    (B : ℕ) (hdeg : ValidDegrees K B)
    (x : RawExperiments.DegreeOutcome (fun i => source p hp (A i)) B 1) : Option ℕ :=
  SourceEndpoint.sourceObservation (source p hp (A x.1)).a₁_zero
    (source p hp (A x.1)).a₃_zero B hdeg (FiniteLaw.firstHint 1 (by decide) x.2)

def targetObservation (hp : 3 < p)
    (A : ι → FiniteMontgomerySampler.Parameters (K := K) p)
    (B : ℕ) (hdeg : ValidDegrees K B)
    (x : RawExperiments.TargetOutcome (fun i => source p hp (A i)) B 1) : Option ℕ :=
  RawTargetSampler.observedDegree p (source p hp (A x.1)).a₁_zero
    (source p hp (A x.1)).a₃_zero B hdeg (FiniteLaw.firstHint 1 (by decide) x.2)

/-- Exact public acceptance difference after the common context, raw
isogenies, arbitrary valid continuations and randomized representations. -/
def signedGap (P : FiniteLaw ι) (hp : 3 < p)
    (A X : ι → FiniteMontgomerySampler.Parameters (K := K) p)
    (B s : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B)
    (E : PolynomialDegreeDecoder)
    (CU : EncodingChannel E (degreeObservation p hp A B hdeg))
    (CS : EncodingChannel E (targetObservation p hp X B hdeg)) : ℝ :=
  let U i := source p hp (A i)
  let S i := source p hp (X i)
  letI := RawExperiments.degreeFintype U hp B 1 hdeg
  letI := RawExperiments.targetFintype S hp B 1 hdeg
  acceptance (RawExperiments.degreeLaw P U hp B 1 hdeg hB)
    E (degreeObservation p hp A B hdeg) CU B s -
  acceptance (RawExperiments.targetLaw P S hp B 1 hdeg)
    E (targetObservation p hp X B hdeg) CS B s

theorem strict_raw_gap_le_signedGap (P : FiniteLaw ι) (hp : 3 < p)
    (A X : ι → FiniteMontgomerySampler.Parameters (K := K) p)
    (B s : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) (hs : 0 < s)
    (E : PolynomialDegreeDecoder)
    (CU : EncodingChannel E (degreeObservation p hp A B hdeg))
    (CS : EncodingChannel E (targetObservation p hp X B hdeg)) :
    RawExperiments.signedGap P (fun i => source p hp (A i))
        (fun i => source p hp (X i)) hp B s 1 hdeg hB (by decide) ≤
      signedGap p P hp A X B s hdeg hB E CU CS := by
  letI := RawExperiments.degreeFintype (fun i => source p hp (A i)) hp B 1 hdeg
  letI := RawExperiments.targetFintype (fun i => source p hp (X i)) hp B 1 hdeg
  unfold signedGap
  dsimp only
  rw [acceptance_eq _ _ _ _ _ _ hs, acceptance_eq _ _ _ _ _ _ hs]
  unfold RawExperiments.signedGap
  apply sub_le_sub
  · apply FiniteLaw.eventMass_mono
    intro x hx
    have hh : publicTest B s (RawDegreeGeometry.observation
        (source p hp (A x.1)).a₁_zero (source p hp (A x.1)).a₃_zero B hdeg
        (FiniteLaw.firstHint 1 (by decide) x.2)) = true := by
      simpa only [RawExperiments.degreeEvent, ArithmeticAttack.decision_correct B s _ hs,
        RawDegreeGeometry.observation_eq_genuineDegreeObservation] using hx
    exact SourceEndpoint.strict_accept_implies_source _ _ B hdeg _ (publicTest B s) rfl hh
  · apply le_of_eq
    apply FiniteLaw.eventMass_congr
    intro x
    simp only [targetObservation, RawExperiments.targetEvent,
      ArithmeticAttack.decision_correct B s _ hs]

/-- The principal finite certificate: a signed inverse-cubic distinguishing
gap and polynomial charged work of the public decoder-plus-test. The response
cutoff is exactly the source's rounded power of two. The two source curves are
actual supersingular Montgomery equations over the constructed p²-element
field and may differ arbitrarily with the common public context. -/
theorem full_attack_certificate (P : FiniteLaw ι)
    (A X : ι → FiniteMontgomerySampler.Parameters (K := K) p)
    {s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8*s^2 ≤ ResponseCutoff.bound p)
    (E : PolynomialDegreeDecoder)
    (CU : EncodingChannel E (degreeObservation p (by omega) A (ResponseCutoff.bound p)
      (validDegrees_of_cutoff p (ResponseCutoff.bound p) hp
        (ResponseCutoff.bound_sq_lt_four_mul_real p (by omega)))))
    (CS : EncodingChannel E (targetObservation p (by omega) X (ResponseCutoff.bound p)
      (validDegrees_of_cutoff p (ResponseCutoff.bound p) hp
        (ResponseCutoff.bound_sq_lt_four_mul_real p (by omega))))) :
    (1/(1024*(s : ℝ)^3) ≤
      signedGap p P (by omega) A X (ResponseCutoff.bound p) s
        (validDegrees_of_cutoff p (ResponseCutoff.bound p) hp
          (ResponseCutoff.bound_sq_lt_four_mul_real p (by omega)))
        (ResponseCutoff.bound_pos p) E CU CS) ∧
    (∀ D : Option (List Bool),
      (run E (ResponseCutoff.bound p) s D).work ≤
        (E.coefficient + 8192*(E.coefficient+1)^2 + 2) *
        ((ResponseCutoff.bound p).size + s.size + (D.map List.length).getD 0 + 1)^
          (2*(E.exponent+1))) := by
  constructor
  · exact (RawExperiments.signedGap_lower P _ _ hs hp hB
      (ResponseCutoff.bound_sq_lt_four_mul_real p (by omega)) (by decide)).trans
      (strict_raw_gap_le_signedGap p P _ A X _ s _ _ (by omega) E CU CS)
  · exact run_work_polynomial E (ResponseCutoff.bound p) s

end
end IsogenyAttack.EndToEnd
