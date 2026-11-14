import IsogenyAttack.RawSamplerAttack
import IsogenyAttack.RawDegreeGeometry
import IsogenyAttack.RawTargetGeometry
import IsogenyAttack.MontgomeryMorphismDescent

/-! The public adversary, including failure and randomized representations.
Representation channels are required only to decode to the genuine public
isogeny's degree, as in Definition 2.11. No probability bound is an input. -/
namespace IsogenyAttack.PublicFullAttack

open WeierstrassCurve WeierstrassCurve.Affine TauCeti
open PublicObservation BitComplexity
open scoped BigOperators

/-- A protocol failure is separate from an invalid representation string. -/
def decoded (E : PolynomialDegreeDecoder) (D : Option (List Bool)) : Option ℕ :=
  D.bind E.degree

def run (E : PolynomialDegreeDecoder) (B s : ℕ)
    (D : Option (List Bool)) : BitComplexity.Computation Bool :=
  match D with
  | none => ⟨false, 1⟩
  | some D => program E B.bits s.bits D

theorem run_correct (E : PolynomialDegreeDecoder) (B s : ℕ)
    (hs : 0 < s) (D : Option (List Bool)) :
    (run E B s D).result = publicTest B s (decoded E D) := by
  cases D with
  | none => simp [run, decoded, publicTest]
  | some D =>
    simpa only [run, decoded, Option.bind_some, value_bits] using
      program_correct E B.bits s.bits D (by simpa using hs)

/-- A finite random representation channel. Its only semantic condition is
correct degree decoding; this permits arbitrary randomized representations. -/
structure EncodingChannel {α : Type*} (E : PolynomialDegreeDecoder)
    (degree : α → Option ℕ) where
  coins : α → Type
  finite : ∀ a, Fintype (coins a)
  law : ∀ a, @FiniteLaw (coins a) (finite a)
  encode : ∀ a, coins a → Option (List Bool)
  valid : ∀ a r, decoded E (encode a r) = degree a

attribute [instance] EncodingChannel.finite

noncomputable def acceptance {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E : PolynomialDegreeDecoder) (degree : α → Option ℕ)
    (C : EncodingChannel E degree) (B s : ℕ) : ℝ :=
  (P.dependentBind C.coins C.law).eventMass
    (fun x => (run E B s (C.encode x.1 x.2)).result = true)

theorem acceptance_eq {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E : PolynomialDegreeDecoder) (degree : α → Option ℕ)
    (C : EncodingChannel E degree) (B s : ℕ) (hs : 0 < s) :
    acceptance P E degree C B s = P.eventMass (fun x => publicTest B s (degree x) = true) := by
  unfold acceptance
  simp_rw [run_correct E B s hs]
  exact P.dependentBind_degree_observation C.coins C.law degree
    (fun x => decoded E (C.encode x.1 x.2)) (publicTest B s) C.valid

/-- The full charged work, including decoding and protocol failure, is
polynomial in the public input length. -/
theorem run_work_polynomial (E : PolynomialDegreeDecoder) (B s : ℕ)
    (D : Option (List Bool)) :
    (run E B s D).work ≤
      (E.coefficient + 8192*(E.coefficient+1)^2 + 2) *
      (B.size + s.size + (D.map List.length).getD 0 + 1)^(2*(E.exponent+1)) := by
  cases D with
  | some D =>
    simpa only [run, Option.map_some, Option.getD_some, ← Nat.size_eq_bits_len] using
      program_work_polynomial E B.bits s.bits D
  | none =>
    simp only [run, Option.map_none, Option.getD_none, add_zero]
    have hp : 1 ≤ (B.size + s.size + 1)^(2*(E.exponent+1)) :=
      one_le_pow₀ (by omega)
    nlinarith

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
    {WU WS : Affine K} [WU.IsElliptic] [WS.IsElliptic]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

/-- Finite correctness theorem for the actual raw samplers and public
decoder. The observed optional degrees are genuine cyclic-component degrees,
not freely specified observations. The degree-first endpoint and empty
target fibers use the explicit failure completion. -/
theorem finite_attack (hWS : WS.IsSupersingular p)
    (hu₁ : WU.a₁ = 0) (hu₃ : WU.a₃ = 0) (hs₁ : WS.a₁ = 0) (hs₃ : WS.a₃ = 0)
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8*s^2 ≤ B)
    (hcut : (B : ℝ)^2 < 4*(p : ℝ)) (E : PolynomialDegreeDecoder)
    (CU : EncodingChannel E (RawDegreeGeometry.observation hu₁ hu₃ B
      (validDegrees_of_cutoff p B hp hcut)))
    (CS : EncodingChannel E (RawTargetSampler.observedDegree p hs₁ hs₃ B
      (validDegrees_of_cutoff p B hp hcut))) :
    let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
    let h2 := NeZero.ne (2 : K)
    let h3 := Legendre.small_natCast_ne_zero (K := K) p (k := 3) (by decide) (by omega)
    letI := RawDegreeSampler.outcomeFintype hu₁ hu₃ B hdeg h2 h3
    letI := RawTargetSampler.outcomeFintype p (by omega) hs₁ hs₃ B hdeg
    1/(1024*(s : ℝ)^3) ≤
      acceptance (RawDegreeSampler.law hu₁ hu₃ B hdeg (cutoff_positive hs hB) h2 h3)
        E (RawDegreeGeometry.observation hu₁ hu₃ B hdeg) CU B s -
      acceptance (RawTargetSampler.law p (by omega) hs₁ hs₃ B hdeg)
        E (RawTargetSampler.observedDegree p hs₁ hs₃ B hdeg) CS B s := by
  dsimp only
  let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
  letI := RawDegreeSampler.outcomeFintype hu₁ hu₃ B hdeg (NeZero.ne (2 : K))
    (Legendre.small_natCast_ne_zero p (k := 3) (by decide) (by omega))
  letI := RawTargetSampler.outcomeFintype p (by omega) hs₁ hs₃ B hdeg
  rw [acceptance_eq _ _ _ _ _ _ (by omega), acceptance_eq _ _ _ _ _ _ (by omega)]
  simp_rw [RawDegreeGeometry.observation_eq_genuineDegreeObservation]
  have h := RawSamplerAttack.signed_gap_lower p hWS hu₁ hu₃ hs₁ hs₃ hs hp hB hcut
  simpa only [RawSamplerAttack.degreeAcceptance, RawSamplerAttack.targetAcceptance,
    ArithmeticAttack.decision_correct B s _ (by omega : 0 < s)] using h

/-- The source's literal response cutoff supplies the numeric cutoff
condition; the user of the theorem need not assume a geometric mass bound. -/
theorem source_cutoff (hp : 49 ≤ p) :
    (ResponseCutoff.bound p : ℝ)^2 < 4*(p : ℝ) :=
  ResponseCutoff.bound_sq_lt_four_mul_real p (by omega)

end
end IsogenyAttack.PublicFullAttack
