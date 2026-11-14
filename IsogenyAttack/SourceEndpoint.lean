import IsogenyAttack.RawDegreeGeometry
import IsogenyAttack.RawSamplerAttack

/-! The literal Algorithm 5 endpoint: only cyclic-component degree B has a
zero complementary degree. Valid noncyclic raw degree-B outcomes are retained. -/
namespace IsogenyAttack.SourceEndpoint

open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
    {W : Affine K} [W.IsElliptic]

theorem component_degree_le_raw (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : RawDegreeSampler.Outcome W B) :
    (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree ≤ φ.1.val := by
  rw [RawDegreeGeometry.component_degree_code]
  have h := (actualKernelEquiv ha₁ ha₃ B hdeg (RawDegreeSampler.kernel W φ)).val.cyclicDegree_le_degree
  rwa [actualKernelEquiv_degree] at h

theorem component_degree_le_cutoff (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : RawDegreeSampler.Outcome W B) :
    (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree ≤ B :=
  (component_degree_le_raw ha₁ ha₃ B hdeg φ).trans (Finset.mem_Icc.mp φ.1.property).2

/-- Reject exactly the zero-complementary-degree case, retaining every cyclic
component of degree strictly less than B, including those from raw degree B. -/
def sourceObservation (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : RawDegreeSampler.Outcome W B) : Option ℕ :=
  if (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree < B then
    some (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree
  else none

theorem sourceObservation_eq_some (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : RawDegreeSampler.Outcome W B)
    (hC : (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree < B) :
    sourceObservation ha₁ ha₃ B hdeg φ =
      some (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree := by
  simp only [sourceObservation, hC, ↓reduceIte]

theorem sourceObservation_eq_none_iff (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : RawDegreeSampler.Outcome W B) :
    sourceObservation ha₁ ha₃ B hdeg φ = none ↔
      (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree = B := by
  have h := component_degree_le_cutoff ha₁ ha₃ B hdeg φ
  simp only [sourceObservation, ite_eq_right_iff, Option.some_ne_none, imp_false, not_lt]
  omega

theorem sourceObservation_interior (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : RawDegreeSampler.Outcome W B)
    (hφ : φ.1.val < B) :
    sourceObservation ha₁ ha₃ B hdeg φ =
      some (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree :=
  sourceObservation_eq_some ha₁ ha₃ B hdeg φ
    ((component_degree_le_raw ha₁ ha₃ B hdeg φ).trans_lt hφ)

/-- Pointwise inclusion of the old accepting event in the literal source
accepting event; usable directly inside a joint context experiment. -/
theorem strict_accept_implies_source (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : RawDegreeSampler.Outcome W B)
    (test : Option ℕ → Bool) (hfail : test none = false)
    (h : test (RawDegreeGeometry.observation ha₁ ha₃ B hdeg φ) = true) :
    test (sourceObservation ha₁ ha₃ B hdeg φ) = true := by
  by_cases hφ : φ.1.val < B
  · simp only [RawDegreeGeometry.observation, hφ, ↓reduceIte] at h
    rwa [sourceObservation_interior ha₁ ha₃ B hdeg φ hφ]
  · simp only [RawDegreeGeometry.observation, hφ, ↓reduceIte, hfail, Bool.false_eq_true] at h

/-- The former strict raw-degree endpoint is a conservative lower bound for
every completion which retains all interior outputs and rejects failures. -/
theorem strict_event_le_completion (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) [Fintype (RawDegreeSampler.Outcome W B)]
    (P : FiniteLaw (RawDegreeSampler.Outcome W B))
    (observed : RawDegreeSampler.Outcome W B → Option ℕ)
    (hobserved : ∀ φ, φ.1.val < B → observed φ =
      some (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree)
    (test : Option ℕ → Bool) (hfail : test none = false) :
    P.eventMass (fun φ => test (RawDegreeGeometry.observation ha₁ ha₃ B hdeg φ) = true) ≤
      P.eventMass (fun φ => test (observed φ) = true) := by
  apply P.eventMass_mono
  intro φ h
  by_cases hφ : φ.1.val < B
  · simp only [RawDegreeGeometry.observation, hφ, ↓reduceIte] at h
    rwa [hobserved φ hφ]
  · simp only [RawDegreeGeometry.observation, hφ, ↓reduceIte, hfail, Bool.false_eq_true] at h

theorem strict_event_le_source (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) [Fintype (RawDegreeSampler.Outcome W B)]
    (P : FiniteLaw (RawDegreeSampler.Outcome W B))
    (test : Option ℕ → Bool) (hfail : test none = false) :
    P.eventMass (fun φ => test (RawDegreeGeometry.observation ha₁ ha₃ B hdeg φ) = true) ≤
      P.eventMass (fun φ => test (sourceObservation ha₁ ha₃ B hdeg φ) = true) :=
  strict_event_le_completion ha₁ ha₃ B hdeg P _
    (sourceObservation_interior ha₁ ha₃ B hdeg) test hfail

/-- Assigning any output to the sole invalid cyclic-degree-B endpoint can
only increase acceptance relative to the explicit failure completion. -/
theorem source_event_le_completion (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) [Fintype (RawDegreeSampler.Outcome W B)]
    (P : FiniteLaw (RawDegreeSampler.Outcome W B))
    (observed : RawDegreeSampler.Outcome W B → Option ℕ)
    (hobserved : ∀ φ, (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree < B →
      observed φ = some (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree)
    (test : Option ℕ → Bool) (hfail : test none = false) :
    P.eventMass (fun φ => test (sourceObservation ha₁ ha₃ B hdeg φ) = true) ≤
      P.eventMass (fun φ => test (observed φ) = true) := by
  apply P.eventMass_mono
  intro φ h
  by_cases hφ : (RawDegreeGeometry.component ha₁ ha₃ B hdeg φ).degree < B
  · simp only [sourceObservation, hφ, ↓reduceIte] at h
    rwa [hobserved φ hφ]
  · simp only [sourceObservation, hφ, ↓reduceIte, hfail, Bool.false_eq_true] at h

variable (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

def degreeAcceptance (hp : 3 < p) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B s : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) : ℝ :=
  letI := RawDegreeSampler.outcomeFintype ha₁ ha₃ B hdeg (NeZero.ne (2 : K))
    (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)
  (RawDegreeSampler.law ha₁ ha₃ B hdeg hB (NeZero.ne (2 : K))
    (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)).eventMass
    (fun φ => (ArithmeticAttack.decision B s (sourceObservation ha₁ ha₃ B hdeg φ)).result = true)

omit [Fact p.Prime] [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K] in
theorem degreeAcceptance_le_source (hp : 3 < p) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B s : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) :
    RawSamplerAttack.degreeAcceptance p hp ha₁ ha₃ B s hdeg hB ≤
      degreeAcceptance p hp ha₁ ha₃ B s hdeg hB := by
  let := RawDegreeSampler.outcomeFintype ha₁ ha₃ B hdeg (NeZero.ne (2 : K))
    (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)
  unfold RawSamplerAttack.degreeAcceptance degreeAcceptance
  simp_rw [← RawDegreeGeometry.observation_eq_genuineDegreeObservation]
  exact strict_event_le_source ha₁ ha₃ B hdeg _
    (fun d => (ArithmeticAttack.decision B s d).result)
    (by simp [ArithmeticAttack.decision, BitComplexity.testBitsOption])

/-- The original quantitative gap remains valid after retaining all valid
raw-degree-B outcomes. Only cyclic component degree B is failure-completed. -/
theorem signed_gap_lower {WS : Affine K} [WS.IsElliptic]
    (hWS : WS.IsSupersingular p)
    (hu₁ : W.a₁ = 0) (hu₃ : W.a₃ = 0) (hs₁ : WS.a₁ = 0) (hs₃ : WS.a₃ = 0)
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ)) :
    let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
    1 / (1024 * (s : ℝ) ^ 3) ≤
      degreeAcceptance p (by omega) hu₁ hu₃ B s hdeg (cutoff_positive hs hB) -
        RawSamplerAttack.targetAcceptance p (by omega) hs₁ hs₃ B s hdeg := by
  dsimp only
  exact (RawSamplerAttack.signed_gap_lower p hWS hu₁ hu₃ hs₁ hs₃ hs hp hB hcut).trans
    (sub_le_sub_right (degreeAcceptance_le_source p (by omega) hu₁ hu₃ B s
      (validDegrees_of_cutoff p B hp hcut) (cutoff_positive hs hB)) _)

/-- In the actual power-of-two cutoff, zero complementary degree is exactly
the cyclic-component endpoint. A raw degree-B map with smaller cyclic degree
does not satisfy this condition. -/
theorem zero_complement_iff {e n d : ℕ} (hd : 0 < d) (hC : 2 ^ n * d ≤ 2 ^ e) :
    2 ^ (e - n) - d = 0 ↔ 2 ^ n * d = 2 ^ e := by
  have hpowle : 2 ^ n ≤ 2 ^ n * d := Nat.le_mul_of_pos_right _ hd
  have hn : n ≤ e := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (hpowle.trans hC)
  have he : 2 ^ n * 2 ^ (e - n) = 2 ^ e := by
    rw [← pow_add, Nat.add_sub_of_le hn]
  have hle : d ≤ 2 ^ (e - n) := Nat.le_of_mul_le_mul_left (by rwa [he]) (pow_pos (by decide) n)
  rw [Nat.sub_eq_zero_iff_le]
  constructor
  · intro h
    rw [Nat.le_antisymm hle h, he]
  · intro h
    have hdEq : d = 2 ^ (e - n) := Nat.eq_of_mul_eq_mul_left (pow_pos (by decide) n)
      (h.trans he.symm)
    exact hdEq.ge

end
end IsogenyAttack.SourceEndpoint
