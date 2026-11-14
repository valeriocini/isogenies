import IsogenyAttack.RawSamplerAttack

/-!
Joint public-context experiments on raw morphisms. The degree-first and
target-first sources may differ, and any positive number of fresh hints is
sampled after the common context. The distinguisher reads the first hint.
-/
namespace IsogenyAttack.RawExperiments

open WeierstrassCurve WeierstrassCurve.Affine
open scoped BigOperators
noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    {ι : Type*} [Fintype ι]

abbrev DegreeOutcome (U : ι → GenuineExperiment.Source K p) (B q : ℕ) :=
  Σ i, FiniteLaw.HintTuple.{_,0} (RawDegreeSampler.Outcome (U i).curve B) q

abbrev TargetOutcome (S : ι → GenuineExperiment.Source K p) (B q : ℕ) :=
  Σ i, FiniteLaw.HintTuple.{_,0} (RawTargetSampler.Outcome (W := (S i).curve) p B) q

@[reducible] def degreeFintype (U : ι → GenuineExperiment.Source K p)
    (hp : 3 < p) (B q : ℕ) (hdeg : ValidDegrees K B) :
    Fintype (DegreeOutcome U B q) := by
  letI : ∀ i, Fintype (RawDegreeSampler.Outcome (U i).curve B) := fun i =>
    RawDegreeSampler.outcomeFintype (U i).a₁_zero (U i).a₃_zero B hdeg
      (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (by decide) hp)
  exact inferInstanceAs (Fintype (Σ i,
    FiniteLaw.HintTuple.{_,0} (RawDegreeSampler.Outcome (U i).curve B) q))

@[reducible] def targetFintype (S : ι → GenuineExperiment.Source K p)
    (hp : 3 < p) (B q : ℕ) (hdeg : ValidDegrees K B) :
    Fintype (TargetOutcome S B q) := by
  letI : ∀ i, Fintype (RawTargetSampler.Outcome (W := (S i).curve) p B) := fun i =>
    RawTargetSampler.outcomeFintype p hp (S i).a₁_zero (S i).a₃_zero B hdeg
  exact inferInstanceAs (Fintype (Σ i,
    FiniteLaw.HintTuple.{_,0} (RawTargetSampler.Outcome (W := (S i).curve) p B) q))

/-- Draw the public context once, then q independent degree-first raw hints
from its own source curve. -/
def degreeLaw (P : FiniteLaw ι) (U : ι → GenuineExperiment.Source K p)
    (hp : 3 < p) (B q : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) :
    @FiniteLaw (DegreeOutcome U B q) (degreeFintype U hp B q hdeg) := by
  letI : ∀ i, Fintype (RawDegreeSampler.Outcome (U i).curve B) := fun i =>
    RawDegreeSampler.outcomeFintype (U i).a₁_zero (U i).a₃_zero B hdeg
      (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (by decide) hp)
  exact P.dependentBind
    (fun i => FiniteLaw.HintTuple.{_,0} (RawDegreeSampler.Outcome (U i).curve B) q)
    (fun i => (RawDegreeSampler.law (U i).a₁_zero (U i).a₃_zero B hdeg hB
      (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (by decide) hp)).repeatHints q)

/-- Draw the same public-context law, then q independent target-first raw
hints from the possibly different challenge source curve. -/
def targetLaw (P : FiniteLaw ι) (S : ι → GenuineExperiment.Source K p)
    (hp : 3 < p) (B q : ℕ) (hdeg : ValidDegrees K B) :
    @FiniteLaw (TargetOutcome S B q) (targetFintype S hp B q hdeg) := by
  letI : ∀ i, Fintype (RawTargetSampler.Outcome (W := (S i).curve) p B) := fun i =>
    RawTargetSampler.outcomeFintype p hp (S i).a₁_zero (S i).a₃_zero B hdeg
  exact P.dependentBind
    (fun i => FiniteLaw.HintTuple.{_,0} (RawTargetSampler.Outcome (W := (S i).curve) p B) q)
    (fun i => (RawTargetSampler.law p hp (S i).a₁_zero (S i).a₃_zero B hdeg).repeatHints q)

def degreeEvent (U : ι → GenuineExperiment.Source K p) (B s q : ℕ)
    (hdeg : ValidDegrees K B) (hq : 0 < q) (x : DegreeOutcome U B q) : Prop :=
  (ArithmeticAttack.decision B s (genuineDegreeObservation
    (U x.1).a₁_zero (U x.1).a₃_zero B hdeg
    (RawDegreeSampler.kernel (U x.1).curve (FiniteLaw.firstHint q hq x.2)))).result = true

def targetEvent (S : ι → GenuineExperiment.Source K p) (B s q : ℕ)
    (hdeg : ValidDegrees K B) (hq : 0 < q) (x : TargetOutcome S B q) : Prop :=
  (ArithmeticAttack.decision B s (RawTargetSampler.observedDegree p
    (S x.1).a₁_zero (S x.1).a₃_zero B hdeg (FiniteLaw.firstHint q hq x.2))).result = true

/-- The actual signed difference of the two complete joint experiments. -/
def signedGap (P : FiniteLaw ι) (U S : ι → GenuineExperiment.Source K p)
    (hp : 3 < p) (B s q : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) (hq : 0 < q) : ℝ :=
  letI := degreeFintype U hp B q hdeg
  letI := targetFintype S hp B q hdeg
  (degreeLaw P U hp B q hdeg hB).eventMass (degreeEvent U B s q hdeg hq) -
    (targetLaw P S hp B q hdeg).eventMass (targetEvent S B s q hdeg hq)

/-- The context is averaged before taking absolute values; q fresh hints
have exactly the one-hint gap because the decision reads only their first. -/
theorem signedGap_eq_context_sum (P : FiniteLaw ι)
    (U S : ι → GenuineExperiment.Source K p)
    (hp : 3 < p) (B s q : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) (hq : 0 < q) :
    signedGap P U S hp B s q hdeg hB hq =
      ∑ i, P.mass i *
        (RawSamplerAttack.degreeAcceptance p hp (U i).a₁_zero (U i).a₃_zero B s hdeg hB -
         RawSamplerAttack.targetAcceptance p hp (S i).a₁_zero (S i).a₃_zero B s hdeg) := by
  letI : ∀ i, Fintype (RawDegreeSampler.Outcome (U i).curve B) := fun i =>
    RawDegreeSampler.outcomeFintype (U i).a₁_zero (U i).a₃_zero B hdeg
      (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (by decide) hp)
  letI : ∀ i, Fintype (RawTargetSampler.Outcome (W := (S i).curve) p B) := fun i =>
    RawTargetSampler.outcomeFintype p hp (S i).a₁_zero (S i).a₃_zero B hdeg
  unfold signedGap degreeLaw targetLaw
  rw [FiniteLaw.dependentBind_eventMass, FiniteLaw.dependentBind_eventMass,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [degreeEvent, targetEvent]
  rw [FiniteLaw.repeatHints_first_event
    (RawDegreeSampler.law (U i).a₁_zero (U i).a₃_zero B hdeg hB
      (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (by decide) hp)) q hq
    (fun φ => (ArithmeticAttack.decision B s (genuineDegreeObservation
      (U i).a₁_zero (U i).a₃_zero B hdeg (RawDegreeSampler.kernel (U i).curve φ))).result = true),
    FiniteLaw.repeatHints_first_event
      (RawTargetSampler.law p hp (S i).a₁_zero (S i).a₃_zero B hdeg) q hq
      (fun φ => (ArithmeticAttack.decision B s (RawTargetSampler.observedDegree p
        (S i).a₁_zero (S i).a₃_zero B hdeg φ)).result = true)]
  simp only [RawSamplerAttack.degreeAcceptance, RawSamplerAttack.targetAcceptance, mul_sub]

/-- Any positive hint count, and two arbitrary genuine source families,
preserve the explicitly proved inverse-cubic advantage. -/
theorem signedGap_lower (P : FiniteLaw ι) (U S : ι → GenuineExperiment.Source K p)
    {B s q : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8*s^2 ≤ B)
    (hcut : (B : ℝ)^2 < 4*(p : ℝ)) (hq : 0 < q) :
    let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
    1/(1024*(s : ℝ)^3) ≤
      signedGap P U S (by omega) B s q hdeg (cutoff_positive hs hB) hq := by
  dsimp only
  rw [signedGap_eq_context_sum]
  exact RawSamplerAttack.context_gap_lower p P U S hs hp hB hcut

theorem signedGap_eq_one_hint (P : FiniteLaw ι)
    (U S : ι → GenuineExperiment.Source K p)
    (hp : 3 < p) (B s q : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) (hq : 0 < q) :
    signedGap P U S hp B s q hdeg hB hq =
      signedGap P U S hp B s 1 hdeg hB (by decide) := by
  rw [signedGap_eq_context_sum, signedGap_eq_context_sum]

end

noncomputable section
open scoped Classical

section Families
variable (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, IsAlgClosed (K n)]
    [∀ n, NeZero (2 : K n)] (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (p : ℕ → ℕ) [∀ n, Fact (p n).Prime] [∀ n, CharP (K n) (p n)]
    [∀ n, Algebra (ZMod (p n)) (K n)]
    [∀ n, Algebra.IsAlgebraic (ZMod (p n)) (K n)]
    (hp : ∀ n, 49 ≤ p n) (P : ∀ n, FiniteLaw (ι n))
    (U S : ∀ n, ι n → GenuineExperiment.Source (K n) (p n))
    (q : ℕ → ℕ) (hq : ∀ n, 0 < q n)

/-- Actual joint experiment gaps at the source's exact power-of-two cutoff,
with s=n+784 and any positive number q(n) of hints. -/
def familySignedGap (n : ℕ) : ℝ :=
  signedGap (P n) (U n) (S n) (by have := hp n; omega)
    (ResponseCutoff.bound (p n)) (n+784) (q n)
    (validDegrees_of_cutoff (K := K n) (p n) (ResponseCutoff.bound (p n)) (hp n)
      (ResponseCutoff.bound_sq_lt_four_mul_real (p n) (by have := hp n; omega)))
    (ResponseCutoff.bound_pos (p n)) (hq n)

/-- Only characteristic growth is assumed. The cutoff and all quantitative
attack hypotheses are derived, including their explicit eventual index. -/
theorem family_gap_lower_eventually
    (hgrowth : ∃ N : ℕ, ∀ n ≥ N, 2^n ≤ p n) :
    ∃ N : ℕ, ∀ n ≥ N,
      1/(1024*((n : ℝ)+784)^3) ≤ familySignedGap K ι p hp P U S q hq n := by
  obtain ⟨N, hN⟩ := hgrowth
  refine ⟨max N 64, fun n hn => ?_⟩
  have h64 : 64 ≤ n := (le_max_right N 64).trans hn
  have hg := (ResponseCutoff.polynomial_le_exponential n h64).trans
    (hN n ((le_max_left N 64).trans hn))
  have hB := ResponseCutoff.threshold_growth (p n) n hg
  have hcut := ResponseCutoff.bound_sq_lt_four_mul_real (p n)
    (by have := hp n; omega : 1 < p n)
  simpa only [familySignedGap, Nat.cast_add, Nat.cast_ofNat] using
    (signedGap_lower (P n) (U n) (S n) (by omega : 784 ≤ n+784)
      (hp n) hB hcut (hq n))

/-- The signed difference of the two genuine raw-isogeny experiments is
nonnegligible; no codomain map or conditional probability bound is assumed. -/
theorem family_gap_not_negligible
    (hgrowth : ∃ N : ℕ, ∀ n ≥ N, 2^n ≤ p n) :
    ¬ IsNegligible (familySignedGap K ι p hp P U S q hq) :=
  not_negligible_of_attack_bound
    (family_gap_lower_eventually K ι p hp P U S q hq hgrowth)

/-- The ordinary absolute distinguishing advantage is nonnegligible. -/
theorem family_advantage_not_negligible
    (hgrowth : ∃ N : ℕ, ∀ n ≥ N, 2^n ≤ p n) :
    ¬ IsNegligible (fun n => |familySignedGap K ι p hp P U S q hq n|) := by
  intro h
  apply family_gap_not_negligible K ι p hp P U S q hq hgrowth
  simpa only [IsNegligible, abs_abs] using h

theorem family_advantage_not_negligible_of_exponential
    (hgrowth : ∀ n, 2^n ≤ p n) :
    ¬ IsNegligible (fun n => |familySignedGap K ι p hp P U S q hq n|) :=
  family_advantage_not_negligible K ι p hp P U S q hq ⟨0, fun n _ => hgrowth n⟩

end Families
end
end IsogenyAttack.RawExperiments
