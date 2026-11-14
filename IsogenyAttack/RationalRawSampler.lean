import IsogenyAttack.RationalMapSampler
import IsogenyAttack.RationalTargetMembership

/-! The full degree-first sample space of actual rational maps over the quadratic
finite field, and its exact equivalence with the raw geometric experiment. -/
namespace IsogenyAttack.RationalRawSampler
open WeierstrassCurve WeierstrassCurve.Affine TauCeti

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
    (p : ℕ) [Fact p.Prime] [CharP K p]

abbrev Parameter := FiniteMontgomerySampler.Parameters (K := K) p
abbrev source (a : Parameter (K := K) p) := Montgomery.curve (a.val : K)

instance source_elliptic (a : Parameter (K := K) p) : (source p a).IsElliptic := by
  apply Montgomery.curve_isElliptic (NeZero.ne (2 : K))
  intro h
  exact a.property.1 ((frobeniusFixedField (K := K) p 2).subtype.injective h)

omit [IsAlgClosed K] [NeZero (2 : K)] in
theorem source_supersingular (hp : 2 < p) (a : Parameter (K := K) p) :
    (source p a).IsSupersingular p :=
  (FiniteMontgomerySampler.coefficient_isSupersingular_iff p hp a.val a.property.1).mpr
    a.property.2

/-- Rational isogenies to one concrete finite-field target, with intrinsic degree
and separability conditions; no geometric map is stored as part of the data. -/
abbrev MapsToTarget (a b : Parameter (K := K) p) (d : ℕ) :=
  {φ : Isogeny (Montgomery.curve a.val).toAffine (Montgomery.curve b.val).toAffine //
    φ.degree = d ∧ Algebra.IsSeparable φ.fieldPullback.fieldRange
      (Montgomery.curve a.val).toAffine.FunctionField}

/-- The unadorned finite-field degree-d outcome: target coefficient and rational map. -/
abbrev DegreeMaps (a : Parameter (K := K) p) (d : ℕ) :=
  Σ b : Parameter (K := K) p, MapsToTarget p a b d

/-- The complete bounded rational sample space. -/
abbrev Outcome (a : Parameter (K := K) p) (B : ℕ) :=
  Σ d : DegreeIndex B, DegreeMaps p a d.val

abbrev GeometricMapsToTarget (a b : Parameter (K := K) p) (d : ℕ) :=
  {φ : Isogeny (source p a).toAffine (source p b).toAffine //
    φ.degree = d ∧ Nat.card φ.ker = φ.degree}

abbrev TargetedGeometricDegreeMaps (a : Parameter (K := K) p) (d : ℕ) :=
  Σ b : Parameter (K := K) p, GeometricMapsToTarget p a b d

/-- The finite-field target label adds no data to a geometric raw map: the original
coefficient determines it uniquely, and actual supersingularity proves it exists. -/
def targetedEquivRaw (hp : 2 < p) (a : Parameter (K := K) p)
    (d : ℕ) [NeZero d] (hcop : Nat.Coprime p d) :
    TargetedGeometricDegreeMaps p a d ≃
      IsogenySampler.DegreeMaps (source p a).toAffine d :=
  Equiv.ofBijective
    (fun x => ⟨⟨x.1.val.val, by
      intro h
      exact x.1.property.1 ((frobeniusFixedField (K := K) p 2).subtype.injective h)⟩,
      x.2⟩)
    ⟨by
      rintro ⟨b, φ⟩ ⟨c, ψ⟩ h
      have hbc : b = c := by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : IsogenySampler.DegreeMaps (source p a).toAffine d => x.1.val) h
      subst c
      have hf : φ = ψ := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
      subst ψ
      rfl,
    by
      intro φ
      let b := RationalTargetMembership.degreeMapFiniteTarget (source p a).toAffine p hp
        (source_supersingular p hp a) hcop φ
      exact ⟨⟨b, φ.2⟩, rfl⟩⟩

@[simp] theorem targetedEquivRaw_coefficient (hp : 2 < p) (a : Parameter (K := K) p)
    (d : ℕ) [NeZero d] (hcop : Nat.Coprime p d) (φ : TargetedGeometricDegreeMaps p a d) :
    (targetedEquivRaw p hp a d hcop φ).1.val = φ.1.val.val := rfl

variable [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

/-- Base change bijects the intrinsic degree-d separable rational maps and all
geometric maps to the specified finite-field target. -/
def mapsToTargetEquiv (hp : 3 < p) (hp4 : p % 4 = 3)
    (a b : Parameter (K := K) p) (d : ℕ) :
    MapsToTarget p a b d ≃ GeometricMapsToTarget p a b d :=
  (RationalMapSampler.quadraticFieldEquiv p (by omega) hp4 a b).subtypeEquiv (by
    intro φ
    rw [IsogenySampler.card_ker_eq_degree_iff_separable,
      RationalMapSampler.quadraticFieldEquiv_degree,
      RationalMapSampler.quadraticFieldEquiv_separable_iff])

/-- Every geometric degree-d raw morphism is uniquely a rational map over the
quadratic finite field, with its original target coefficient preserved. -/
def degreeEquivRaw (hp : 3 < p) (hp4 : p % 4 = 3) (a : Parameter (K := K) p)
    (d : ℕ) [NeZero d] (hcop : Nat.Coprime p d) :
    DegreeMaps p a d ≃ IsogenySampler.DegreeMaps (source p a).toAffine d :=
  (Equiv.sigmaCongrRight (fun b => mapsToTargetEquiv p hp hp4 a b d)).trans
    (targetedEquivRaw p (by omega) a d hcop)

@[simp] theorem degreeEquivRaw_coefficient (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : Parameter (K := K) p) (d : ℕ) [NeZero d] (hcop : Nat.Coprime p d)
    (φ : DegreeMaps p a d) :
    (degreeEquivRaw p hp hp4 a d hcop φ).1.val = φ.1.val.val := rfl

omit [IsAlgClosed K] [NeZero (2 : K)] [Algebra (ZMod p) K]
    [Algebra.IsAlgebraic (ZMod p) K] in
theorem degreeIndex_coprime (B : ℕ) (hdeg : ValidDegrees K B) (d : DegreeIndex B) :
    Nat.Coprime p d.val := by
  rw [(Fact.out : p.Prime).coprime_iff_not_dvd]
  intro hd
  exact hdeg d.val (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp d.property).2
    ((CharP.cast_eq_zero_iff K p _).mpr hd)

/-- The complete bounded rational degree-first sample space is bijective to the
unadorned raw geometric sample space. No kernel or Frobenius witness is stored. -/
def outcomeEquivRaw (hp : 3 < p) (hp4 : p % 4 = 3) (a : Parameter (K := K) p)
    (B : ℕ) (hdeg : ValidDegrees K B) :
    Outcome p a B ≃ RawDegreeSampler.Outcome (source p a).toAffine B :=
  Equiv.sigmaCongrRight (fun d => by
    letI : NeZero d.val := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp d.property).1⟩
    exact degreeEquivRaw p hp hp4 a d.val (degreeIndex_coprime p B hdeg d))

@[simp] theorem outcomeEquivRaw_degreeIndex (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : Parameter (K := K) p) (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome p a B) :
    (outcomeEquivRaw p hp hp4 a B hdeg φ).1 = φ.1 := rfl

@[simp] theorem outcomeEquivRaw_coefficient (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : Parameter (K := K) p) (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome p a B) :
    (outcomeEquivRaw p hp hp4 a B hdeg φ).2.1.val = φ.2.1.val.val := rfl

@[reducible] def geometricOutcomeFintype (hp : 3 < p) (a : Parameter (K := K) p)
    (B : ℕ) (hdeg : ValidDegrees K B) :
    Fintype (RawDegreeSampler.Outcome (source p a).toAffine B) :=
  RawDegreeSampler.outcomeFintype rfl rfl B hdeg (NeZero.ne (2 : K))
    (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)

/-- Finiteness of the actual rational-map sample space is proved, not assumed. -/
@[reducible] def outcomeFintype (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : Parameter (K := K) p) (B : ℕ) (hdeg : ValidDegrees K B) :
    Fintype (Outcome p a B) := by
  letI := geometricOutcomeFintype p hp a B hdeg
  exact Fintype.ofEquiv _ (outcomeEquivRaw p hp hp4 a B hdeg).symm

@[reducible] def geometricDegreeFintype (hp : 3 < p) (a : Parameter (K := K) p)
    (B : ℕ) (hdeg : ValidDegrees K B) (d : DegreeIndex B) :
    Fintype (IsogenySampler.DegreeMaps (source p a).toAffine d.val) := by
  letI := geometricOutcomeFintype p hp a B hdeg
  exact Fintype.ofInjective
    (fun φ => (⟨d, φ⟩ : RawDegreeSampler.Outcome (source p a).toAffine B)) (by
      intro φ ψ h
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h)

@[reducible] def degreeFintype (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : Parameter (K := K) p) (B : ℕ) (hdeg : ValidDegrees K B) (d : DegreeIndex B) :
    Fintype (DegreeMaps p a d.val) := by
  letI : NeZero d.val := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp d.property).1⟩
  letI := geometricDegreeFintype p hp a B hdeg d
  exact Fintype.ofEquiv _
    (degreeEquivRaw p hp hp4 a d.val (degreeIndex_coprime p B hdeg d)).symm

omit [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K] in
theorem geometricDegree_nonempty (hp : 3 < p) (a : Parameter (K := K) p)
    (B : ℕ) (hdeg : ValidDegrees K B) (d : DegreeIndex B) :
    Nonempty (IsogenySampler.DegreeMaps (source p a).toAffine d.val) := by
  let : NeZero d.val := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp d.property).1⟩
  have hcard : Nat.card (IsogenySampler.DegreeKernel (source p a).toAffine d.val) =
      kernelCount d.val :=
    elliptic_kernel_count (W := (source p a).toAffine) rfl rfl
      (hdeg d.val (Finset.mem_Icc.mp d.property).1 (Finset.mem_Icc.mp d.property).2)
  have : Nonempty (IsogenySampler.DegreeKernel (source p a).toAffine d.val) :=
    (Nat.card_ne_zero.mp (by
      rw [hcard]
      exact ne_of_gt (kernelCount_pos (Finset.mem_Icc.mp d.property).1))).1
  exact IsogenySampler.degreeMaps_nonempty (source p a).toAffine d.val
    (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)

/-- Uniform conditional sampling at every printed degree agrees exactly with
uniform sampling over all geometric raw maps of that degree. -/
theorem degree_uniform_event (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : Parameter (K := K) p) (B : ℕ) (hdeg : ValidDegrees K B) (d : DegreeIndex B)
    (E : IsogenySampler.DegreeMaps (source p a).toAffine d.val → Prop) :
    letI : NeZero d.val := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp d.property).1⟩
    letI := geometricDegreeFintype p hp a B hdeg d
    letI := degreeFintype p hp hp4 a B hdeg d
    letI := geometricDegree_nonempty p hp a B hdeg d
    letI : Nonempty (DegreeMaps p a d.val) :=
      (degreeEquivRaw p hp hp4 a d.val (degreeIndex_coprime p B hdeg d)).nonempty
    (FiniteLaw.uniform (DegreeMaps p a d.val)).eventMass
      (fun φ => E (degreeEquivRaw p hp hp4 a d.val (degreeIndex_coprime p B hdeg d) φ)) =
      (FiniteLaw.uniform (IsogenySampler.DegreeMaps (source p a).toAffine d.val)).eventMass E := by
  let : NeZero d.val := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp d.property).1⟩
  let := geometricDegreeFintype p hp a B hdeg d
  let := degreeFintype p hp hp4 a B hdeg d
  let := geometricDegree_nonempty p hp a B hdeg d
  let : Nonempty (DegreeMaps p a d.val) :=
    (degreeEquivRaw p hp hp4 a d.val (degreeIndex_coprime p B hdeg d)).nonempty
  exact FiniteLaw.uniform_event_equiv _ E

/-- The printed degree-first law on actual finite-field rational maps. Its exact
mass formula below identifies the degree weight and uniform conditional map law. -/
def law (hp : 3 < p) (hp4 : p % 4 = 3) (a : Parameter (K := K) p)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) :
    @FiniteLaw (Outcome p a B) (outcomeFintype p hp hp4 a B hdeg) := by
  letI := geometricOutcomeFintype p hp a B hdeg
  letI := outcomeFintype p hp hp4 a B hdeg
  exact (RawDegreeSampler.law (W := (source p a).toAffine) rfl rfl B hdeg hB
    (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)).pushForward
      (outcomeEquivRaw p hp hp4 a B hdeg).symm

/-- Every rational degree-d morphism has exactly the source's printed mass. -/
theorem law_mass (hp : 3 < p) (hp4 : p % 4 = 3) (a : Parameter (K := K) p)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B) (φ : Outcome p a B) :
    letI := outcomeFintype p hp hp4 a B hdeg
    (law p hp hp4 a B hdeg hB).mass φ =
      (printedWeight φ.1.val : ℝ) / (normalizer B * 12 * (kernelCount φ.1.val : ℝ)) := by
  let := geometricOutcomeFintype p hp a B hdeg
  let := outcomeFintype p hp hp4 a B hdeg
  rw [law, FiniteLaw.pushForward_equiv_mass]
  exact RawDegreeSampler.law_mass (W := (source p a).toAffine) rfl rfl B hdeg hB
    (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)
    (outcomeEquivRaw p hp hp4 a B hdeg φ)

/-- Every event has exactly the same probability after base change; thus the
proved raw geometric distinguisher transfers to the rational-map sampler. -/
theorem law_event (hp : 3 < p) (hp4 : p % 4 = 3) (a : Parameter (K := K) p)
    (B : ℕ) (hdeg : ValidDegrees K B) (hB : 0 < B)
    (E : RawDegreeSampler.Outcome (source p a).toAffine B → Prop) :
    letI := geometricOutcomeFintype p hp a B hdeg
    letI := outcomeFintype p hp hp4 a B hdeg
    (law p hp hp4 a B hdeg hB).eventMass (fun φ => E (outcomeEquivRaw p hp hp4 a B hdeg φ)) =
      (RawDegreeSampler.law (W := (source p a).toAffine) rfl rfl B hdeg hB
        (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)).eventMass E := by
  let := geometricOutcomeFintype p hp a B hdeg
  let := outcomeFintype p hp hp4 a B hdeg
  rw [law, FiniteLaw.pushForward_event]
  apply FiniteLaw.eventMass_congr
  intro φ
  rw [Equiv.apply_symm_apply]

end
end IsogenyAttack.RationalRawSampler
