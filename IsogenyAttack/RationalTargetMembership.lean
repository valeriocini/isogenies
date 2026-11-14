import IsogenyAttack.RawDegreeSampler
import IsogenyAttack.GenuineAttack
import IsogenyAttack.FiniteMontgomerySampler

/-! Every actual prime-to-characteristic map from a supersingular source has a
supersingular target. For normalized Montgomery targets this yields the concrete
finite-field coefficient used in the target-first sampler. -/
namespace IsogenyAttack.RationalTargetMembership
open WeierstrassCurve WeierstrassCurve.Affine TauCeti IsogenySampler

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
    (W : Affine K) [W.IsElliptic]

omit [NeZero (2 : K)] in
theorem fixedKernelMaps_target_supersingular (V : WeierstrassCurve K) [V.IsElliptic]
    (S : AddSubgroup W.Point) [Finite S] (φ : FixedKernelMaps W V S)
    {p : ℕ} (hp : p ≠ 0) (hW : W.IsSupersingular p)
    (hcop : Nat.Coprime p (Nat.card S)) : V.IsSupersingular p := by
  let C := (coordinateIsoEquivFixedKernelMaps W V S).symm φ
  rw [← C.property, WeierstrassCurve.isSupersingular_variableChange_iff]
  exact quotientCurve_supersingular W S hp hW hcop

theorem degreeMap_target_supersingular {d : ℕ} [NeZero d] (φ : DegreeMaps W d)
    {p : ℕ} (hp : p ≠ 0) (hW : W.IsSupersingular p) (hcop : Nat.Coprime p d) :
    (Montgomery.curve φ.1.val).IsSupersingular p := by
  let S := degreeMapKernel W φ
  have := Montgomery.curve_isElliptic (NeZero.ne (2 : K)) φ.1.property
  exact fixedKernelMaps_target_supersingular W (Montgomery.curve φ.1.val) S.val
    ⟨φ.2.val, (quotientKernel_pointKernel W φ.2.val).symm, φ.2.property.2⟩ hp hW
    (S.property.symm ▸ hcop)

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The actual target coefficient of every raw map belongs to the explicit quadratic
finite subfield; supersingularity and descent are derived from the source. -/
def degreeMapFiniteTarget (hp : 2 < p) (hW : W.IsSupersingular p)
    {d : ℕ} [NeZero d] (hcop : Nat.Coprime p d) (φ : DegreeMaps W d) :
    FiniteMontgomerySampler.Parameters (K := K) p := by
  have := Montgomery.curve_isElliptic (NeZero.ne (2 : K)) φ.1.property
  have hss := degreeMap_target_supersingular W φ (Fact.out : p.Prime).ne_zero hW hcop
  let a : frobeniusFixedField (K := K) p 2 :=
    ⟨φ.1.val, Montgomery.supersingular_parameter_mem_quadraticField p (by omega) φ.1.val hss⟩
  have ha : a^2 ≠ 4 := by
    intro h
    exact φ.1.property (congrArg Subtype.val h)
  exact ⟨a, ha, (FiniteMontgomerySampler.coefficient_isSupersingular_iff p hp a ha).mp hss⟩

@[simp] theorem degreeMapFiniteTarget_coefficient (hp : 2 < p) (hW : W.IsSupersingular p)
    {d : ℕ} [NeZero d] (hcop : Nat.Coprime p d) (φ : DegreeMaps W d) :
    (degreeMapFiniteTarget W p hp hW hcop φ).val.val = φ.1.val := rfl

omit [IsAlgClosed K] [NeZero (2 : K)] in
theorem outcome_degree_coprime {B : ℕ} (hdeg : ValidDegrees K B)
    (φ : RawDegreeSampler.Outcome W B) : Nat.Coprime p φ.1.val := by
  rw [(Fact.out : p.Prime).coprime_iff_not_dvd]
  intro hd
  exact hdeg φ.1.val (Finset.mem_Icc.mp φ.1.property).1
    (Finset.mem_Icc.mp φ.1.property).2 ((CharP.cast_eq_zero_iff K p _).mpr hd)

/-- A raw degree-first outcome has a canonical member of exactly the finite-field
target set sampled by the target-first experiment. -/
def outcomeFiniteTarget (hp : 2 < p) (hW : W.IsSupersingular p)
    {B : ℕ} (hdeg : ValidDegrees K B) (φ : RawDegreeSampler.Outcome W B) :
    FiniteMontgomerySampler.Parameters (K := K) p := by
  letI : NeZero φ.1.val := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp φ.1.property).1⟩
  exact degreeMapFiniteTarget W p hp hW (outcome_degree_coprime W p hdeg φ) φ.2

@[simp] theorem outcomeFiniteTarget_coefficient (hp : 2 < p) (hW : W.IsSupersingular p)
    {B : ℕ} (hdeg : ValidDegrees K B) (φ : RawDegreeSampler.Outcome W B) :
    (outcomeFiniteTarget W p hp hW hdeg φ).val.val = φ.2.1.val := rfl

/-- The canonical finite-field target has exactly the geometric quotient j-class
used by the kernel experiment. -/
theorem outcomeFiniteTarget_jMap [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    (hp : 3 < p) (hW : W.IsSupersingular p) {B : ℕ} (hdeg : ValidDegrees K B)
    (φ : RawDegreeSampler.Outcome W B) :
    FiniteMontgomerySampler.jMap p hp
      (outcomeFiniteTarget W p (by omega) hW hdeg φ) =
      geometricTarget p (by omega) hW (RawDegreeSampler.kernel W φ).2.val := by
  have := Montgomery.curve_isElliptic (NeZero.ne (2 : K)) φ.2.1.property
  have hj := fixedKernelMaps_target_j W (Montgomery.curve φ.2.1.val)
    (RawDegreeSampler.kernel W φ).2.val
    ⟨φ.2.2.val, (quotientKernel_pointKernel W φ.2.2.val).symm, φ.2.2.property.2⟩
  apply Subtype.ext
  rw [FiniteMontgomerySampler.jMap_val, outcomeFiniteTarget_coefficient,
    geometricTarget_val p (by omega) hW _
      (actualKernel_coprime p hdeg (RawDegreeSampler.kernel W φ))]
  exact (Montgomery.curve_jInvariant φ.2.1.val).symm.trans hj.symm

end
end IsogenyAttack.RationalTargetMembership
