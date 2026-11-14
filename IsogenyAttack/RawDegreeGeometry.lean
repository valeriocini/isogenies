import IsogenyAttack.RawDegreeSampler
import IsogenyAttack.CyclicComponent
import IsogenyAttack.GenuineAttack

/-! The observed response of the degree-first sampler is the actual cyclic
component of the raw map, with its original target equation retained. -/
namespace IsogenyAttack.RawDegreeGeometry
open WeierstrassCurve WeierstrassCurve.Affine TauCeti
open IsogenySampler RawDegreeSampler

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [NeZero (2 : K)] [IsAlgClosed K]
    {W : Affine K} [W.IsElliptic]

abbrev target {B : ℕ} (φ : Outcome W B) : WeierstrassCurve K :=
  Montgomery.curve φ.2.1.val

instance target_isElliptic {B : ℕ} (φ : Outcome W B) : (target φ).IsElliptic :=
  Montgomery.curve_isElliptic (NeZero.ne (2 : K)) φ.2.1.property

abbrev rawMap {B : ℕ} (φ : Outcome W B) : Isogeny W (target φ).toAffine :=
  φ.2.2.val

theorem rawMap_degree {B : ℕ} (φ : Outcome W B) : (rawMap φ).degree = φ.1.val :=
  φ.2.2.property.1

instance rawMap_separable {B : ℕ} (φ : Outcome W B) :
    Algebra.IsSeparable (rawMap φ).fieldPullback.fieldRange W.FunctionField :=
  isSeparable_of_card_ker_eq_degree W (rawMap φ) φ.2.2.property.2

theorem rawMap_kernel {B : ℕ} (φ : Outcome W B) :
    (rawMap φ).toPointHom.ker = (kernel W φ).2.val :=
  (pointKernel_eq_toPointHom_ker W (rawMap φ)).symm

theorem rawMap_target_j {B : ℕ} (φ : Outcome W B) :
    (quotientCurve W (kernel W φ).2.val).j = (target φ).j :=
  fixedKernelMaps_target_j W (target φ) (kernel W φ).2.val
    ⟨rawMap φ, (quotientKernel_pointKernel W (rawMap φ)).symm, φ.2.2.property.2⟩

/-- The scalar-stripped actual map into the original Montgomery target. -/
def component (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome W B) :
    Isogeny W (target φ).toAffine :=
  actualCyclicComponent ha₁ ha₃ B hdeg (kernel W φ) (rawMap φ) (rawMap_kernel φ)

theorem component_factorization (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome W B) :
    (component ha₁ ha₃ B hdeg φ).comp
      (Isogeny.mulByIntIsogenyOfNeZero W
        (show ((actualKernelEquiv ha₁ ha₃ B hdeg (kernel W φ)).val.content : ℤ) ≠ 0 by
          exact_mod_cast (actualKernelEquiv ha₁ ha₃ B hdeg (kernel W φ)).val.content_pos.ne')) =
      rawMap φ :=
  (actualCyclicComponent_spec ha₁ ha₃ B hdeg (kernel W φ)
    (rawMap φ) (rawMap_kernel φ)).1

theorem component_degree_card (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome W B) :
    (component ha₁ ha₃ B hdeg φ).degree =
      Nat.card (actualStrip ha₁ ha₃ B hdeg (kernel W φ)) :=
  (actualCyclicComponent_spec ha₁ ha₃ B hdeg (kernel W φ)
    (rawMap φ) (rawMap_kernel φ)).2.1

theorem component_degree_code (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome W B) :
    (component ha₁ ha₃ B hdeg φ).degree =
      (actualKernelEquiv ha₁ ha₃ B hdeg (kernel W φ)).val.cyclicDegree :=
  actualCyclicComponent_degree ha₁ ha₃ B hdeg (kernel W φ) (rawMap φ) (rawMap_kernel φ)

theorem component_kernel (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome W B) :
    (component ha₁ ha₃ B hdeg φ).toPointHom.ker =
      actualStrip ha₁ ha₃ B hdeg (kernel W φ) :=
  actualCyclicComponent_point_kernel ha₁ ha₃ B hdeg (kernel W φ)
    (rawMap φ) (rawMap_kernel φ)

theorem component_cyclic (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome W B) :
    IsAddCyclic (component ha₁ ha₃ B hdeg φ).toPointHom.ker :=
  (actualCyclicComponent_spec ha₁ ha₃ B hdeg (kernel W φ)
    (rawMap φ) (rawMap_kernel φ)).2.2.2.2.1

instance component_separable (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome W B) :
    Algebra.IsSeparable (component ha₁ ha₃ B hdeg φ).fieldPullback.fieldRange
      W.FunctionField :=
  actualCyclicComponent_separable ha₁ ha₃ B hdeg (kernel W φ)
    (rawMap φ) (rawMap_kernel φ)

/-- The strict cutoff is tested on the original degree. On success the
observed number is the degree of the genuine cyclic-component response. -/
def observation (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome W B) : Option ℕ :=
  if φ.1.val < B then some (component ha₁ ha₃ B hdeg φ).degree else none

theorem observation_eq_genuineDegreeObservation (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (φ : Outcome W B) :
    observation ha₁ ha₃ B hdeg φ =
      genuineDegreeObservation ha₁ ha₃ B hdeg (kernel W φ) := by
  unfold observation genuineDegreeObservation
  rw [component_degree_card, quotientIsogeny_degree]
  rfl

end
end IsogenyAttack.RawDegreeGeometry
