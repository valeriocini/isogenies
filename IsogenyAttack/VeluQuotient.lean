import IsogenyAttack.HasseSupersingular
import IsogenyAttack.StationaryRootLaw
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Isogeny
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel

/-! The genuine algebraic quotient by a finite subgroup of elliptic-curve
points. The underlying construction is Tau Ceti's Vélu function-field map,
with proved kernel, separability, degree, and ellipticity of the codomain. -/
namespace IsogenyAttack

open WeierstrassCurve WeierstrassCurve.Affine TauCeti

variable {K : Type*} [Field K] [DecidableEq K]
    (W : Affine K) [W.IsElliptic]

/-- Transport along the identity base change required by the function-field API. -/
noncomputable abbrev quotientKernel (S : AddSubgroup W.Point) :
    AddSubgroup (W.baseChange K).toAffine.Point :=
  S.map (Point.equivBaseChangeSelf W).toAddMonoidHom

instance quotientKernel_finite (S : AddSubgroup W.Point) [Finite S] :
    Finite (quotientKernel W S) := by
  exact Finite.of_equiv S ((Point.equivBaseChangeSelf W).addSubgroupMap S).toEquiv

/-- The actual elliptic quotient curve, constructed from Vélu coordinates. -/
noncomputable abbrev quotientCurve (S : AddSubgroup W.Point) [Finite S] : WeierstrassCurve K :=
  W.veluCurve (quotientKernel W S)

instance quotientCurve_isElliptic (S : AddSubgroup W.Point) [Finite S] :
    (quotientCurve W S).IsElliptic := by
  exact W.isElliptic_veluCurve (quotientKernel W S)

/-- The genuine nonconstant pointed algebraic map into the quotient curve. -/
noncomputable abbrev quotientIsogeny (S : AddSubgroup W.Point) [Finite S] :
    Isogeny W (quotientCurve W S).toAffine :=
  W.veluIsogeny (quotientKernel W S)

theorem quotientIsogeny_degree (S : AddSubgroup W.Point) [Finite S] :
    (quotientIsogeny W S).degree = Nat.card S := by
  rw [quotientIsogeny,degree_veluIsogeny]
  exact (Nat.card_congr ((Point.equivBaseChangeSelf W).addSubgroupMap S).toEquiv).symm

theorem quotientIsogeny_kernel (S : AddSubgroup W.Point) [Finite S] :
    (quotientIsogeny W S).ker = quotientKernel W S :=
  W.ker_veluIsogeny (quotientKernel W S)

instance quotientIsogeny_separable (S : AddSubgroup W.Point) [Finite S] :
    Algebra.IsSeparable (quotientIsogeny W S).fieldPullback.fieldRange W.FunctionField := by
  exact W.isSeparable_veluIsogeny (quotientKernel W S)

/-- On actual curve points, the kernel is exactly the input subgroup. -/
theorem quotientIsogeny_point_kernel [IsAlgClosed K]
    (S : AddSubgroup W.Point) [Finite S] : (quotientIsogeny W S).toPointHom.ker = S := by
  apply AddSubgroup.map_injective (f := (Point.equivBaseChangeSelf W).toAddMonoidHom)
    (Point.equivBaseChangeSelf W).injective
  rw [← Isogeny.ker_eq_map_ker_toPointHom,quotientIsogeny_kernel]

/-- Prime torsion cannot be created by a surjective group homomorphism with
kernel order coprime to that prime. -/
theorem no_torsion_of_surjective_of_coprime {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Surjective f) (p : ℕ)
    (hp : Nat.Coprime p (Nat.card f.ker))
    (hA : ∀ x : A, p • x = 0 → x = 0) :
    ∀ y : B, p • y = 0 → y = 0 := by
  intro y hy
  obtain ⟨x,rfl⟩ := hf y
  have hx : p • x ∈ f.ker := by
    change f (p • x) = 0
    rw [map_nsmul,hy]
  have hd : Nat.card f.ker • (p • x) = 0 :=
    congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨p • x,hx⟩ : f.ker)))
  have hd' : p • (Nat.card f.ker • x) = 0 := by
    rw [smul_comm]
    exact hd
  have hdx := hA _ hd'
  have hdy : Nat.card f.ker • f x = 0 := by rw [← map_nsmul,hdx,map_zero]
  have ho : addOrderOf (f x) ∣ 1 := by
    rw [← hp.gcd_eq_one]
    exact Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hy)
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hdy)
  have hz := addOrderOf_dvd_iff_nsmul_eq_zero.mp ho
  simpa using hz

/-- Over an algebraically closed field the geometric supersingularity
definition may be read directly on the current affine point group. -/
theorem supersingular_iff_point_torsion [IsAlgClosed K] {p : ℕ} (hp : p ≠ 0) :
    W.IsSupersingular p ↔ AddSubgroup.torsionBy W.Point p = ⊥ := by
  have hh := WeierstrassCurve.isSupersingular_iff_of_isAlgClosed (W := W) hp K
  rw [W.baseChange_self] at hh
  exact hh

/-- A quotient of a supersingular elliptic curve by a subgroup of order
coprime to p is again an actual supersingular elliptic curve. -/
theorem quotientCurve_supersingular [IsAlgClosed K] (S : AddSubgroup W.Point) [Finite S]
    {p : ℕ} (hp : p ≠ 0) (hW : W.IsSupersingular p)
    (hcop : Nat.Coprime p (Nat.card S)) : (quotientCurve W S).IsSupersingular p := by
  apply (supersingular_iff_point_torsion (quotientCurve W S).toAffine hp).mpr
  have hsource := (supersingular_iff_point_torsion W hp).mp hW
  have hcop' : Nat.Coprime p (Nat.card (quotientIsogeny W S).toPointHom.ker) := by
    rw [quotientIsogeny_point_kernel]
    exact hcop
  have hzero := no_torsion_of_surjective_of_coprime
    (quotientIsogeny W S).toPointHom (quotientIsogeny W S).toPointHom_surjective p hcop'
    (by
      intro x hx
      have hm := AddSubgroup.torsionBy.nsmul_iff.mpr hx
      rw [hsource] at hm
      exact hm)
  apply le_antisymm _ bot_le
  intro y hy
  exact hzero y (AddSubgroup.torsionBy.nsmul_iff.mp hy)

/-- The target of the actual algebraic quotient, as a member of the finite
Hasse j-set used by the attack's stationary distribution. -/
noncomputable def quotientJClass [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    (hp : 2 < p) (hW : W.IsSupersingular p) (S : AddSubgroup W.Point) [Finite S]
    (hcop : Nat.Coprime p (Nat.card S)) : Legendre.HasseJClass (K := K) ((p-1)/2) :=
  ⟨(quotientCurve W S).j,
    (Legendre.isSupersingular_iff_j_mem_hasse p hp (quotientCurve W S)).mp
      (quotientCurve_supersingular W S (Fact.out : p.Prime).ne_zero hW hcop)⟩

@[simp] theorem quotientJClass_val [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    (hp : 2 < p) (hW : W.IsSupersingular p) (S : AddSubgroup W.Point) [Finite S]
    (hcop : Nat.Coprime p (Nat.card S)) :
    (quotientJClass W p hp hW S hcop).val = (quotientCurve W S).j := rfl

end IsogenyAttack
