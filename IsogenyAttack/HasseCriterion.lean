import IsogenyAttack.StationaryIdentification

/-! The intrinsic coefficient criterion on actual Legendre equations.

For y²=f(x) in odd characteristic p, the Hasse coefficient is the coefficient
of x^(p−1) in f(x)^((p−1)/2). This file identifies that coefficient for the
actual Mathlib Legendre curve and proves its vanishing invariant under equal
j-invariants and admissible coordinate isomorphisms between Legendre models.
It does not assert an equivalence with the vanishing of geometric p-torsion,
nor that the resulting j-invariants lie in the quadratic finite field.
-/
namespace IsogenyAttack.Legendre
open Polynomial Finset
variable {K : Type*} [Field K]

/-- The cubic on the right side of an actual Weierstrass equation. -/
noncomputable def cubicRHS (W : WeierstrassCurve K) : K[X] :=
  X^3 + C W.a₂*X^2 + C W.a₄*X + C W.a₆

/-- The classical Hasse coefficient of an equation y²=f(x). Its geometric
interpretation applies when a₁=a₃=0 and p is an odd characteristic. -/
noncomputable def hasseCoefficient (p : ℕ) (W : WeierstrassCurve K) : K :=
  ((cubicRHS W)^((p-1)/2)).coeff (p-1)

@[simp] theorem curve_map {L : Type*} [Field L] (f : K →+* L) (t : K) :
    (curve t).map f = curve (f t) := by
  ext <;> simp [curve]

theorem cubicRHS_map {L : Type*} [Field L] (f : K →+* L) (W : WeierstrassCurve K) :
    cubicRHS (W.map f) = (cubicRHS W).map f := by
  simp [cubicRHS]

/-- The actual Hasse coefficient commutes with extension of the base field. -/
theorem hasseCoefficient_map {L : Type*} [Field L] (f : K →+* L)
    (p : ℕ) (W : WeierstrassCurve K) :
    hasseCoefficient p (W.map f) = f (hasseCoefficient p W) := by
  simp only [hasseCoefficient, cubicRHS_map, ← Polynomial.map_pow, coeff_map]

@[simp] theorem curve_cubicRHS (t : K) :
    cubicRHS (curve t) = X*(X-1)*(X-C t) := by
  simp only [cubicRHS, curve, map_neg, map_add, map_one, map_zero]
  ring

/-- The explicit Hasse polynomial is exactly the actual curve's Hasse
coefficient, up to the displayed nonzero sign. -/
theorem curve_hasseCoefficient (p n : ℕ) (hp : p=2*n+1) (t : K) :
    hasseCoefficient p (curve t) = (-1 : K)^n *
      (hassePolynomial (K := K) n).eval t := by
  have hn : (p-1)/2=n := by omega
  have hn' : p-1=2*n := by omega
  rw [hasseCoefficient, curve_cubicRHS, hn, hn']
  exact legendre_middle_coefficient n t

theorem curve_hasseCoefficient_zero_iff (p n : ℕ) (hp : p=2*n+1) (t : K) :
    hasseCoefficient p (curve t) = 0 ↔
      (hassePolynomial (K := K) n).IsRoot t := by
  rw [curve_hasseCoefficient p n hp]
  simp only [IsRoot, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero,
    one_ne_zero, false_and, false_or]

theorem elliptic_parameter_ne_zero (t : K) [(curve t).IsElliptic] : t ≠ 0 := by
  intro h
  have hd := (curve t).isUnit_Δ.ne_zero
  simp [curve_discriminant, h] at hd

theorem elliptic_parameter_ne_one (t : K) [(curve t).IsElliptic] : t ≠ 1 := by
  intro h
  have hd := (curve t).isUnit_Δ.ne_zero
  simp [curve_discriminant, h] at hd

/-- Hasse-coefficient vanishing is an invariant of the actual geometric
j-class among nonsingular Legendre models, in every odd characteristic. -/
theorem curve_hasseCoefficient_zero_iff_of_j_eq (p : ℕ) [CharP K p]
    [Fact p.Prime] (hp : 2 < p) (a t : K)
    [(curve a).IsElliptic] [(curve t).IsElliptic]
    (hj : (curve t).j = (curve a).j) :
    hasseCoefficient p (curve t) = 0 ↔ hasseCoefficient p (curve a) = 0 := by
  obtain ⟨b, hb⟩ := (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  have hpn : p = 2*((p-1)/2)+1 := by omega
  have h2 : (2 : K) ≠ 0 := small_natCast_ne_zero p (k := 2) (by decide) hp
  have h256 : (256 : K) ≠ 0 := by
    have h := pow_ne_zero 8 h2
    norm_num at h
    exact h
  rw [curve_hasseCoefficient_zero_iff p _ hpn,
    curve_hasseCoefficient_zero_iff p _ hpn]
  rw [curve_jInvariant, curve_jInvariant] at hj
  constructor
  · intro ht
    exact same_j_hasse_root p hpn h256 ht (elliptic_parameter_ne_zero a)
      (elliptic_parameter_ne_one a) hj.symm
  · intro ha
    exact same_j_hasse_root p hpn h256 ha (elliptic_parameter_ne_zero t)
      (elliptic_parameter_ne_one t) hj

/-- An actual admissible Weierstrass coordinate isomorphism between
Legendre models preserves Hasse-coefficient vanishing. -/
theorem curve_hasseCoefficient_zero_iff_of_coordinateIso (p : ℕ)
    [CharP K p] [Fact p.Prime] (hp : 2 < p) (a t : K)
    [(curve a).IsElliptic] [(curve t).IsElliptic]
    (C : WeierstrassCurve.VariableChange K) (hC : C • curve a = curve t) :
    hasseCoefficient p (curve t) = 0 ↔ hasseCoefficient p (curve a) = 0 := by
  apply curve_hasseCoefficient_zero_iff_of_j_eq p hp a t
  have hj := WeierstrassCurve.variableChange_j (curve a) C
  simpa only [hC] using hj

/-- The finite target class set is precisely the actual Legendre
Hasse-coefficient zero locus, with no extra root or mass assumption. -/
theorem mem_hasseJClasses_iff_coefficient_zero [DecidableEq K]
    (p : ℕ) [CharP K p] [Fact p.Prime] (hp : 2 < p)
    (t : K) [(curve t).IsElliptic] :
    (curve t).j ∈ (hassePolynomial (K := K) ((p-1)/2)).roots.toFinset.image jInvariant ↔
      hasseCoefficient p (curve t) = 0 := by
  obtain ⟨b, hb⟩ := (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  have hpn : p = 2*((p-1)/2)+1 := by omega
  have h2 : (2 : K) ≠ 0 := small_natCast_ne_zero p (k := 2) (by decide) hp
  have h256 : (256 : K) ≠ 0 := by
    have h := pow_ne_zero 8 h2
    norm_num at h
    exact h
  rw [curve_hasseCoefficient_zero_iff p _ hpn, curve_jInvariant]
  constructor
  · intro hj
    obtain ⟨a, ha, haj⟩ := Finset.mem_image.mp hj
    have ha' : (hassePolynomial (K := K) ((p-1)/2)).IsRoot a := by
      simpa only [Multiset.mem_toFinset,
        mem_roots (hassePolynomial_monic _).ne_zero] using ha
    exact same_j_hasse_root p hpn h256 ha' (elliptic_parameter_ne_zero t)
      (elliptic_parameter_ne_one t) haj.symm
  · intro ht
    apply Finset.mem_image.mpr
    refine ⟨t, ?_, rfl⟩
    simpa only [Multiset.mem_toFinset,
      mem_roots (hassePolynomial_monic _).ne_zero] using ht

/-- Every actual elliptic curve over an algebraically closed field of odd
characteristic admits a Legendre model by an actual coordinate isomorphism. -/
theorem exists_legendre_model [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (t : K) (_ : (curve t).IsElliptic) (C : WeierstrassCurve.VariableChange K),
      C • W = curve t := by
  have h256 : (256 : K) ≠ 0 := by
    have h := pow_ne_zero 8 h2
    norm_num at h
    exact h
  have hdeg : (fiberPolynomial W.j).degree ≠ 0 := by
    rw [degree_eq_natDegree (fiberPolynomial_ne_zero W.j h256),
      fiberPolynomial_natDegree W.j h256]
    norm_num
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (fiberPolynomial W.j) hdeg
  obtain ⟨ht0, ht1, hj⟩ := (fiberPolynomial_isRoot_iff h256).mp ht
  haveI := curve_isElliptic h2 ht0 ht1
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W (curve t)
    ((curve_jInvariant t).trans hj).symm
  exact ⟨t, inferInstance, C, hC⟩

/-- An explicit representative-independent geometric locus: an actual
Weierstrass model is isomorphic to a Legendre model of Hasse coefficient zero.
This definition makes no claim about p-rank or quadratic-field descent. -/
def HasLegendreHasseZero (p : ℕ) (W : WeierstrassCurve K) : Prop :=
  ∃ (t : K) (C : WeierstrassCurve.VariableChange K),
    C • W = curve t ∧ hasseCoefficient p (curve t) = 0

/-- The finite target set is exactly the j-set of the explicitly defined
geometric Hasse-coefficient zero locus. -/
theorem hasLegendreHasseZero_iff_j_mem [IsAlgClosed K] [DecidableEq K]
    (p : ℕ) [CharP K p] [Fact p.Prime] (hp : 2 < p)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    HasLegendreHasseZero p W ↔
      W.j ∈ (hassePolynomial (K := K) ((p-1)/2)).roots.toFinset.image jInvariant := by
  constructor
  · rintro ⟨t, C, hC, ht⟩
    haveI : (curve t).IsElliptic := hC ▸ (inferInstance : (C • W).IsElliptic)
    have hj : (curve t).j = W.j := by
      simpa only [hC] using WeierstrassCurve.variableChange_j W C
    rw [← hj, mem_hasseJClasses_iff_coefficient_zero p hp t]
    exact ht
  · intro hj
    obtain ⟨t, ht, htj⟩ := Finset.mem_image.mp hj
    let r : HasseRoot (K := K) ((p-1)/2) := ⟨t, ht⟩
    haveI := curve_isElliptic (small_natCast_ne_zero p (k := 2) (by decide) hp)
      (hasseRoot_ne_zero r) (hasseRoot_ne_one
        (hassePolynomial_eval_one_ne_zero p (by omega)) r)
    obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W (curve t)
      ((curve_jInvariant t).trans htj).symm
    refine ⟨t, C, hC, ?_⟩
    rw [← mem_hasseJClasses_iff_coefficient_zero p hp t, curve_jInvariant]
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩

end IsogenyAttack.Legendre
