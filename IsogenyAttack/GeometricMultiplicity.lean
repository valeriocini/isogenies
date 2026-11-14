import IsogenyAttack.MontgomeryGeometry
import IsogenyAttack.LegendreDistribution

/-!
Actual geometric model and coordinate-isomorphism multiplicities. A realization
is a target Montgomery model together with an actual admissible change of variables
to it. The number is twelve for every nonsingular source curve. The final uniform
projection theorem applies to any supplied finite family of source curves; it does
not assert that those curves are quotients by isogeny kernels.
-/
namespace IsogenyAttack.GeometricMultiplicity
open scoped BigOperators
open CurveAutomorphisms Montgomery

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

abbrev ModelFiber (j : K) := {t : K // t ∈ (fiberPolynomial j).roots.toFinset}

omit [DecidableEq K] [IsAlgClosed K] in
lemma two_pow_eight_ne_zero (h2 : (2 : K) ≠ 0) : (256 : K) ≠ 0 := by
  convert pow_ne_zero 8 h2 using 1; norm_num

omit [IsAlgClosed K] in
lemma modelFiber_property (j : K) (h2 : (2 : K) ≠ 0) (t : ModelFiber j) :
    t.val^2 ≠ 4 ∧ jInvariant t.val = j := by
  apply (fiberPolynomial_isRoot_iff (two_pow_eight_ne_zero h2)).mp
  exact (Polynomial.mem_roots (fiberPolynomial_ne_zero j (two_pow_eight_ne_zero h2))).mp
    (Multiset.mem_toFinset.mp t.property)

theorem card_modelFiber (j : K) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Fintype.card (ModelFiber j) = if j = 0 then 2 else if j = 1728 then 3 else 6 := by
  simp only [ModelFiber, Fintype.card_coe]
  by_cases hj0 : j = 0
  · subst j
    simpa using zero_j_fiber_card h2 h3
  · by_cases hj1728 : j = 1728
    · subst j
      simpa [hj0] using exceptional_j_fiber_card h2 h3
    · simpa [hj0,hj1728] using generic_j_fiber_card h2 hj0 hj1728

/-- All geometric Montgomery realizations of a nonsingular Weierstrass equation. -/
abbrev Realization (W : WeierstrassCurve K) [W.IsElliptic] :=
  Σ t : ModelFiber W.j, CoordinateIso W (curve t.val)

lemma card_realization_fiber (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (t : ModelFiber W.j) :
    Nat.card (CoordinateIso W (curve t.val)) =
      if W.j = 0 then 6 else if W.j = 1728 then 4 else 2 := by
  have ht := modelFiber_property W.j h2 t
  letI := curve_isElliptic h2 ht.1
  apply card_coordinateIso_by_j W (curve t.val) _ h2 h3
  exact (curve_jInvariant t.val |>.trans ht.2).symm

lemma realization_fiber_finite (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (t : ModelFiber W.j) :
    Finite (CoordinateIso W (curve t.val)) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_realization_fiber W h2 h3 t]
  split_ifs <;> norm_num

/-- The product of actual model count 2/3/6 and actual isomorphism count 6/4/2
is exactly twelve, independently of the source curve. -/
theorem card_realization (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Nat.card (Realization W) = 12 := by
  letI : ∀ t : ModelFiber W.j, Finite (CoordinateIso W (curve t.val)) :=
    realization_fiber_finite W h2 h3
  rw [Realization, Nat.card_sigma]
  simp_rw [card_realization_fiber W h2 h3]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [card_modelFiber W.j h2 h3]
  split_ifs <;> norm_num

lemma realization_finite (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Finite (Realization W) :=
  Nat.finite_of_card_ne_zero (by rw [card_realization W h2 h3]; norm_num)

lemma realization_nonempty (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Nonempty (Realization W) :=
  (Nat.card_ne_zero.mp (by rw [card_realization W h2 h3]; norm_num)).1

/-- The fiber of the first projection is the original dependent component. -/
def sigmaFirstFiberEquiv {ι : Type*} (β : ι → Type*) (i : ι) :
    {x : (Σ i, β i) // x.1 = i} ≃ β i where
  toFun x := x.property ▸ x.val.2
  invFun b := ⟨⟨i,b⟩,rfl⟩
  left_inv x := by rcases x with ⟨⟨j,b⟩,h⟩; cases h; rfl
  right_inv b := rfl

/-- Equal finite component sizes make the first projection of a uniform
sigma-type exactly uniform. This is an equality of the defined finite laws. -/
theorem uniform_sigma_first {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ι → Type*) [∀ i, Fintype (β i)] [Nonempty (Σ i, β i)]
    (m : ℕ) (hm : m ≠ 0) (hc : ∀ i, Fintype.card (β i) = m) (i : ι) :
    ((FiniteLaw.uniform (Σ i, β i)).pushForward Sigma.fst).mass i =
      (FiniteLaw.uniform ι).mass i := by
  classical
  change (FiniteLaw.uniform (Σ i, β i)).eventMass (fun x => x.1 = i) = _
  rw [FiniteLaw.uniform_event, Fintype.card_congr (sigmaFirstFiberEquiv β i), hc i,
    Fintype.card_sigma]
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul,
    FiniteLaw.uniform]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hiR : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  field_simp

/-- Uniformly sampling the twelve geometric realizations of each member of any
finite curve family induces exactly the uniform law on that family. An isogeny
application must separately supply and verify the family of quotient curves. -/
theorem uniform_realization_family {ι : Type*} [Fintype ι] [Nonempty ι]
    (Q : ι → WeierstrassCurve K) [∀ i, (Q i).IsElliptic]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (i : ι) :
    letI : ∀ i, Finite (Realization (Q i)) := fun i => realization_finite (Q i) h2 h3
    letI : ∀ i, Fintype (Realization (Q i)) := fun i => Fintype.ofFinite _
    letI : Nonempty (Σ i, Realization (Q i)) := by
      obtain ⟨i⟩ := ‹Nonempty ι›
      obtain ⟨r⟩ := realization_nonempty (Q i) h2 h3
      exact ⟨⟨i,r⟩⟩
    ((FiniteLaw.uniform (Σ i, Realization (Q i))).pushForward Sigma.fst).mass i =
      (FiniteLaw.uniform ι).mass i := by
  letI : ∀ i, Finite (Realization (Q i)) := fun i => realization_finite (Q i) h2 h3
  letI : ∀ i, Fintype (Realization (Q i)) := fun i => Fintype.ofFinite _
  letI : Nonempty (Σ i, Realization (Q i)) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨r⟩ := realization_nonempty (Q i) h2 h3
    exact ⟨⟨i,r⟩⟩
  apply uniform_sigma_first (fun i => Realization (Q i)) 12 (by norm_num) _ i
  intro i
  rw [Fintype.card_eq_nat_card, card_realization (Q i) h2 h3]


lemma modelFiber_nonempty (j : K) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Nonempty (ModelFiber j) := by
  apply Fintype.card_pos_iff.mp
  rw [card_modelFiber j h2 h3]
  split_ifs <;> norm_num

/-- Conditional on any particular source curve, a uniform coordinate
realization chooses uniformly among all its geometric Montgomery models. -/
theorem uniform_realization_model (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (t : ModelFiber W.j) :
    letI : ∀ t : ModelFiber W.j, Finite (CoordinateIso W (curve t.val)) :=
      realization_fiber_finite W h2 h3
    letI : ∀ t : ModelFiber W.j, Fintype (CoordinateIso W (curve t.val)) :=
      fun _ => Fintype.ofFinite _
    letI : Nonempty (ModelFiber W.j) := modelFiber_nonempty W.j h2 h3
    letI : Nonempty (Realization W) := realization_nonempty W h2 h3
    ((FiniteLaw.uniform (Realization W)).pushForward Sigma.fst).mass t =
      (FiniteLaw.uniform (ModelFiber W.j)).mass t := by
  letI : ∀ t : ModelFiber W.j, Finite (CoordinateIso W (curve t.val)) :=
    realization_fiber_finite W h2 h3
  letI : ∀ t : ModelFiber W.j, Fintype (CoordinateIso W (curve t.val)) :=
    fun _ => Fintype.ofFinite _
  letI : Nonempty (ModelFiber W.j) := modelFiber_nonempty W.j h2 h3
  letI : Nonempty (Realization W) := realization_nonempty W h2 h3
  apply uniform_sigma_first (fun t : ModelFiber W.j => CoordinateIso W (curve t.val))
    (if W.j = 0 then 6 else if W.j = 1728 then 4 else 2) _ _ t
  · split_ifs <;> norm_num
  · intro t
    rw [Fintype.card_eq_nat_card, card_realization_fiber W h2 h3]

end IsogenyAttack.GeometricMultiplicity
