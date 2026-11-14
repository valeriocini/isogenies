import IsogenyAttack.GeometricMultiplicity
import IsogenyAttack.StationaryIdentification

/-! The uniform law on actual Montgomery parameters with Hasse supersingular
j-invariant agrees exactly with the Hasse-root law. Both exceptional fibers are
included. The supersingular interpretation is supplied by HasseSupersingular. -/
namespace IsogenyAttack.MontgomeryStationary
open scoped BigOperators
open Legendre

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

/-- A distinct Montgomery parameter, indexed by its uniquely determined j-class. -/
abbrev Parameters (n : ℕ) :=
  Σ j : HasseJClass (K := K) n, GeometricMultiplicity.ModelFiber j.val

theorem card_model_eq_hasse_fiber (p : ℕ) [CharP K p] [Fact p.Prime]
    (hp : 3 < p) (j : HasseJClass (K := K) ((p-1)/2)) :
    Fintype.card (GeometricMultiplicity.ModelFiber j.val) =
      Fintype.card {r : HasseRoot (K := K) ((p-1)/2) // hasseJMap r = j} := by
  have h2 : (2 : K) ≠ 0 := small_natCast_ne_zero p (k := 2) (by decide) (by omega)
  have h3 : (3 : K) ≠ 0 := small_natCast_ne_zero p (k := 3) (by decide) hp
  have h256 := GeometricMultiplicity.two_pow_eight_ne_zero h2
  have hpodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨a, ha⟩ := hpodd
  have hpn : p = 2*((p-1)/2)+1 := by omega
  rw [GeometricMultiplicity.card_modelFiber j.val h2 h3,
    Fintype.card_congr (hasseJFiberEquiv p hpn h256 j), Fintype.card_coe]
  by_cases h0 : j.val = 0
  · simp only [h0, ite_true]
    exact (zero_j_fiber_card h256 h3).symm
  · by_cases h1728 : j.val = 1728
    · rw [if_neg h0, if_pos h1728, h1728, exceptional_j_fiber_card h2 h3]
    · rw [if_neg h0, if_neg h1728, generic_j_fiber_card h256 h0 h1728]

/-- There are exactly (p-1)/2 distinct geometric Montgomery parameters. -/
theorem card_parameters (p : ℕ) [CharP K p] [Fact p.Prime] (hp : 3 < p) :
    Fintype.card (Parameters (K := K) ((p-1)/2)) = (p-1)/2 := by
  calc
    Fintype.card (Parameters (K := K) ((p-1)/2)) =
        ∑ j : HasseJClass (K := K) ((p-1)/2), Fintype.card (GeometricMultiplicity.ModelFiber j.val) :=
      Fintype.card_sigma
    _ = ∑ j : HasseJClass (K := K) ((p-1)/2),
        Fintype.card {r : HasseRoot (K := K) ((p-1)/2) // hasseJMap r = j} := by
      apply Finset.sum_congr rfl
      intro j _
      exact card_model_eq_hasse_fiber p hp j
    _ = Fintype.card (Σ j : HasseJClass (K := K) ((p-1)/2),
        {r : HasseRoot (K := K) ((p-1)/2) // hasseJMap r = j}) :=
      Fintype.card_sigma.symm
    _ = Fintype.card (HasseRoot (K := K) ((p-1)/2)) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv hasseJMap)
    _ = (p-1)/2 := hasseRoot_card _ (hassePolynomial_separable p (by omega))

theorem parameters_nonempty (p : ℕ) [CharP K p] [Fact p.Prime] (hp : 3 < p) :
    Nonempty (Parameters (K := K) ((p-1)/2)) :=
  Fintype.card_pos_iff.mp (by rw [card_parameters p hp]; omega)

/-- The uniform distribution on the actual Montgomery parameters. -/
noncomputable def parameterLaw (p : ℕ) [CharP K p] [Fact p.Prime] (hp : 3 < p) :
    FiniteLaw (Parameters (K := K) ((p-1)/2)) := by
  letI := parameters_nonempty (K := K) p hp
  exact FiniteLaw.uniform _

/-- Exact equality of the j-marginals, not just an upper bound on their masses. -/
theorem parameterLaw_j_mass (p : ℕ) [CharP K p] [Fact p.Prime] (hp : 3 < p)
    (j : HasseJClass (K := K) ((p-1)/2)) :
    ((parameterLaw (K := K) p hp).pushForward Sigma.fst).mass j =
      (hasseInvariantLaw (K := K) p (by omega)).mass j := by
  letI := parameters_nonempty (K := K) p hp
  letI := hasseRoot_nonempty (K := K) ((p-1)/2) (by omega)
    (hassePolynomial_separable p (by omega))
  change (FiniteLaw.uniform (Parameters (K := K) ((p-1)/2))).eventMass
      (fun x => x.1 = j) =
    (FiniteLaw.uniform (HasseRoot (K := K) ((p-1)/2))).eventMass
      (fun r => hasseJMap r = j)
  rw [FiniteLaw.uniform_event, FiniteLaw.uniform_event,
    Fintype.card_congr (GeometricMultiplicity.sigmaFirstFiberEquiv (fun j => GeometricMultiplicity.ModelFiber j.val) j),
    card_model_eq_hasse_fiber p hp j, card_parameters p hp,
    hasseRoot_card _ (hassePolynomial_separable p (by omega))]

/-- Each parameter occurs only once in the finite indexing above. -/
theorem parameter_injective (p : ℕ) [CharP K p] [Fact p.Prime] (hp : 3 < p) :
    Function.Injective (fun x : Parameters (K := K) ((p-1)/2) => x.2.val) := by
  intro ⟨j, a⟩ ⟨j', a'⟩ h
  have h2 : (2 : K) ≠ 0 := small_natCast_ne_zero p (k := 2) (by decide) (by omega)
  have hj : j = j' := by
    apply Subtype.ext
    exact (GeometricMultiplicity.modelFiber_property j.val h2 a).2.symm.trans
      ((congrArg Montgomery.jInvariant h).trans (GeometricMultiplicity.modelFiber_property j'.val h2 a').2)
  subst j'
  have ha : a = a' := Subtype.ext h
  subst a'
  rfl

/-- The same set without any j-class indexing: distinct coefficients of actual
Montgomery equations with nonzero discriminant and Hasse supersingular j. -/
abbrev ParameterLocus (n : ℕ) :=
  {a : K // a^2 ≠ 4 ∧ Montgomery.jInvariant a ∈
    (hassePolynomial (K := K) n).roots.toFinset.image Legendre.jInvariant}

noncomputable def parametersEquivLocus (n : ℕ) (h2 : (2 : K) ≠ 0) :
    Parameters (K := K) n ≃ ParameterLocus (K := K) n :=
  Equiv.ofBijective
    (fun x => ⟨x.2.val, (GeometricMultiplicity.modelFiber_property x.1.val h2 x.2).1,
      (GeometricMultiplicity.modelFiber_property x.1.val h2 x.2).2.symm ▸ x.1.property⟩)
    ⟨by
      intro ⟨j,a⟩ ⟨j',a'⟩ h
      have ha := congrArg Subtype.val h
      have hj : j = j' := by
        apply Subtype.ext
        exact (GeometricMultiplicity.modelFiber_property j.val h2 a).2.symm.trans
          ((congrArg Montgomery.jInvariant ha).trans
            (GeometricMultiplicity.modelFiber_property j'.val h2 a').2)
      subst j'
      have haa : a = a' := Subtype.ext ha
      subst a'
      rfl,
    by
      intro a
      refine ⟨⟨⟨Montgomery.jInvariant a.val, a.property.2⟩, ⟨a.val, ?_⟩⟩, ?_⟩
      · rw [Multiset.mem_toFinset, Polynomial.mem_roots
          (Montgomery.fiberPolynomial_ne_zero _
            (GeometricMultiplicity.two_pow_eight_ne_zero h2))]
        exact (Montgomery.fiberPolynomial_isRoot_iff
          (GeometricMultiplicity.two_pow_eight_ne_zero h2)).mpr ⟨a.property.1, rfl⟩
      · apply Subtype.ext
        rfl⟩

theorem card_parameterLocus (p : ℕ) [CharP K p] [Fact p.Prime] (hp : 3 < p) :
    Nat.card (ParameterLocus (K := K) ((p-1)/2)) = (p-1)/2 := by
  rw [← Nat.card_congr (parametersEquivLocus ((p-1)/2)
    (small_natCast_ne_zero p (k := 2) (by decide) (by omega))),
    Nat.card_eq_fintype_card, card_parameters p hp]

end IsogenyAttack.MontgomeryStationary
