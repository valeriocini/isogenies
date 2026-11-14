import IsogenyAttack.HasseCriterion
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-! Every root of the Legendre Hasse polynomial is defined over an actual
finite extension of the prime field. This reduction is elementary algebra;
it does not assume quadratic-field descent or a supersingularity criterion. -/

namespace IsogenyAttack.Legendre
open Polynomial

variable {K : Type*} [Field K]

/-- A Hasse root is integral over the prime field, witnessed by the monic
Hasse polynomial itself. -/
theorem hasseRoot_isIntegral (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K]
    (n : ℕ) (t : K) (ht : (hassePolynomial (K := K) n).IsRoot t) :
    IsIntegral (ZMod p) t := by
  refine ⟨hassePolynomial (K := ZMod p) n, hassePolynomial_monic n, ?_⟩
  rw [← eval_map, hassePolynomial_map]
  exact ht

/-- Every geometric Hasse root comes from a Hasse root in an actual finite
subfield. No bound on the extension degree is asserted here. -/
theorem hasseRoot_finite_subfield (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K]
    (n : ℕ) (t : K) (ht : (hassePolynomial (K := K) n).IsRoot t) :
    ∃ (F : IntermediateField (ZMod p) K) (_ : Finite F) (t₀ : F),
      (t₀ : K) = t ∧ (hassePolynomial (K := F) n).IsRoot t₀ := by
  let F : IntermediateField (ZMod p) K := IntermediateField.adjoin (ZMod p) {t}
  have : Module.Finite (ZMod p) F :=
    IntermediateField.adjoin.finiteDimensional (hasseRoot_isIntegral p n t ht)
  have : Finite F := Module.finite_of_finite (ZMod p)
  let t₀ : F := ⟨t, IntermediateField.subset_adjoin (ZMod p) {t} (Set.mem_singleton t)⟩
  refine ⟨F, inferInstance, t₀, rfl, ?_⟩
  apply F.subtype.injective
  change F.subtype ((hassePolynomial (K := F) n).eval t₀) = F.subtype 0
  rw [map_zero, ← eval_map_apply]
  change ((hassePolynomial (K := F) n).map (F.subtype : F →+* K)).eval t = 0
  rw [hassePolynomial_map (K := F) (L := K) (F.subtype : F →+* K)]
  exact ht

/-- An integral parameter of a nonsingular Legendre model has an actual
elliptic model over a finite subfield, with the displayed coefficient map. -/
theorem exists_finite_legendre_model_of_integral
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (hp : 2 < p) (t : K) [(curve t).IsElliptic]
    (ht : IsIntegral (ZMod p) t) :
    ∃ (F : IntermediateField (ZMod p) K) (_ : Finite F) (t₀ : F)
      (_ : (curve t₀).IsElliptic),
      (t₀ : K) = t ∧ (curve t₀).map (F.subtype : F →+* K) = curve t := by
  let F : IntermediateField (ZMod p) K := IntermediateField.adjoin (ZMod p) {t}
  have : Module.Finite (ZMod p) F := IntermediateField.adjoin.finiteDimensional ht
  have : Finite F := Module.finite_of_finite (ZMod p)
  let t₀ : F := ⟨t, IntermediateField.subset_adjoin (ZMod p) {t}
    (Set.mem_singleton t)⟩
  have ht0 : t₀ ≠ 0 := fun h => elliptic_parameter_ne_zero t (congrArg Subtype.val h)
  have ht1 : t₀ ≠ 1 := fun h => elliptic_parameter_ne_one t (congrArg Subtype.val h)
  have := curve_isElliptic (small_natCast_ne_zero p (k := 2) (by decide) hp) ht0 ht1
  exact ⟨F, inferInstance, t₀, inferInstance, rfl, curve_map F.subtype t₀⟩

end IsogenyAttack.Legendre
