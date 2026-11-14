import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Field.Subfield.Basic

/-! The finite subfield cut out by a power of Frobenius, constructed inside
the chosen algebraically closed field and counted by its actual root polynomial. -/
namespace IsogenyAttack
open Polynomial
variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The elements fixed by the r-th iterate of Frobenius form a subfield. -/
def frobeniusFixedField (r : ℕ) : Subfield K :=
  (iterateFrobenius K p r).eqLocusField (RingHom.id K)

@[simp] theorem mem_frobeniusFixedField (r : ℕ) (x : K) :
    x ∈ frobeniusFixedField (K := K) p r ↔ x^(p^r)=x := Iff.rfl

noncomputable def frobeniusFixedFieldEquivRoots [DecidableEq K] (r : ℕ) (hr : r ≠ 0) :
    frobeniusFixedField (K := K) p r ≃
      {x : K // x ∈ (X^(p^r)-X : K[X]).roots.toFinset} := by
  have hpow : 1 < p^r := Nat.one_lt_pow hr (Fact.out : p.Prime).one_lt
  refine Equiv.subtypeEquivProp ?_
  funext x
  apply propext
  simp only [mem_frobeniusFixedField, Multiset.mem_toFinset,
    mem_roots (X_pow_sub_X_ne_zero hpow), IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]

theorem finite_frobeniusFixedField (r : ℕ) (hr : r ≠ 0) :
    Finite (frobeniusFixedField (K := K) p r) := by
  classical
  exact Finite.of_equiv _ (frobeniusFixedFieldEquivRoots p r hr).symm

/-- Inside an algebraically closed field, the Frobenius fixed field has
exactly p^r elements; in particular r=2 constructs the quadratic finite field. -/
theorem card_frobeniusFixedField [IsAlgClosed K] (r : ℕ) (hr : r ≠ 0) :
    Nat.card (frobeniusFixedField (K := K) p r) = p^r := by
  classical
  rw [Nat.card_congr (frobeniusFixedFieldEquivRoots p r hr), Nat.card_eq_fintype_card,
    Fintype.card_coe, Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots (galois_poly_separable p (p^r) (dvd_pow_self p hr))),
    IsAlgClosed.card_roots_eq_natDegree,
    natDegree_X_pow_sub_X (Nat.one_lt_pow hr (Fact.out : p.Prime).one_lt)]

end IsogenyAttack
