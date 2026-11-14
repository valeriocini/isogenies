/-
The prime-rank-bound argument is adapted from LANA Project's
EllipticCurves/Torsion/TorsionCountCharFree.lean (Apache 2.0), commit
e70086a9c442dcfe76152fa03777091c50985d43.
See Vendor/EllipticCurves/LICENSE and SOURCE.md for attribution.
-/
import IsogenyAttack.Vendor.Iut.Torsion.Count
import IsogenyAttack.Vendor.EllipticCurves.Torsion.AbelianStructure

/-!
# Prime-to-characteristic torsion of actual elliptic-curve points

The group is mathlib's nonsingular affine point group, and the cardinality
input is proved by division polynomials in the imported `Count` module.
There is no assumed torsion basis or cardinality. The field has characteristic
different from two, the equation has `a₁ = a₃ = 0`, and the index is nonzero
in the field. These hypotheses include the Montgomery and Legendre models
used in the attack for odd characteristic.
-/

namespace IsogenyAttack

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [NeZero (2 : K)] [IsAlgClosed K]
  {W : Affine K} [W.IsElliptic] (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)

include ha₁ ha₃

open scoped Classical in
/-- The prime torsion inside `E[n]` has rank at most two. -/
theorem elliptic_torsion_prime_rank_bound {n : ℕ} (hn : (n : K) ≠ 0)
    (q : ℕ) (hq : q.Prime) :
    Nat.card {a : AddSubgroup.torsionBy W.Point n // q • a = 0} ≤ q ^ 2 := by
  classical
  by_cases hdvd : q ∣ n
  · have hqK : (q : K) ≠ 0 := by
      intro hz
      obtain ⟨k, rfl⟩ := hdvd
      exact hn (by push_cast; rw [hz, zero_mul])
    have hcard := Iut.Torsion.card_torsionBy_eq_sq ha₁ ha₃ q hqK
    haveI : Finite (AddSubgroup.torsionBy W.Point q) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hq.ne_zero)
    let f : {a : AddSubgroup.torsionBy W.Point n // q • a = 0} →
        AddSubgroup.torsionBy W.Point q := fun a =>
      ⟨a.1.1, AddSubgroup.torsionBy.nsmul_iff.mpr (congrArg Subtype.val a.2)⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : AddSubgroup.torsionBy W.Point q => (z : W.Point)) hab
    calc
      Nat.card {a : AddSubgroup.torsionBy W.Point n // q • a = 0}
        ≤ Nat.card (AddSubgroup.torsionBy W.Point q) := Nat.card_le_card_of_injective f hf
      _ = q ^ 2 := hcard
  · have hcop : IsCoprime (q : ℤ) (n : ℤ) := by
      have hnat : Nat.Coprime q n := hq.coprime_iff_not_dvd.mpr hdvd
      simpa using Nat.isCoprime_iff_coprime.mpr hnat
    obtain ⟨u, v, huv⟩ := hcop
    have hzero : ∀ a : AddSubgroup.torsionBy W.Point n, q • a = 0 → a = 0 := by
      intro a ha
      have hqa : (q : ℤ) • a = 0 := by rw [natCast_zsmul, ha]
      have hna : (n : ℤ) • a = 0 := by
        rw [natCast_zsmul]
        exact AddSubgroup.torsionBy.nsmul a
      have h1 : (1 : ℤ) • a = 0 := by
        rw [← huv, add_smul, mul_smul, mul_smul, hqa, hna, smul_zero, smul_zero, add_zero]
      simpa using h1
    have hcard1 : Nat.card {a : AddSubgroup.torsionBy W.Point n // q • a = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hzero a.1 a.2).trans (hzero b.1 b.2).symm)⟩,
        ⟨⟨0, by simp⟩⟩⟩
    rw [hcard1]
    exact Nat.one_le_pow 2 q hq.pos

open scoped Classical in
/-- The full rank-two torsion theorem for a Weierstrass equation with
`a₁ = a₃ = 0`, over an algebraically closed field of characteristic different
from two, at every index nonzero in the field. -/
theorem elliptic_torsion_rank_two {n : ℕ} (hn : (n : K) ≠ 0) :
    Nonempty (AddSubgroup.torsionBy W.Point n ≃+ ZMod n × ZMod n) := by
  have hcard := Iut.Torsion.card_torsionBy_eq_sq ha₁ ha₃ n hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn (by simp))
  haveI : Finite (AddSubgroup.torsionBy W.Point n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hn0.ne')
  exact AddCommGroup.equiv_zmod_sq_of_card_sq hn0 AddSubgroup.torsionBy.nsmul hcard
    (elliptic_torsion_prime_rank_bound ha₁ ha₃ hn)

end IsogenyAttack
