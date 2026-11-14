import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-!
Coordinate automorphisms of short Weierstrass equations. These are stabilizers
for mathlib's actual admissible variable-change action, not arbitrary point-group
automorphisms. Characteristic exclusions are stated as 2 ≠ 0 and 3 ≠ 0.
-/
namespace IsogenyAttack
namespace CurveAutomorphisms

open WeierstrassCurve
variable {F : Type*} [Field F]

/-- The actual Weierstrass equation y² = x³ + A x + B. -/
def shortCurve (A B : F) : WeierstrassCurve F := ⟨0, 0, 0, A, B⟩

instance shortNF (A B : F) : (shortCurve A B).IsShortNF := ⟨rfl, rfl, rfl⟩

/-- Admissible coordinate changes preserving the given short curve. -/
abbrev CoordinateAut (A B : F) :=
  MulAction.stabilizer (VariableChange F) (shortCurve A B)

/-- Stabilizing a short equation forces all translation/shear parameters to vanish. -/
theorem stabilizes_short_iff (A B : F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (C : VariableChange F) :
    C • shortCurve A B = shortCurve A B ↔
      C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧
        ((C.u⁻¹ : Fˣ) : F) ^ 4 * A = A ∧
        ((C.u⁻¹ : Fˣ) : F) ^ 6 * B = B := by
  have hu : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := Units.ne_zero _
  constructor
  · intro h
    have hs : C.s = 0 := by
      have hh := congrArg WeierstrassCurve.a₁ h
      simpa only [variableChange_a₁, shortCurve, zero_add, mul_eq_zero,
        hu, h2, false_or] using hh
    have hr : C.r = 0 := by
      have hh := congrArg WeierstrassCurve.a₂ h
      simpa [variableChange_a₂, shortCurve, hs, mul_eq_zero, hu, h3] using hh
    have ht : C.t = 0 := by
      have hh := congrArg WeierstrassCurve.a₃ h
      simpa [variableChange_a₃, shortCurve, mul_eq_zero, hu, h2] using hh
    refine ⟨hr, hs, ht, ?_, ?_⟩
    · simpa [variableChange_a₄, shortCurve, hr, hs, ht] using congrArg WeierstrassCurve.a₄ h
    · simpa [variableChange_a₆, shortCurve, hr, hs, ht] using congrArg WeierstrassCurve.a₆ h
  · rintro ⟨hr, hs, ht, hA, hB⟩
    simp only [Units.val_inv_eq_inv_val, inv_pow] at hA hB
    ext <;> simp [variableChange_def, shortCurve, hr, hs, ht, hA, hB]

/-- The surviving scalar parameters. -/
def ScalingUnits (A B : F) := {u : Fˣ //
  ((u⁻¹ : Fˣ) : F) ^ 4 * A = A ∧ ((u⁻¹ : Fˣ) : F) ^ 6 * B = B}

/-- Classification as an explicit equivalence; injectivity is the proved
vanishing of r,s,t and surjectivity constructs the actual coordinate change. -/
def shortAutEquivScaling (A B : F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    CoordinateAut A B ≃ ScalingUnits A B where
  toFun C := ⟨C.val.u,
    ((stabilizes_short_iff A B h2 h3 C.val).mp C.property).2.2.2⟩
  invFun u := ⟨⟨u.val, 0, 0, 0⟩,
    (stabilizes_short_iff A B h2 h3 _).mpr ⟨rfl, rfl, rfl, u.property⟩⟩
  left_inv C := by
    apply Subtype.ext
    have hc := (stabilizes_short_iff A B h2 h3 C.val).mp C.property
    apply VariableChange.ext
    · rfl
    · exact hc.1.symm
    · exact hc.2.1.symm
    · exact hc.2.2.1.symm
  right_inv u := rfl

lemma inverse_pow_coefficient (u : Fˣ) (A : F) (n : ℕ) (hA : A ≠ 0) :
    ((u⁻¹ : Fˣ) : F) ^ n * A = A ↔ u ^ n = 1 := by
  have hi : ((u⁻¹ : Fˣ) : F) ^ n * A = A ↔ ((u⁻¹ : Fˣ) : F) ^ n = 1 := by
    constructor
    · intro h
      exact mul_right_cancel₀ hA (by simpa using h)
    · intro h
      rw [h, one_mul]
  rw [hi]
  change ↑((u⁻¹) ^ n) = (1 : F) ↔ u ^ n = 1
  rw [← Units.val_one, Units.val_inj, inv_pow, inv_eq_one]

/-- When A=0 and B≠0, the coordinate automorphism parameters are exactly μ₆. -/
def zeroAEquivRoots (B : F) (hB : B ≠ 0) : ScalingUnits (0 : F) B ≃ rootsOfUnity 6 F :=
  (Equiv.refl Fˣ).subtypeEquiv fun u => by
    simp only [mul_zero, true_and, Equiv.refl_apply]
    rw [inverse_pow_coefficient u B 6 hB]
    exact (mem_rootsOfUnity 6 u).symm

/-- When B=0 and A≠0, the coordinate automorphism parameters are exactly μ₄. -/
def zeroBEquivRoots (A : F) (hA : A ≠ 0) : ScalingUnits A (0 : F) ≃ rootsOfUnity 4 F :=
  (Equiv.refl Fˣ).subtypeEquiv fun u => by
    simp only [mul_zero, and_true, Equiv.refl_apply]
    rw [inverse_pow_coefficient u A 4 hA]
    exact (mem_rootsOfUnity 4 u).symm

/-- The generic case is μ₂ because gcd(4,6)=2. -/
def genericEquivRoots (A B : F) (hA : A ≠ 0) (hB : B ≠ 0) :
    ScalingUnits A B ≃ rootsOfUnity 2 F :=
  (Equiv.refl Fˣ).subtypeEquiv fun u => by
    rw [inverse_pow_coefficient u A 4 hA, inverse_pow_coefficient u B 6 hB,
      ← pow_gcd_eq_one]
    norm_num [mem_rootsOfUnity]

variable [IsAlgClosed F]

theorem card_coordinateAut_zeroA (B : F) (hB : B ≠ 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (CoordinateAut (0 : F) B) = 6 := by
  letI : NeZero (6 : F) := ⟨by have := mul_ne_zero h2 h3; norm_num at this ⊢; exact this⟩
  rw [Nat.card_congr ((shortAutEquivScaling 0 B h2 h3).trans (zeroAEquivRoots B hB))]
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity F 6

theorem card_coordinateAut_zeroB (A : F) (hA : A ≠ 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (CoordinateAut A (0 : F)) = 4 := by
  letI : NeZero (4 : F) := ⟨by have := mul_ne_zero h2 h2; norm_num at this ⊢; exact this⟩
  rw [Nat.card_congr ((shortAutEquivScaling A 0 h2 h3).trans (zeroBEquivRoots A hA))]
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity F 4

theorem card_coordinateAut_generic (A B : F) (hA : A ≠ 0) (hB : B ≠ 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (CoordinateAut A B) = 2 := by
  letI : NeZero (2 : F) := ⟨h2⟩
  rw [Nat.card_congr ((shortAutEquivScaling A B h2 h3).trans (genericEquivRoots A B hA hB))]
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity F 2


omit [IsAlgClosed F] in
lemma short_j_zero_iff (A B : F) [(shortCurve A B).IsElliptic]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (shortCurve A B).j = 0 ↔ A = 0 := by
  have h48 : (48 : F) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 4 h2) h3 using 1; norm_num
  rw [WeierstrassCurve.j_eq_zero_iff, c₄_of_isShortNF]
  change -48 * A = 0 ↔ A = 0
  simp [mul_eq_zero, h48]

omit [IsAlgClosed F] in
lemma short_discriminant_nonzero (A B : F) [(shortCurve A B).IsElliptic] :
    4 * A ^ 3 + 27 * B ^ 2 ≠ 0 := by
  have hd := (shortCurve A B).Δ'.ne_zero
  rw [coe_Δ', Δ_of_isShortNF] at hd
  exact right_ne_zero_of_mul hd

omit [IsAlgClosed F] in
lemma short_j_1728_iff (A B : F) [(shortCurve A B).IsElliptic]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (shortCurve A B).j = 1728 ↔ B = 0 := by
  have h46656 : (46656 : F) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 6 h2) (pow_ne_zero 6 h3) using 1; norm_num
  rw [j_of_isShortNF]
  change 6912 * A ^ 3 / (4 * A ^ 3 + 27 * B ^ 2) = 1728 ↔ B = 0
  rw [div_eq_iff (short_discriminant_nonzero A B)]
  constructor
  · intro h
    have hz : 46656 * B ^ 2 = 0 := by linear_combination -h
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp (mul_eq_zero.mp hz |>.resolve_left h46656)
  · intro h
    rw [h]
    ring

/-- The exact classical 6/4/2 automorphism count, proved for the actual
Weierstrass coordinate-change stabilizer of every nonsingular short equation. -/
theorem card_coordinateAut_by_j [DecidableEq F] (A B : F) [(shortCurve A B).IsElliptic]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (CoordinateAut A B) =
      if (shortCurve A B).j = 0 then 6 else
        if (shortCurve A B).j = 1728 then 4 else 2 := by
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_contra h
    push Not at h
    have hd := short_discriminant_nonzero A B
    simp [h.1, h.2] at hd
  simp only [short_j_zero_iff A B h2 h3, short_j_1728_iff A B h2 h3]
  by_cases hA : A = 0
  · have hB : B ≠ 0 := hAB.resolve_left (not_not.mpr hA)
    subst A
    simpa using card_coordinateAut_zeroA B hB h2 h3
  · by_cases hB : B = 0
    · subst B
      simpa [hA] using card_coordinateAut_zeroB A hA h2 h3
    · simpa [hA, hB] using card_coordinateAut_generic A B hA hB h2 h3


/-- Coordinate automorphisms of an arbitrary Weierstrass equation. -/
abbrev CurveAut (W : WeierstrassCurve F) := MulAction.stabilizer (VariableChange F) W

omit [IsAlgClosed F] in
/-- Changing Weierstrass coordinates preserves the number of coordinate automorphisms. -/
theorem card_curveAut_variableChange (W : WeierstrassCurve F) (C : VariableChange F) :
    Nat.card (CurveAut W) = Nat.card (CurveAut (C • W)) :=
  Nat.card_congr (MulAction.stabilizerEquivStabilizer (G := VariableChange F)
    (a := W) (g := C) rfl).toEquiv

/-- Every nonsingular Weierstrass equation over an algebraically closed field
of characteristic different from 2 and 3 has exactly 6, 4 or 2 admissible
coordinate automorphisms, determined solely by its actual j-invariant. -/
theorem card_curveAut_by_j [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (CurveAut W) = if W.j = 0 then 6 else if W.j = 1728 then 4 else 2 := by
  letI : Invertible (2 : F) := invertibleOfNonzero h2
  letI : Invertible (3 : F) := invertibleOfNonzero h3
  let C := W.toShortNF
  let W' := C • W
  have hs : W' = shortCurve W'.a₄ W'.a₆ := by
    ext <;> simp [shortCurve]
  haveI : (shortCurve W'.a₄ W'.a₆).IsElliptic := hs ▸ inferInstance
  calc
    Nat.card (CurveAut W) = Nat.card (CurveAut W') := card_curveAut_variableChange W C
    _ = Nat.card (CoordinateAut W'.a₄ W'.a₆) := by rw [hs]; rfl
    _ = if (shortCurve W'.a₄ W'.a₆).j = 0 then 6 else
          if (shortCurve W'.a₄ W'.a₆).j = 1728 then 4 else 2 :=
      card_coordinateAut_by_j W'.a₄ W'.a₆ h2 h3
    _ = if W.j = 0 then 6 else if W.j = 1728 then 4 else 2 := by
      have hj : (shortCurve W'.a₄ W'.a₆).j = W.j := by
        have hj' : W'.j = W.j := variableChange_j W C
        simpa only [← hs] using hj'
      rw [hj]


/-- Actual coordinate changes from one Weierstrass model to another. -/
def CoordinateIso (W V : WeierstrassCurve F) := {C : VariableChange F // C • W = V}

omit [IsAlgClosed F] in
/-- After choosing one coordinate isomorphism, all others form an explicit
copy of the source automorphism group. -/
def coordinateIsoEquivAut (W V : WeierstrassCurve F) (C₀ : VariableChange F)
    (h₀ : C₀ • W = V) : CoordinateIso W V ≃ CurveAut W where
  toFun C := ⟨C₀⁻¹ * C.val, by
    change (C₀⁻¹ * C.val) • W = W
    rw [mul_smul, C.property, ← h₀, inv_smul_smul]⟩
  invFun U := ⟨C₀ * U.val, by
    rw [mul_smul, U.property, h₀]⟩
  left_inv C := by apply Subtype.ext; simp
  right_inv U := by apply Subtype.ext; simp

/-- Equal j-invariants produce actual coordinate isomorphisms over an
algebraically closed field, and their cardinal is exactly the source stabilizer. -/
theorem card_coordinateIso (W V : WeierstrassCurve F) [W.IsElliptic] [V.IsElliptic]
    (hj : W.j = V.j) : Nat.card (CoordinateIso W V) = Nat.card (CurveAut W) := by
  obtain ⟨C₀, h₀⟩ := exists_variableChange_of_j_eq W V hj
  exact Nat.card_congr (coordinateIsoEquivAut W V C₀ h₀)

/-- The exact number of coordinate isomorphisms between equal-j models. -/
theorem card_coordinateIso_by_j [DecidableEq F] (W V : WeierstrassCurve F)
    [W.IsElliptic] [V.IsElliptic] (hj : W.j = V.j)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (CoordinateIso W V) =
      if W.j = 0 then 6 else if W.j = 1728 then 4 else 2 := by
  rw [card_coordinateIso W V hj, card_curveAut_by_j W h2 h3]

end CurveAutomorphisms
end IsogenyAttack
