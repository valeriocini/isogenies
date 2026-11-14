import IsogenyAttack.MontgomeryGeometry
import IsogenyAttack.LegendreCurve
import IsogenyAttack.LegendreMaximal
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Supersingular
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Composition

/-! The rational Montgomery-to-Legendre isogeny. Its coordinate pullback is
constructed directly; the pole of the first coordinate proves pointedness. -/

namespace IsogenyAttack.Montgomery

open WeierstrassCurve.Affine TauCeti

variable {K : Type*} [Field K]

def legendreParameter (A : K) : K := (2 - A) / 4

lemma legendreParameter_ne_zero {A : K} (h2 : (2 : K) ≠ 0) (hA : A ^ 2 ≠ 4) :
    legendreParameter A ≠ 0 := by
  intro h
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h' : (2 : K) - A = 0 := (div_eq_zero_iff).mp h |>.resolve_right h4
  apply hA
  rw [← sub_eq_zero.mp h']
  ring

lemma legendreParameter_ne_one {A : K} (h2 : (2 : K) ≠ 0) (hA : A ^ 2 ≠ 4) :
    legendreParameter A ≠ 1 := by
  intro h
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h' : (2 : K) - A = 4 := (div_eq_one_iff_eq h4).mp h
  have hA' : A = -2 := by linear_combination -h'
  apply hA
  rw [hA']
  ring

lemma legendre_map_equation {A x y : K} (h2 : (2 : K) ≠ 0) (hx : x ≠ 0)
    (he : y ^ 2 = x ^ 3 + A * x ^ 2 + x) :
    (y * (x ^ 2 - 1) / (8 * x ^ 2)) ^ 2 =
      ((x + 1) ^ 2 / (4 * x)) ^ 3 -
        (legendreParameter A + 1) * ((x + 1) ^ 2 / (4 * x)) ^ 2 +
        legendreParameter A * ((x + 1) ^ 2 / (4 * x)) := by
  dsimp [legendreParameter]
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h8 : (8 : K) ≠ 0 := by convert pow_ne_zero 3 h2 using 1; norm_num
  field_simp
  rw [he]
  ring

noncomputable def legendreMapX (A : K) : (curve A).toAffine.FunctionField :=
  ((curve A).toAffine.genericX + 1) ^ 2 / (4 * (curve A).toAffine.genericX)

noncomputable def legendreMapY (A : K) : (curve A).toAffine.FunctionField :=
  (curve A).toAffine.genericY * ((curve A).toAffine.genericX ^ 2 - 1) /
    (8 * (curve A).toAffine.genericX ^ 2)

lemma legendreMap_equation (A : K) (h2 : (2 : K) ≠ 0) :
    ((Legendre.curve (legendreParameter A)).baseChange
      (curve A).toAffine.FunctionField).toAffine.Equation
      (legendreMapX A) (legendreMapY A) := by
  let W := (curve A).toAffine
  have hx : W.genericX ≠ 0 := by
    intro hx
    have hv := W.one_lt_infinityPlace_X
    rw [← genericX_eq_algebraMap, hx, map_zero] at hv
    exact (not_lt_of_ge (by simp)) hv
  have he := equation_genericX_genericY W
  rw [equation_iff] at he
  change W.genericY ^ 2 + (algebraMap K W.FunctionField) 0 * W.genericX * W.genericY +
      (algebraMap K W.FunctionField) 0 * W.genericY =
      W.genericX ^ 3 + (algebraMap K W.FunctionField) A * W.genericX ^ 2 +
      (algebraMap K W.FunctionField) 1 * W.genericX + (algebraMap K W.FunctionField) 0 at he
  simp only [map_zero, map_one, zero_mul, add_zero, one_mul] at he
  have h2' : (2 : W.FunctionField) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K W.FunctionField)).mpr h2
  have h := legendre_map_equation h2' hx he
  have hp : (algebraMap K W.FunctionField) (legendreParameter A) =
      legendreParameter ((algebraMap K W.FunctionField) A) := by
    dsimp only [legendreParameter]
    rw [map_div₀, map_sub, map_ofNat, map_ofNat]
  rw [equation_iff]
  change legendreMapY A ^ 2 + (algebraMap K W.FunctionField) 0 * legendreMapX A * legendreMapY A +
      (algebraMap K W.FunctionField) 0 * legendreMapY A =
      legendreMapX A ^ 3 + (algebraMap K W.FunctionField) (-(legendreParameter A + 1)) *
      legendreMapX A ^ 2 + (algebraMap K W.FunctionField) (legendreParameter A) *
      legendreMapX A + (algebraMap K W.FunctionField) 0
  simp only [map_zero, map_one, map_neg, map_add, hp, zero_mul, add_zero, neg_mul,
    ← sub_eq_add_neg]
  exact h

lemma legendreMapX_pole (A : K) (h2 : (2 : K) ≠ 0) :
    1 < (curve A).toAffine.infinityPlace (legendreMapX A) := by
  let W := (curve A).toAffine
  let v := W.infinityPlace
  have hx : 1 < v W.genericX := by
    simpa only [genericX_eq_algebraMap] using W.one_lt_infinityPlace_X
  have hx0 : v W.genericX ≠ 0 := ne_of_gt (lt_trans (by simp) hx)
  have hadd : v (W.genericX + 1) = v W.genericX := by
    apply v.map_add_eq_of_lt_left
    simpa only [map_one] using hx
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have hval4 : v (4 : W.FunctionField) = 1 := by
    simpa only [map_ofNat] using Valuation.IsTrivialOn.eq_one (v := v) (4 : K) h4
  change 1 < v ((W.genericX + 1) ^ 2 / (4 * W.genericX))
  rw [map_div₀, map_pow, map_mul, hadd, hval4, one_mul, pow_two, mul_div_cancel_right₀ _ hx0]
  exact hx

/-- The actual rational isogeny from the B=1 Montgomery model to its Legendre quotient. -/
noncomputable def legendreIsogeny (A : K) (h2 : (2 : K) ≠ 0) :
    TauCeti.Isogeny (curve A).toAffine (Legendre.curve (legendreParameter A)).toAffine where
  pullback := CoordinateRing.evalAlgHom (legendreMap_equation A h2)
  mapsInfinity := by
    apply CoordinatePullback.mapsInfinity_of_one_lt_infinityPlace _
      (AdjoinRoot.of (Legendre.curve (legendreParameter A)).toAffine.polynomial Polynomial.X)
    rw [CoordinateRing.evalAlgHom_of_X]
    exact legendreMapX_pole A h2

end IsogenyAttack.Montgomery

namespace IsogenyAttack

open WeierstrassCurve TauCeti TauCeti.Isogeny

/-- Isogenous elliptic curves over a finite field have the same point count.
This is the degree argument using the naturality of Frobenius. -/
theorem isogeny_pointCount_eq {F : Type*} [Field F] [Finite F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁ W₂) : W₁.pointCount = W₂.pointCount := by
  have h := congrArg Hom.degree <| show
      (1 - Hom.ofIsogeny (frobeniusIsogeny W₂)).comp (Hom.ofIsogeny φ) =
        (Hom.ofIsogeny φ).comp (1 - Hom.ofIsogeny (frobeniusIsogeny W₁)) by
    rw [Hom.sub_comp, Hom.comp_sub, Hom.frobenius_comp, Hom.one_def, Hom.one_def,
      Hom.id_comp, Hom.comp_id]
  rw [Hom.degree_comp, Hom.degree_comp, Hom.degree_ofIsogeny, mul_comm] at h
  have he := (Nat.eq_of_mul_eq_mul_left φ.degree_pos h).symm
  simpa only [← ofIsogeny_oneSubFrobeniusIsogeny, Hom.degree_ofIsogeny,
    degree_oneSubFrobeniusIsogeny_eq_pointCount] using he

namespace Montgomery

variable {K : Type*} [Field K] [Finite K]

/-- The rational Montgomery-to-Legendre isogeny preserves point counts. -/
theorem pointCount_eq_legendre (A : K) (h2 : (2 : K) ≠ 0) (hA : A ^ 2 ≠ 4) :
    (curve A).pointCount = (Legendre.curve (legendreParameter A)).pointCount := by
  let := curve_isElliptic h2 hA
  let := Legendre.curve_isElliptic h2 (legendreParameter_ne_zero h2 hA)
    (legendreParameter_ne_one h2 hA)
  exact isogeny_pointCount_eq (legendreIsogeny A h2)

/-- The same rational isogeny preserves supersingularity over a finite field. -/
theorem supersingular_legendre (A : K) (h2 : (2 : K) ≠ 0) (hA : A ^ 2 ≠ 4)
    (p : ℕ) [ExpChar K p] (hss : (curve A).IsSupersingular p) :
    (Legendre.curve (legendreParameter A)).IsSupersingular p := by
  let := curve_isElliptic h2 hA
  let := Legendre.curve_isElliptic h2 (legendreParameter_ne_zero h2 hA)
    (legendreParameter_ne_one h2 hA)
  rw [WeierstrassCurve.isSupersingular_iff_dvd_frobeniusTrace] at hss ⊢
  have he : (curve A).frobeniusTrace = (Legendre.curve (legendreParameter A)).frobeniusTrace := by
    rw [WeierstrassCurve.frobeniusTrace_def, WeierstrassCurve.frobeniusTrace_def,
      pointCount_eq_legendre A h2 hA]
  rwa [← he]

/-- Every supersingular B=1 Montgomery curve over a field of order `p²`,
with `p ≡ 3 (mod 4)`, is maximal over that field. -/
theorem supersingular_pointCount (A : K) (h2 : (2 : K) ≠ 0) (hA : A ^ 2 ≠ 4)
    (p : ℕ) [ExpChar K p] (hp : 0 < p) (hp4 : p % 4 = 3)
    (hcard : Nat.card K = p ^ 2) (hss : (curve A).IsSupersingular p) :
    (curve A).pointCount = (p + 1) ^ 2 := by
  let := Legendre.curve_isElliptic h2 (legendreParameter_ne_zero h2 hA)
    (legendreParameter_ne_one h2 hA)
  rw [pointCount_eq_legendre A h2 hA]
  exact Legendre.supersingular_pointCount (legendreParameter A) hp hp4 hcard
    (supersingular_legendre A h2 hA p hss)

theorem supersingular_card_point (A : K) (h2 : (2 : K) ≠ 0) (hA : A ^ 2 ≠ 4)
    (p : ℕ) [ExpChar K p] (hp : 0 < p) (hp4 : p % 4 = 3)
    (hcard : Nat.card K = p ^ 2) (hss : (curve A).IsSupersingular p) :
    Nat.card (curve A).toAffine.Point = (p + 1) ^ 2 := by
  let := curve_isElliptic h2 hA
  rw [← (curve A).pointCount_eq_card_point]
  exact supersingular_pointCount A h2 hA p hp hp4 hcard hss

/-- The Frobenius endomorphism of a supersingular B=1 Montgomery curve over
`𝔽_(p²)` is the negative scalar `[-p]` when `p ≡ 3 (mod 4)`. Naturality of
Frobenius and cancellation of the rational isogeny transfer the Legendre result. -/
theorem supersingular_frobenius_negative (A : K) [(curve A).IsElliptic] (h2 : (2 : K) ≠ 0) (hA : A ^ 2 ≠ 4)
    (p : ℕ) [ExpChar K p] (hp : 0 < p) (hp4 : p % 4 = 3)
    (hcard : Nat.card K = p ^ 2) (hss : (curve A).IsSupersingular p) :
    Hom.ofIsogeny (frobeniusIsogeny (curve A).toAffine) =
      -(p : ℤ) • Hom.id (curve A).toAffine := by
  let := curve_isElliptic h2 hA
  let := Legendre.curve_isElliptic h2 (legendreParameter_ne_zero h2 hA)
    (legendreParameter_ne_one h2 hA)
  have hn := Legendre.supersingular_frobenius_negative (legendreParameter A) p hp hp4 hcard
    (supersingular_legendre A h2 hA p hss)
  let f := Hom.ofIsogeny (legendreIsogeny A h2)
  have he : f.comp (Hom.ofIsogeny (frobeniusIsogeny (curve A).toAffine) -
      (-(p : ℤ)) • Hom.id (curve A).toAffine) = 0 := by
    rw [Hom.comp_sub, ← Hom.frobenius_comp, hn, Hom.comp_zsmul, Hom.zsmul_comp,
      Hom.comp_id, Hom.id_comp, sub_self]
  exact sub_eq_zero.mp ((Hom.comp_eq_zero_iff.mp he).resolve_left
    (Hom.ofIsogeny_ne_zero _))

end Montgomery
end IsogenyAttack
