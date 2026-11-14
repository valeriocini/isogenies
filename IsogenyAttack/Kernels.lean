import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Arithmetic Hermite normal forms for prime-to-characteristic kernels.
This file proves finite counting facts; the equivalence with elliptic-curve
kernels is a separate geometric interface. -/

namespace IsogenyAttack

/-- The Hermite normal form with columns `(a,0)` and `(b,e)`. -/
@[ext] structure HNF where
  a : ℕ
  e : ℕ
  b : ℕ
  a_pos : 0 < a
  e_pos : 0 < e
  b_lt : b < a
  deriving DecidableEq

namespace HNF

def degree (x : HNF) : ℕ := x.a * x.e

theorem degree_pos (x : HNF) : 0 < x.degree := Nat.mul_pos x.a_pos x.e_pos

def content (x : HNF) : ℕ := Nat.gcd x.a (Nat.gcd x.e x.b)

def cyclicDegree (x : HNF) : ℕ := x.degree / x.content ^ 2

/-- A concrete scalar lift of one of the `c` cyclic HNFs `(c,1,t)`. -/
def lift (m c t : ℕ) (hm : 0 < m) (hc : 0 < c) (ht : t < c) : HNF where
  a := m * c
  e := m
  b := m * t
  a_pos := Nat.mul_pos hm hc
  e_pos := hm
  b_lt := Nat.mul_lt_mul_of_pos_left ht hm

@[simp] theorem lift_degree (m c t : ℕ) (hm : 0 < m) (hc : 0 < c) (ht : t < c) :
    (lift m c t hm hc ht).degree = m ^ 2 * c := by
  simp only [degree, lift]
  ring

@[simp] theorem lift_content (m c t : ℕ) (hm : 0 < m) (hc : 0 < c) (ht : t < c) :
    (lift m c t hm hc ht).content = m := by
  simp [content, lift]

@[simp] theorem lift_cyclicDegree (m c t : ℕ) (hm : 0 < m) (hc : 0 < c) (ht : t < c) :
    (lift m c t hm hc ht).cyclicDegree = c := by
  simp [cyclicDegree, Nat.ne_of_gt hm]

/-- The scalar and cyclic degree are recoverable, so these witnesses never collide. -/
theorem lift_injective {m c t m' c' t' : ℕ}
    {hm : 0 < m} {hc : 0 < c} {ht : t < c}
    {hm' : 0 < m'} {hc' : 0 < c'} {ht' : t' < c'}
    (h : lift m c t hm hc ht = lift m' c' t' hm' hc' ht') :
    m = m' ∧ c = c' ∧ t = t' := by
  have hme : m = m' := congrArg HNF.e h
  subst m'
  have hca : m * c = m * c' := congrArg HNF.a h
  have htb : m * t = m * t' := congrArg HNF.b h
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hm hca, Nat.eq_of_mul_eq_mul_left hm htb⟩

/-- A row-major code for all HNFs of degree at most `L`. -/
def boundedCode (L : ℕ) (x : {x : HNF // x.degree ≤ L}) : Fin L × Fin L :=
  (⟨x.val.a - 1, by
      have he := x.val.e_pos
      have ha := x.val.a_pos
      have hd := x.property
      dsimp [degree] at hd
      have has : x.val.a - 1 + 1 = x.val.a := Nat.sub_add_cancel ha
      nlinarith⟩,
   ⟨x.val.a * (x.val.e - 1) + x.val.b, by
      have he := x.val.e_pos
      have hb := x.val.b_lt
      have hd := x.property
      dsimp [degree] at hd
      have hes : x.val.e - 1 + 1 = x.val.e := Nat.sub_add_cancel he
      nlinarith⟩)

theorem boundedCode_injective (L : ℕ) : Function.Injective (boundedCode L) := by
  intro x y h
  have ha : x.val.a - 1 = y.val.a - 1 := congrArg (fun z => z.1.val) h
  have hab : x.val.a = y.val.a := by
    have hx := x.val.a_pos
    have hy := y.val.a_pos
    omega
  have hv : x.val.a * (x.val.e - 1) + x.val.b =
      y.val.a * (y.val.e - 1) + y.val.b := congrArg (fun z => z.2.val) h
  have he : x.val.e = y.val.e := by
    have hx := x.val.e_pos
    have hy := y.val.e_pos
    have hxb := x.val.b_lt
    have hyb := y.val.b_lt
    rw [← hab] at hv hyb
    by_contra hh
    rcases lt_or_gt_of_ne hh with hlt | hgt
    · have hs : x.val.e - 1 + 1 ≤ y.val.e - 1 := by omega
      nlinarith
    · have hs : y.val.e - 1 + 1 ≤ x.val.e - 1 := by omega
      nlinarith
  have hb : x.val.b = y.val.b := by
    rw [hab, he] at hv
    omega
  apply Subtype.ext
  exact HNF.ext hab he hb

noncomputable instance boundedFintype (L : ℕ) : Fintype {x : HNF // x.degree ≤ L} :=
  Fintype.ofInjective (boundedCode L) (boundedCode_injective L)

/-- The elementary summatory bound underlying the target-support estimate. -/
theorem bounded_card_le (L : ℕ) :
    Fintype.card {x : HNF // x.degree ≤ L} ≤ L ^ 2 := by
  calc
    _ ≤ Fintype.card (Fin L × Fin L) := Fintype.card_le_of_injective _ (boundedCode_injective L)
    _ = L ^ 2 := by simp [pow_two]

end HNF

/-- Degree-d HNFs: choose a positive divisor `a` and the `a` possible offsets. -/
abbrev Kernel (d : ℕ) := Sigma fun a : {a : ℕ // a ∈ d.divisors} => Fin a.val

def kernelCount (d : ℕ) : ℕ := ∑ a ∈ d.divisors, a

theorem kernelCount_eq_sigma (d : ℕ) : kernelCount d = ArithmeticFunction.sigma 1 d :=
  (ArithmeticFunction.sigma_one_apply d).symm

theorem kernelCount_pos {d : ℕ} (hd : 0 < d) : 0 < kernelCount d := by
  have h : 1 ≤ kernelCount d :=
    Finset.single_le_sum (fun i _ => Nat.zero_le i)
      (Nat.one_mem_divisors.mpr (Nat.ne_of_gt hd))
  omega

theorem kernel_card (d : ℕ) : Fintype.card (Kernel d) = kernelCount d := by
  unfold kernelCount
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Finset.sum_coe_sort d.divisors (fun a : ℕ => a)


namespace Kernel

def toHNF {d : ℕ} (x : Kernel d) : HNF where
  a := x.1.val
  e := d / x.1.val
  b := x.2.val
  a_pos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp x.1.property).1
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp x.1.property).2)
  e_pos := Nat.div_pos (Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp x.1.property).2)
    (Nat.mem_divisors.mp x.1.property).1)
    (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp x.1.property).1
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp x.1.property).2))
  b_lt := x.2.isLt

@[simp] theorem toHNF_degree {d : ℕ} (x : Kernel d) : x.toHNF.degree = d := by
  exact Nat.mul_div_cancel' (Nat.mem_divisors.mp x.1.property).1

def ofHNF {d : ℕ} (x : {x : HNF // x.degree = d}) : Kernel d :=
  ⟨⟨x.val.a, Nat.mem_divisors.mpr ⟨by
      exact (Nat.dvd_mul_right x.val.a x.val.e).trans (dvd_of_eq x.property),
    by
      have h := Nat.mul_pos x.val.a_pos x.val.e_pos
      intro hd
      exact Nat.ne_of_gt h (x.property.trans hd)⟩⟩, ⟨x.val.b, x.val.b_lt⟩⟩

def equivDegree (d : ℕ) : Kernel d ≃ {x : HNF // x.degree = d} where
  toFun x := ⟨x.toHNF, x.toHNF_degree⟩
  invFun := ofHNF
  left_inv x := by
    rcases x with ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    rfl
  right_inv x := by
    apply Subtype.ext
    apply HNF.ext
    · rfl
    · dsimp [toHNF, ofHNF]
      calc
        d / x.val.a = x.val.degree / x.val.a := congrArg (fun n => n / x.val.a) x.property.symm
        _ = x.val.e := by simp [HNF.degree, Nat.ne_of_gt x.val.a_pos]
    · rfl

end Kernel

noncomputable instance degreeFintype (d : ℕ) : Fintype {x : HNF // x.degree = d} :=
  Fintype.ofEquiv (Kernel d) (Kernel.equivDegree d)

theorem degree_card (d : ℕ) : Fintype.card {x : HNF // x.degree = d} = kernelCount d := by
  rw [← Fintype.card_congr (Kernel.equivDegree d), kernel_card]

/-- Explicit disjoint scalar lifts used in the attack. -/
abbrev LiftIndex (M L : ℕ) := Fin M × (Sigma fun c : Fin L => Fin (c.val + 1))

def liftIndexMap {M L : ℕ} (x : LiftIndex M L) : HNF :=
  HNF.lift (x.1.val + 1) (x.2.1.val + 1) x.2.2.val
    (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) x.2.2.isLt

theorem liftIndexMap_injective (M L : ℕ) :
    Function.Injective (@liftIndexMap M L) := by
  intro x y h
  obtain ⟨hm,hc,ht⟩ := HNF.lift_injective h
  rcases x with ⟨⟨m,hmx⟩,⟨⟨c,hcx⟩,⟨t,htx⟩⟩⟩
  rcases y with ⟨⟨m',hmy⟩,⟨⟨c',hcy⟩,⟨t',hty⟩⟩⟩
  dsimp at hm hc ht
  have hm' : m = m' := by omega
  have hc' : c = c' := by omega
  subst m'
  subst c'
  subst t'
  rfl

@[simp] theorem liftIndexMap_cyclicDegree {M L : ℕ} (x : LiftIndex M L) :
    (liftIndexMap x).cyclicDegree = x.2.1.val + 1 := by
  apply HNF.lift_cyclicDegree

theorem liftIndexMap_short {M L : ℕ} (x : LiftIndex M L) :
    (liftIndexMap x).cyclicDegree ≤ L := by
  rw [liftIndexMap_cyclicDegree]
  exact Nat.succ_le_of_lt x.2.1.isLt

theorem liftIndexMap_degree_le {M L : ℕ} (x : LiftIndex M L) :
    (liftIndexMap x).degree ≤ M ^ 2 * L := by
  rw [liftIndexMap, HNF.lift_degree]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.succ_le_of_lt x.1.isLt) 2)
    (Nat.succ_le_of_lt x.2.1.isLt)

theorem liftIndexMap_interior {M L B : ℕ} (h : M ^ 2 * L < B) (x : LiftIndex M L) :
    (liftIndexMap x).degree < B := lt_of_le_of_lt (liftIndexMap_degree_le x) h

/-- Twice the favorable count, with no divisions or rounding. -/
theorem liftIndex_card_twice (M L : ℕ) :
    2 * Fintype.card (LiftIndex M L) = M * L * (L + 1) := by
  have hs : ∀ n : ℕ, 2 * (∑ i : Fin n, (i.val + 1)) = n * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      nlinarith
  simp only [LiftIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  have h := hs L
  nlinarith

theorem liftIndex_card_lower (M L : ℕ) :
    M * L ^ 2 ≤ 2 * Fintype.card (LiftIndex M L) := by
  rw [liftIndex_card_twice]
  nlinarith


namespace HNF

theorem content_pos (x : HNF) : 0 < x.content :=
  Nat.gcd_pos_of_pos_left _ x.a_pos

theorem content_dvd_a (x : HNF) : x.content ∣ x.a := Nat.gcd_dvd_left _ _

theorem content_dvd_e (x : HNF) : x.content ∣ x.e :=
  (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)

theorem content_dvd_b (x : HNF) : x.content ∣ x.b :=
  (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

/-- Divide all entries by their largest common scalar. -/
def strip (x : HNF) : HNF where
  a := x.a / x.content
  e := x.e / x.content
  b := x.b / x.content
  a_pos := Nat.div_pos (Nat.le_of_dvd x.a_pos x.content_dvd_a) x.content_pos
  e_pos := Nat.div_pos (Nat.le_of_dvd x.e_pos x.content_dvd_e) x.content_pos
  b_lt := (Nat.div_lt_iff_lt_mul x.content_pos).mpr (by
    rw [Nat.div_mul_cancel x.content_dvd_a]
    exact x.b_lt)

@[simp] theorem strip_content (x : HNF) : x.strip.content = 1 := by
  change Nat.gcd (x.a / x.content) (Nat.gcd (x.e / x.content) (x.b / x.content)) = 1
  rw [Nat.gcd_div x.content_dvd_e x.content_dvd_b]
  rw [Nat.gcd_div x.content_dvd_a (Nat.gcd_dvd_right _ _)]
  exact Nat.div_self x.content_pos

/-- The determinant changes by the square of the scalar. -/
theorem degree_eq_content_sq_mul_strip (x : HNF) :
    x.degree = x.content ^ 2 * x.strip.degree := by
  have ha : x.content * (x.a / x.content) = x.a := Nat.mul_div_cancel' x.content_dvd_a
  have he : x.content * (x.e / x.content) = x.e := Nat.mul_div_cancel' x.content_dvd_e
  dsimp [degree, strip]
  calc
    x.a * x.e = (x.content * (x.a / x.content)) *
      (x.content * (x.e / x.content)) := by rw [ha, he]
    _ = x.content ^ 2 * (x.a / x.content * (x.e / x.content)) := by ring

@[simp] theorem strip_degree (x : HNF) : x.strip.degree = x.cyclicDegree := by
  unfold cyclicDegree
  rw [degree_eq_content_sq_mul_strip x]
  exact (Nat.mul_div_cancel_left x.strip.degree (pow_pos x.content_pos 2)).symm

theorem cyclicDegree_pos (x : HNF) : 0 < x.cyclicDegree := by
  rw [← strip_degree]
  exact x.strip.degree_pos

theorem cyclicDegree_le_degree (x : HNF) : x.cyclicDegree ≤ x.degree := by
  exact Nat.div_le_self _ _

/-- Multiplication of all HNF entries by `m`, i.e. adding a scalar factor. -/
def scale (m : ℕ) (hm : 0 < m) (x : HNF) : HNF where
  a := m * x.a
  e := m * x.e
  b := m * x.b
  a_pos := Nat.mul_pos hm x.a_pos
  e_pos := Nat.mul_pos hm x.e_pos
  b_lt := Nat.mul_lt_mul_of_pos_left x.b_lt hm

@[simp] theorem scale_content (m : ℕ) (hm : 0 < m) (x : HNF) :
    (scale m hm x).content = m * x.content := by
  simp only [content, scale, Nat.gcd_mul_left]

@[simp] theorem scale_degree (m : ℕ) (hm : 0 < m) (x : HNF) :
    (scale m hm x).degree = m ^ 2 * x.degree := by
  dsimp [degree, scale]
  ring

@[simp] theorem scale_strip (x : HNF) : scale x.content x.content_pos x.strip = x := by
  apply HNF.ext
  · exact Nat.mul_div_cancel' x.content_dvd_a
  · exact Nat.mul_div_cancel' x.content_dvd_e
  · exact Nat.mul_div_cancel' x.content_dvd_b

/-- In a scalar times primitive representation, the scalar is unique. -/
theorem scalar_unique {x y : HNF} {m : ℕ} (hm : 0 < m)
    (hy : y.content = 1) (h : scale m hm y = x) : m = x.content := by
  rw [← h, scale_content, hy, Nat.mul_one]

end HNF

end IsogenyAttack
