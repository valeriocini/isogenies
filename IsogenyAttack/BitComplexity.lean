import IsogenyAttack.Attack
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
A bit-list implementation of the degree test. Bits are least-significant first.
The explicit work counter charges constant Boolean/list work per recursive round
and linear work for lengths/fuel selection. It is not a formal simulation by a
Turing machine, and it does not supply the paper's isogeny representation decoder.
-/
namespace IsogenyAttack.BitComplexity

/-- A result with an explicit Boolean/list work charge. -/
structure Computation (α : Type) where
  result : α
  work : ℕ

def bit (b : Bool) : ℕ := if b then 1 else 0

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => bit b + 2 * value bs

def sumBit (a b c : Bool) : Bool := xor (xor a b) c

def carryBit (a b c : Bool) : Bool := (a && b) || (c && (a || b))

lemma fullAdder (a b c : Bool) :
    bit (sumBit a b c) + 2 * bit (carryBit a b c) = bit a + bit b + bit c := by
  cases a <;> cases b <;> cases c <;> decide

/-- A fixed-fuel full adder. Zero padding does not change numerical value. -/
def addCarry : ℕ → List Bool → List Bool → Bool → Computation (List Bool)
  | 0, _, _, c => ⟨[c], 1⟩
  | n+1, xs, ys, c =>
    let a := xs.headD false
    let b := ys.headD false
    let r := addCarry n xs.tail ys.tail (carryBit a b c)
    ⟨sumBit a b c :: r.result, r.work + 14⟩

lemma addCarry_length (n : ℕ) (xs ys : List Bool) (c : Bool) :
    (addCarry n xs ys c).result.length = n + 1 := by
  induction n generalizing xs ys c with
  | zero => simp [addCarry]
  | succ n ih => simp [addCarry, ih]

lemma addCarry_work (n : ℕ) (xs ys : List Bool) (c : Bool) :
    (addCarry n xs ys c).work = 14 * n + 1 := by
  induction n generalizing xs ys c with
  | zero => simp [addCarry]
  | succ n ih => simp [addCarry, ih]; omega

lemma addCarry_correct (n : ℕ) (xs ys : List Bool) (c : Bool)
    (hx : xs.length ≤ n) (hy : ys.length ≤ n) :
    value (addCarry n xs ys c).result = value xs + value ys + bit c := by
  induction n generalizing xs ys c with
  | zero =>
    have hx' : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy' : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs; subst ys
    simp [addCarry, value]
  | succ n ih =>
    have hxt : xs.tail.length ≤ n := by simpa using Nat.sub_le_sub_right hx 1
    have hyt : ys.tail.length ≤ n := by simpa using Nat.sub_le_sub_right hy 1
    have hrec := ih xs.tail ys.tail (carryBit (xs.headD false) (ys.headD false) c) hxt hyt
    have hxv : value xs = bit (xs.headD false) + 2 * value xs.tail := by cases xs <;> simp [value, bit]
    have hyv : value ys = bit (ys.headD false) + 2 * value ys.tail := by cases ys <;> simp [value, bit]
    simp only [addCarry, value]
    rw [hrec]
    have h := fullAdder (xs.headD false) (ys.headD false) c
    omega

/-- Length/fuel bookkeeping is charged linearly; full-adder rounds have charge14. -/
def addBits (xs ys : List Bool) : Computation (List Bool) :=
  let r := addCarry (max xs.length ys.length) xs ys false
  ⟨r.result, r.work + 3 * (xs.length + ys.length) + 4⟩

lemma addBits_correct (xs ys : List Bool) :
    value (addBits xs ys).result = value xs + value ys := by
  simpa [addBits, bit] using addCarry_correct (max xs.length ys.length) xs ys false
    (le_max_left _ _) (le_max_right _ _)

lemma addBits_length (xs ys : List Bool) :
    (addBits xs ys).result.length = max xs.length ys.length + 1 :=
  addCarry_length _ _ _ _

lemma addBits_work_le (xs ys : List Bool) :
    (addBits xs ys).work ≤ 17 * (xs.length + ys.length) + 5 := by
  simp only [addBits, addCarry_work]
  have hm : max xs.length ys.length ≤ xs.length + ys.length := max_le (by omega) (by omega)
  omega

/-- Schoolbook multiplication uses one shifted recursive product and one bit adder. -/
def mulBits : List Bool → List Bool → Computation (List Bool)
  | [], _ => ⟨[], 1⟩
  | b :: xs, ys =>
    let r := mulBits xs ys
    let a := addBits (if b then ys else []) (false :: r.result)
    ⟨a.result, r.work + a.work + 4⟩

lemma mulBits_correct (xs ys : List Bool) :
    value (mulBits xs ys).result = value xs * value ys := by
  induction xs with
  | nil => simp [mulBits, value]
  | cons b xs ih =>
    simp only [mulBits, addBits_correct, value, bit, Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [ih]
    cases b <;> simp [value] <;> ring

lemma mulBits_length_le (xs ys : List Bool) :
    (mulBits xs ys).result.length ≤ 2 * xs.length + ys.length := by
  induction xs with
  | nil => simp [mulBits]
  | cons b xs ih =>
    simp only [mulBits, addBits_length, List.length_cons]
    have hfirst : (if b then ys else []).length ≤ ys.length := by cases b <;> simp
    have hm : max (if b then ys else []).length ((mulBits xs ys).result.length + 1) ≤
        2 * xs.length + ys.length + 1 := max_le (by omega) (by omega)
    omega

lemma mulBits_work_le (xs ys : List Bool) :
    (mulBits xs ys).work ≤ 64 * (xs.length + ys.length + 1) ^ 2 := by
  induction xs with
  | nil => simp only [mulBits, List.length_nil, zero_add]; nlinarith [Nat.zero_le ys.length]
  | cons b xs ih =>
    have ha := addBits_work_le (if b then ys else []) (false :: (mulBits xs ys).result)
    have hl := mulBits_length_le xs ys
    have hfirst : (if b then ys else []).length ≤ ys.length := by cases b <;> simp
    simp only [List.length_cons] at ha
    simp only [mulBits, List.length_cons]
    nlinarith

/-- Comparison returns (less-or-equal, equal), scanning the higher bits first. -/
def compareFuel : ℕ → List Bool → List Bool → Computation (Bool × Bool)
  | 0, _, _ => ⟨(true, true), 1⟩
  | n+1, xs, ys =>
    let a := xs.headD false
    let b := ys.headD false
    let r := compareFuel n xs.tail ys.tail
    ⟨((if r.result.2 then (!a || b) else r.result.1),
      r.result.2 && (a == b)), r.work + 12⟩

lemma compareFuel_work (n : ℕ) (xs ys : List Bool) :
    (compareFuel n xs ys).work = 12 * n + 1 := by
  induction n generalizing xs ys with
  | zero => simp [compareFuel]
  | succ n ih => simp [compareFuel, ih]; omega

lemma compareFuel_correct (n : ℕ) (xs ys : List Bool)
    (hx : xs.length ≤ n) (hy : ys.length ≤ n) :
    ((compareFuel n xs ys).result.1 = true ↔ value xs ≤ value ys) ∧
    ((compareFuel n xs ys).result.2 = true ↔ value xs = value ys) := by
  induction n generalizing xs ys with
  | zero =>
    have hx' : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy' : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs; subst ys
    simp [compareFuel, value]
  | succ n ih =>
    have hxt : xs.tail.length ≤ n := by simpa using Nat.sub_le_sub_right hx 1
    have hyt : ys.tail.length ≤ n := by simpa using Nat.sub_le_sub_right hy 1
    obtain ⟨hle, heq⟩ := ih xs.tail ys.tail hxt hyt
    have hxv : value xs = bit (xs.headD false) + 2 * value xs.tail := by cases xs <;> simp [value, bit]
    have hyv : value ys = bit (ys.headD false) + 2 * value ys.tail := by cases ys <;> simp [value, bit]
    simp only [compareFuel]
    cases ha : xs.headD false <;> cases hb : ys.headD false <;>
      cases he : (compareFuel n xs.tail ys.tail).result.2 <;>
      cases hl : (compareFuel n xs.tail ys.tail).result.1 <;>
      simp_all [bit] <;> omega

/-- Wrapper charging linear traversal for the lengths and fuel. -/
def leBits (xs ys : List Bool) : Computation Bool :=
  let r := compareFuel (max xs.length ys.length) xs ys
  ⟨r.result.1, r.work + 3 * (xs.length + ys.length) + 4⟩

lemma leBits_correct (xs ys : List Bool) :
    (leBits xs ys).result = true ↔ value xs ≤ value ys :=
  (compareFuel_correct _ _ _ (le_max_left _ _) (le_max_right _ _)).1

lemma leBits_work_le (xs ys : List Bool) :
    (leBits xs ys).work ≤ 15 * (xs.length + ys.length) + 5 := by
  simp only [leBits, compareFuel_work]
  have hm : max xs.length ys.length ≤ xs.length + ys.length := max_le (by omega) (by omega)
  omega

/-- Division-free bit implementation: accept exactly when 4*s*s*c ≤ B. -/
def testBits (B s c : List Bool) : Computation Bool :=
  let ss := mulBits s s
  let ssc := mulBits ss.result c
  let cmp := leBits (false :: false :: ssc.result) B
  ⟨cmp.result, ss.work + ssc.work + cmp.work + 2⟩

lemma testBits_product_spec (B s c : List Bool) :
    (testBits B s c).result = true ↔ 4 * value s ^ 2 * value c ≤ value B := by
  simp only [testBits, leBits_correct, value, bit, Bool.false_eq_true, ↓reduceIte,
    zero_add, mulBits_correct]
  ring_nf

/-- Correctness for the same threshold as `publicTest`, for positive s. -/
theorem testBits_correct (B s c : List Bool) (hs : 0 < value s) :
    (testBits B s c).result = publicTest (value B) (value s) (some (value c)) := by
  apply Bool.eq_iff_iff.mpr
  rw [testBits_product_spec, publicTest_some]
  unfold threshold
  rw [Nat.le_div_iff_mul_le (by positivity : 0 < 4 * value s ^ 2)]
  constructor <;> intro h <;> nlinarith

/-- A uniform quadratic bound in the total number of input bits. -/
theorem testBits_work_le (B s c : List Bool) :
    (testBits B s c).work ≤ 8192 * (B.length + s.length + c.length + 1) ^ 2 := by
  have hs := mulBits_work_le s s
  have hss := mulBits_length_le s s
  have hc := mulBits_work_le (mulBits s s).result c
  have hsc := mulBits_length_le (mulBits s s).result c
  have hb := leBits_work_le (false :: false :: (mulBits (mulBits s s).result c).result) B
  simp only [List.length_cons] at hb
  have hN : (mulBits s s).result.length + c.length + 1 ≤
      3 * (B.length + s.length + c.length + 1) := by omega
  have hN' : s.length + s.length + 1 ≤
      2 * (B.length + s.length + c.length + 1) := by omega
  have hsquare := Nat.pow_le_pow_left hN 2
  have hsquare' := Nat.pow_le_pow_left hN' 2
  simp only [testBits]
  nlinarith

/-- Failure is rejected without performing any arithmetic. -/
def testBitsOption (B s : List Bool) : Option (List Bool) → Computation Bool
  | none => ⟨false, 1⟩
  | some c => let r := testBits B s c; ⟨r.result, r.work + 1⟩

theorem testBitsOption_correct (B s : List Bool) (c : Option (List Bool))
    (hs : 0 < value s) :
    (testBitsOption B s c).result =
      publicTest (value B) (value s) (c.map value) := by
  cases c with
  | none => rfl
  | some c => exact testBits_correct B s c hs

theorem testBitsOption_work_le (B s : List Bool) (c : Option (List Bool)) :
    (testBitsOption B s c).work ≤
      8192 * (B.length + s.length + (c.map List.length).getD 0 + 1) ^ 2 + 1 := by
  cases c with
  | none => simp [testBitsOption]
  | some c =>
    have h := testBits_work_le B s c
    simpa only [testBitsOption, Option.map_some, Option.getD_some] using Nat.add_le_add_right h 1

/-- The value function agrees with the standard binary representation. -/
@[simp] theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [value, ih]
    cases b <;> simp [bit, Nat.bit, Nat.add_comm]

/-- Correctness on canonical binary inputs for arbitrary positive parameter s. -/
theorem testBits_nat_correct (B s c : ℕ) (hs : 0 < s) :
    (testBits B.bits s.bits c.bits).result = publicTest B s (some c) := by
  simpa using testBits_correct B.bits s.bits c.bits (by simpa using hs)

/-- Quadratic work bound in the standard binary lengths of the three inputs. -/
theorem testBits_work_le_size (B s c : ℕ) :
    (testBits B.bits s.bits c.bits).work ≤
      8192 * (B.size + s.size + c.size + 1) ^ 2 := by
  simpa only [Nat.size_eq_bits_len] using testBits_work_le B.bits s.bits c.bits

end IsogenyAttack.BitComplexity
