import IsogenyAttack.PublicFullAttack

/-! A first-hint adversary on arbitrary positive-length transcripts. Later
hints and their fresh challenges belong to unrestricted conditional coins. -/

namespace IsogenyAttack.TranscriptEncoding

open PublicObservation BitComplexity

/-- A whole q-hint transcript channel. Only its first slot must decode to
the actual first degree. Every other slot, later challenge, and correlation
may be chosen by the conditional transcript law. -/
structure Channel {α : Type*} (E : PolynomialDegreeDecoder)
    (degree : α → Option ℕ) (q : ℕ) (hq : 0 < q) where
  coins : α → Type
  finite : ∀ a, Fintype (coins a)
  law : ∀ a, @FiniteLaw (coins a) (finite a)
  encode : ∀ a, coins a → Fin q → Option (List Bool)
  valid : ∀ a r, PublicFullAttack.decoded E (encode a r ⟨0, hq⟩) = degree a

attribute [instance] Channel.finite

/-- Reading slot zero turns a full transcript channel into the previously
verified public encoding channel. No condition on later slots is needed. -/
def Channel.firstChannel {α : Type*} {E : PolynomialDegreeDecoder}
    {degree : α → Option ℕ} {q : ℕ} {hq : 0 < q}
    (C : Channel E degree q hq) : PublicFullAttack.EncodingChannel E degree where
  coins := C.coins
  finite := C.finite
  law := C.law
  encode a r := C.encode a r ⟨0, hq⟩
  valid := C.valid

/-- The transcript adversary reads only the first hint's public encoding. -/
def run (E : PolynomialDegreeDecoder) (B s q : ℕ) (hq : 0 < q)
    (transcript : Fin q → Option (List Bool)) : BitComplexity.Computation Bool :=
  PublicFullAttack.run E B s (transcript ⟨0, hq⟩)

theorem run_eq_of_first_eq (E : PolynomialDegreeDecoder) (B s q : ℕ) (hq : 0 < q)
    (x y : Fin q → Option (List Bool)) (h : x ⟨0, hq⟩ = y ⟨0, hq⟩) :
    run E B s q hq x = run E B s q hq y := by
  simp only [run, h]

noncomputable def acceptance {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E : PolynomialDegreeDecoder) (degree : α → Option ℕ)
    (q : ℕ) (hq : 0 < q) (C : Channel E degree q hq) (B s : ℕ) : ℝ :=
  (P.dependentBind C.coins C.law).eventMass
    (fun x => (run E B s q hq (C.encode x.1 x.2)).result = true)

theorem acceptance_eq_firstChannel {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E : PolynomialDegreeDecoder) (degree : α → Option ℕ)
    (q : ℕ) (hq : 0 < q) (C : Channel E degree q hq) (B s : ℕ) :
    acceptance P E degree q hq C B s =
      PublicFullAttack.acceptance P E degree C.firstChannel B s := rfl

/-- For any positive transcript length, the acceptance probability is exactly
the base first-degree event, including protocol failures. The base outcome may
contain the key and first challenge; subsequent challenges are channel coins. -/
theorem acceptance_eq {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E : PolynomialDegreeDecoder) (degree : α → Option ℕ)
    (q : ℕ) (hq : 0 < q) (C : Channel E degree q hq) (B s : ℕ) (hs : 0 < s) :
    acceptance P E degree q hq C B s =
      P.eventMass (fun a => publicTest B s (degree a) = true) :=
  PublicFullAttack.acceptance_eq P E degree C.firstChannel B s hs

/-- Arbitrary full-transcript channels preserve the exact signed first-hint
gap. The two games can use different coins, spaces, and later challenges. -/
theorem signed_gap_eq {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (Q : FiniteLaw β) (E : PolynomialDegreeDecoder)
    (degreeP : α → Option ℕ) (degreeQ : β → Option ℕ)
    (q : ℕ) (hq : 0 < q) (CP : Channel E degreeP q hq) (CQ : Channel E degreeQ q hq)
    (B s : ℕ) (hs : 0 < s) :
    acceptance P E degreeP q hq CP B s - acceptance Q E degreeQ q hq CQ B s =
      P.eventMass (fun a => publicTest B s (degreeP a) = true) -
        Q.eventMass (fun a => publicTest B s (degreeQ a) = true) := by
  rw [acceptance_eq _ _ _ _ _ _ _ _ hs, acceptance_eq _ _ _ _ _ _ _ _ hs]

/-- The charged work is exactly the first representation's decoder/test work,
independently of q and of every later transcript slot. -/
theorem run_work_eq (E : PolynomialDegreeDecoder) (B s q : ℕ) (hq : 0 < q)
    (transcript : Fin q → Option (List Bool)) :
    (run E B s q hq transcript).work =
      (PublicFullAttack.run E B s (transcript ⟨0, hq⟩)).work := rfl

theorem run_work_polynomial (E : PolynomialDegreeDecoder) (B s q : ℕ) (hq : 0 < q)
    (transcript : Fin q → Option (List Bool)) :
    (run E B s q hq transcript).work ≤
      (E.coefficient + 8192 * (E.coefficient + 1) ^ 2 + 2) *
      (B.size + s.size + ((transcript ⟨0, hq⟩).map List.length).getD 0 + 1) ^
        (2 * (E.exponent + 1)) :=
  PublicFullAttack.run_work_polynomial E B s (transcript ⟨0, hq⟩)

end IsogenyAttack.TranscriptEncoding
