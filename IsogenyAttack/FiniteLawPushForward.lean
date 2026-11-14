import IsogenyAttack.LegendreDistribution

/-! Exact event and atom formulas for deterministic changes of finite sample space. -/
namespace IsogenyAttack.FiniteLaw
open scoped BigOperators

/-- An event under a deterministic pushforward is its inverse-image event. -/
theorem pushForward_event {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (f : α → β) (E : β → Prop) :
    (P.pushForward f).eventMass E = P.eventMass (fun a => E (f a)) := by
  classical
  calc
    (P.pushForward f).eventMass E =
        ∑ b ∈ Finset.univ.filter E, P.eventMass (fun a => f a = b) := by
      rw [eventMass_eq_sum, Finset.sum_filter]
      rfl
    _ = P.eventMass (fun a => f a ∈ Finset.univ.filter E) :=
      (P.target_set_mass f (Finset.univ.filter E)).symm
    _ = P.eventMass (fun a => E (f a)) := P.eventMass_congr (fun a => by simp)

/-- An injective relabeling preserves each atom's mass. -/
theorem pushForward_injective_mass {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (f : α → β) (hf : Function.Injective f) (a : α) :
    (P.pushForward f).mass (f a) = P.mass a := by
  classical
  change P.eventMass (fun x => f x = f a) = _
  rw [P.eventMass_congr (fun x => hf.eq_iff)]
  simp [eventMass_eq_sum]

/-- Atom masses after a bijective change of the entire sample space. -/
theorem pushForward_equiv_mass {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (e : α ≃ β) (b : β) :
    (P.pushForward e).mass b = P.mass (e.symm b) := by
  have h := P.pushForward_injective_mass e e.injective (e.symm b)
  simpa only [e.apply_symm_apply] using h

end IsogenyAttack.FiniteLaw
