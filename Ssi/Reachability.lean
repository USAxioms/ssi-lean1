/-!
# Invariant preservation and reachable-state safety (§21, §23, §32)
-/
namespace Ssi

/-- States reachable from an initial state through permitted transitions. -/
inductive Reach {σ α : Type} (init : σ → Prop) (permit : σ → α → Prop) (next : σ → α → σ → Prop) :
    σ → Prop where
  | base {x : σ} : init x → Reach init permit next x
  | step {x x' : σ} {a : α} : Reach init permit next x → permit x a → next x a x' →
      Reach init permit next x'

/-- Theorem 3 (Safety Preservation). -/
theorem preservation {σ α : Type} (inv : σ → Prop) (permit : σ → α → Prop) (next : σ → α → σ → Prop)
    (pres : ∀ x a x', inv x → permit x a → next x a x' → inv x')
    (x : σ) (a : α) (x' : σ) (hi : inv x) (hp : permit x a) (hn : next x a x') : inv x' :=
  pres x a x' hi hp hn

/-- Theorem 5 (Reachable-State Safety), by induction over transition depth. -/
theorem reachable_safe {σ α : Type} (init : σ → Prop) (permit : σ → α → Prop) (next : σ → α → σ → Prop)
    (inv : σ → Prop) (hinit : ∀ x, init x → inv x)
    (pres : ∀ x a x', inv x → permit x a → next x a x' → inv x') :
    ∀ x, Reach init permit next x → inv x := by
  intro x hr
  induction hr with
  | base h => exact hinit _ h
  | step _ hp hn ih => exact pres _ _ _ ih hp hn

end Ssi
