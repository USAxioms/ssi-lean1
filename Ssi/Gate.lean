/-!
# Execution gate (§7–§9, §13, §31)

PERMIT(X,a) = AUTH ∧ SAFE_ACTION ∧ VER ∧ CAP, and execution follows
EXECUTE → VERIFY → TRANSITION → INVARIANT CHECK → COMMIT.
Nothing commits unless every check passes, including the invariant on the
next state.
-/
namespace Ssi

inductive Outcome (σ : Type) where
  | reject
  | commit (next : σ)
  deriving DecidableEq, Repr

/-- PERMIT(X, a). -/
def permit (auth safe ver cap : Bool) : Bool := auth && safe && ver && cap

/-- EXECUTE(X, A): commit the transition only if permitted and the next state is invariant-valid. -/
def execute {σ : Type} (auth safe ver cap : Bool) (next : σ) (invNext : Bool) : Outcome σ :=
  match permit auth safe ver cap && invNext with
  | true => .commit next
  | false => .reject

/-- Theorem 1 (Authorization Safety): ¬AUTH ⇒ ¬EXECUTE. -/
theorem no_auth_no_execute {σ : Type} (s v c : Bool) (n : σ) (i : Bool) :
    execute false s v c n i = .reject := rfl

/-- Theorem 2 (Verification Safety Gate): ¬VER ⇒ ¬EXECUTE. -/
theorem no_ver_no_execute {σ : Type} (a s c : Bool) (n : σ) (i : Bool) :
    execute a s false c n i = .reject := by
  cases a <;> cases s <;> rfl

/-- An unsafe action is never executed. -/
theorem unsafe_no_execute {σ : Type} (a v c : Bool) (n : σ) (i : Bool) :
    execute a false v c n i = .reject := by
  cases a <;> rfl

/-- An action outside the capability boundary is never executed. -/
theorem no_cap_no_execute {σ : Type} (a s v : Bool) (n : σ) (i : Bool) :
    execute a s v false n i = .reject := by
  cases a <;> cases s <;> cases v <;> rfl

/-- The invariant check precedes commit: an invalid next state is never committed. -/
theorem invalid_next_no_commit {σ : Type} (a s v c : Bool) (n : σ) :
    execute a s v c n false = .reject := by
  cases a <;> cases s <;> cases v <;> cases c <;> rfl

/-- Axiom A2 (Fail-Closed Execution), in full: a commit implies every gate passed. -/
theorem commit_implies_all {σ : Type} (a s v c i : Bool) (n x : σ)
    (h : execute a s v c n i = .commit x) :
    a = true ∧ s = true ∧ v = true ∧ c = true ∧ i = true ∧ x = n := by
  cases a <;> cases s <;> cases v <;> cases c <;> cases i <;> cases h <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Cognitive State Ledger authorization (§13, Axiom C1) -/

structure Csl where
  signatureValid : Bool
  revoked        : Bool
  validUntil     : Nat      -- end of the validity interval
  deriving DecidableEq, Repr

/-- AUTH under the active CSL: valid signature, not revoked, unexpired, and within the envelope. -/
def cslAuth (csl : Csl) (now : Nat) (inEnvelope : Bool) : Bool :=
  csl.signatureValid && !csl.revoked && decide (now ≤ csl.validUntil) && inEnvelope

/-- Axiom C1: an expired CSL authorizes nothing. -/
theorem expired_csl_no_auth (csl : Csl) (now : Nat) (e : Bool) (h : csl.validUntil < now) :
    cslAuth csl now e = false := by
  unfold cslAuth
  rw [decide_eq_false (Nat.not_le.mpr h)]
  simp

/-- Axiom C1: a revoked CSL authorizes nothing. -/
theorem revoked_csl_no_auth (csl : Csl) (now : Nat) (e : Bool) (h : csl.revoked = true) :
    cslAuth csl now e = false := by
  simp [cslAuth, h]

/-- Axiom C1: exceeding the envelope removes authorization. -/
theorem outside_envelope_no_auth (csl : Csl) (now : Nat) : cslAuth csl now false = false := by
  simp [cslAuth]

/-- Axiom C1 end to end: under an expired CSL, nothing executes. -/
theorem expired_csl_no_execute {σ : Type} (csl : Csl) (now : Nat) (e s v c : Bool) (n : σ) (i : Bool)
    (h : csl.validUntil < now) : execute (cslAuth csl now e) s v c n i = .reject := by
  rw [expired_csl_no_auth csl now e h] <;> rfl

end Ssi
