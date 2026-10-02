/-!
# Safety Asset Class (§27, §28, §30, §35)
-/
namespace Ssi

/-- Evidence for a Safety Asset SA = (X, C, P, Σ). -/
structure Evidence where
  certificateValid : Bool    -- VALID(C)
  provenanceValid  : Bool    -- VALID(P)
  bound            : Bool    -- BOUND(C, X)
  authentic        : Bool    -- AUTHENTIC(Σ)
  revoked          : Bool    -- REVOKED(SA)
  deriving DecidableEq, Repr

def evidenceOk (e : Evidence) : Bool :=
  e.certificateValid && e.provenanceValid && e.bound && e.authentic

/-- Definition 27: SAC(X, C) = 1. -/
def sac (ssiX : Bool) (e : Evidence) : Bool := ssiX && evidenceOk e

/-- SAC ⊆ SSI. -/
theorem sac_subset_ssi (ssiX : Bool) (e : Evidence) (h : sac ssiX e = true) : ssiX = true := by
  cases hs : ssiX with
  | false => rw [hs] at h; cases h
  | true => rfl

/-- Axiom P1: no SAC certification without valid provenance. -/
theorem no_provenance_no_sac (ssiX : Bool) (e : Evidence) (h : e.provenanceValid = false) :
    sac ssiX e = false := by
  simp [sac, evidenceOk, h]

/-- Axiom V1: a certificate not bound to this state is not evidence for it. -/
theorem unbound_certificate_no_sac (ssiX : Bool) (e : Evidence) (h : e.bound = false) :
    sac ssiX e = false := by
  simp [sac, evidenceOk, h]

/-- §28: a revoked asset is not currently certified. -/
def currentlyCertified (ssiX : Bool) (e : Evidence) : Bool := sac ssiX e && !e.revoked

theorem revoked_not_certified (ssiX : Bool) (e : Evidence) (h : e.revoked = true) :
    currentlyCertified ssiX e = false := by
  simp [currentlyCertified, h]

/-! ## Conformance levels (§35) and completion (§40) -/

inductive Level where
  | defined
  | executable
  | reproducible
  | mechanicallyVerified
  | operationallyCertified
  deriving DecidableEq, Repr

def Level.rank : Level → Nat
  | .defined => 0
  | .executable => 1
  | .reproducible => 2
  | .mechanicallyVerified => 3
  | .operationallyCertified => 4

/-- §40: the system is mathematically complete only when every proof obligation is discharged. -/
def complete (discharged : List Bool) : Bool := !discharged.isEmpty && discharged.all id

theorem open_obligation_incomplete (ds : List Bool) : complete (ds ++ [false]) = false := by
  simp [complete]

end Ssi
