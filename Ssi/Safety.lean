/-!
# Safety state (§5): VS as an explicit, fail-closed conjunction of invariants

Each invariant evaluates to true, false, or unknown. VS holds only when at
least one invariant is declared (Axiom S1) and every invariant is true.
False or unknown makes VS false (Axiom S2: Unknown MUST NOT be interpreted as safe).
-/
namespace Ssi

inductive Truth3 where
  | tt
  | ff
  | unknown
  deriving DecidableEq, Repr

/-- Every evaluated invariant is true. -/
def allTrue : List Truth3 → Bool
  | [] => true
  | .tt :: xs => allTrue xs
  | .ff :: _ => false
  | .unknown :: _ => false

/-- VS(X): at least one declared invariant (S1), and all of them true (S2). -/
def vs (rs : List Truth3) : Bool := !rs.isEmpty && allTrue rs

theorem allTrue_false_of_unknown : ∀ rs : List Truth3, Truth3.unknown ∈ rs → allTrue rs = false
  | [], h => by cases h
  | .tt :: xs, h => by
    cases h with
    | tail _ h' => exact allTrue_false_of_unknown xs h'
  | .ff :: _, _ => rfl
  | .unknown :: _, _ => rfl

theorem allTrue_false_of_ff : ∀ rs : List Truth3, Truth3.ff ∈ rs → allTrue rs = false
  | [], h => by cases h
  | .tt :: xs, h => by
    cases h with
    | tail _ h' => exact allTrue_false_of_ff xs h'
  | .ff :: _, _ => rfl
  | .unknown :: _, _ => rfl

/-- Axiom S2: an invariant that cannot be evaluated makes VS false. -/
theorem unknown_not_safe (rs : List Truth3) (h : Truth3.unknown ∈ rs) : vs rs = false := by
  unfold vs
  rw [allTrue_false_of_unknown rs h]
  cases rs.isEmpty <;> rfl

/-- Axiom S2: a false invariant makes VS false. -/
theorem false_not_safe (rs : List Truth3) (h : Truth3.ff ∈ rs) : vs rs = false := by
  unfold vs
  rw [allTrue_false_of_ff rs h]
  cases rs.isEmpty <;> rfl

/-- Axiom S1: with no declared invariant, safety is not established. -/
theorem undeclared_not_safe : vs [] = false := rfl

end Ssi
