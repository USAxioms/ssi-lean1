/-!
# R³ refinement (§11, §12, §24–§26)

The system is (K, M, G). R³ is given access only to M and G, so the kernel is
unchanged by construction (Axiom K1). A refinement is adopted only if
KernelEqual ∧ ProofValid ∧ AuthorizationValid ∧ NonRegression.
-/
namespace Ssi

/-- System = (K, M, G). -/
structure System (K M G : Type) where
  k : K
  m : M
  g : G

/-- An R³ refiner may change the model state and the governed configuration only. -/
structure Refiner (M G : Type) where
  refineM : M → M
  refineG : G → G

def Refiner.apply {K M G : Type} (r : Refiner M G) (s : System K M G) : System K M G :=
  { k := s.k, m := r.refineM s.m, g := r.refineG s.g }

/-- Axiom K1 / PO-7: R³(K, M, G) = (K, M', G'). -/
theorem kernel_immutable {K M G : Type} (r : Refiner M G) (s : System K M G) :
    (r.apply s).k = s.k := rfl

/-- All protected invariants hold. -/
def holdsAll {σ : Type} (Φ : List (σ → Bool)) (x : σ) : Prop := ∀ φ ∈ Φ, φ x = true

/-- Definition 24: every invariant satisfied before refinement remains satisfied after. -/
def nonRegression {σ : Type} (Φ : List (σ → Bool)) (x y : σ) : Prop :=
  ∀ φ ∈ Φ, φ x = true → φ y = true

/-- Definition 23: ADOPT = KernelEqual ∧ ProofValid ∧ AuthorizationValid ∧ NonRegression.
KernelEqual holds for every `Refiner` by `kernel_immutable`; the proof and authorization
conditions are supplied by the deployment as propositions. -/
structure Adopt {σ : Type} (Φ : List (σ → Bool)) (x y : σ) (proofValid authorizationValid : Prop) : Prop where
  proofHolds         : proofValid
  authorizationHolds : authorizationValid
  noRegression       : nonRegression Φ x y

/-- Theorem 6 core: an adopted refinement of a safe state keeps every protected invariant. -/
theorem adopted_preserves_safety {σ : Type} (Φ : List (σ → Bool)) (x y : σ) (P A : Prop)
    (hx : holdsAll Φ x) (ha : Adopt Φ x y P A) : holdsAll Φ y :=
  fun φ hφ => ha.noRegression φ hφ (hx φ hφ)

/-- Without non-regression evidence there is no adoption: a refinement that breaks a
protected invariant cannot be adopted. -/
theorem regression_blocks_adoption {σ : Type} (Φ : List (σ → Bool)) (x y : σ) (P A : Prop)
    (φ : σ → Bool) (hφ : φ ∈ Φ) (hx : φ x = true) (hy : φ y = false) : ¬ Adopt Φ x y P A := by
  intro ha
  have := ha.noRegression φ hφ hx
  rw [hy] at this
  cases this

/-- Definition 25: R³ fixed point. -/
def isFixed {σ : Type} (r : σ → σ) (x : σ) : Prop := r x = x

/-- Theorem 7 (Safe Fixed Point): the conjunction of an established fixed point
and established membership. Existence is not assumed. -/
theorem safe_fixed_point {σ : Type} (r : σ → σ) (ssi : σ → Bool) (x : σ)
    (hf : isFixed r x) (hs : ssi x = true) : r x = x ∧ ssi x = true :=
  ⟨hf, hs⟩

/-- A fixed point stays fixed under repeated refinement. -/
def iterate {σ : Type} (f : σ → σ) : Nat → σ → σ
  | 0, x => x
  | n + 1, x => iterate f n (f x)

theorem iterate_fixed {σ : Type} (f : σ → σ) (x : σ) (h : f x = x) : ∀ n, iterate f n x = x := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate, h, ih]

end Ssi
