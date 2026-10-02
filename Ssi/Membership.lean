/-!
# SSI membership (§18, §33, §36, §38)

SSI(X) ⟺ SI(X) ∧ VS(X) ∧ HG(X) ∧ AUTH_STATE(X) ∧ VER_STATE(X), and the class
predicate of §33 adds PROV. Each component is an independent predicate of a
declared profile; none is inferred from another.
-/
namespace Ssi

/-- A deployment profile: each SSI predicate is declared explicitly (§17). -/
structure Profile (σ : Type) where
  si        : σ → Bool
  vs        : σ → Bool
  hg        : σ → Bool
  authState : σ → Bool
  verState  : σ → Bool
  prov      : σ → Bool

/-- Definition 21. -/
def Profile.ssi {σ : Type} (p : Profile σ) (x : σ) : Bool :=
  p.si x && p.vs x && p.hg x && p.authState x && p.verState x

/-- §33: the class predicate including provenance. -/
def Profile.ssiProv {σ : Type} (p : Profile σ) (x : σ) : Bool :=
  p.ssi x && p.prov x

/-- Theorem 8 (Safe Super Intelligence Classification). -/
theorem classification {σ : Type} (p : Profile σ) (x : σ)
    (h1 : p.si x = true) (h2 : p.vs x = true) (h3 : p.hg x = true)
    (h4 : p.authState x = true) (h5 : p.verState x = true) (h6 : p.prov x = true) :
    p.ssiProv x = true := by
  simp [Profile.ssiProv, Profile.ssi, h1, h2, h3, h4, h5, h6]

/-- §38: intelligence alone is not SSI — without verified safety there is no membership. -/
theorem not_safe_not_ssi {σ : Type} (p : Profile σ) (x : σ) (h : p.vs x = false) :
    p.ssi x = false := by
  simp [Profile.ssi, h]

/-- §38: safety alone is not SSI — without the capability criterion there is no membership. -/
theorem not_si_not_ssi {σ : Type} (p : Profile σ) (x : σ) (h : p.si x = false) :
    p.ssi x = false := by
  simp [Profile.ssi, h]

/-- Human guidance is required. -/
theorem not_hg_not_ssi {σ : Type} (p : Profile σ) (x : σ) (h : p.hg x = false) :
    p.ssi x = false := by
  simp [Profile.ssi, h]

/-- A valid authorization state is required. -/
theorem not_auth_not_ssi {σ : Type} (p : Profile σ) (x : σ) (h : p.authState x = false) :
    p.ssi x = false := by
  simp [Profile.ssi, h]

/-- Verification evidence is required. -/
theorem not_ver_not_ssi {σ : Type} (p : Profile σ) (x : σ) (h : p.verState x = false) :
    p.ssi x = false := by
  simp [Profile.ssi, h]

/-- Theorem 4 (SSI Closure Under Admissible Transition): the successor is SSI
when each predicate is re-established for it. Closure is not assumed. -/
theorem closure {σ : Type} (p : Profile σ) (x' : σ)
    (h1 : p.si x' = true) (h2 : p.vs x' = true) (h3 : p.hg x' = true)
    (h4 : p.authState x' = true) (h5 : p.verState x' = true) :
    p.ssi x' = true := by
  simp [Profile.ssi, h1, h2, h3, h4, h5]

/-- §29: canonical encoding is deterministic — equal states have equal encodings. -/
theorem encoding_deterministic {σ : Type} (enc : σ → String) (x₁ x₂ : σ) (h : x₁ = x₂) :
    enc x₁ = enc x₂ := by
  rw [h]

end Ssi
