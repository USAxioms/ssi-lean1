# Safe Super Intelligence (SSI) Axiomatic System v1.0 — Lean 4 Formalization

Lean 4 formalization of the **Safe Super Intelligence Axiomatic System v1.0** by Michael Aaron Russell: a formal specification for human-guided, verifiably safe superintelligence.

$$SSI = SI \cap VS \cap HG \cap AUTH \cap VER$$

Pure Lean 4 core: no Mathlib, no external dependencies.

## Build

```bash
# install elan (Lean toolchain manager): https://github.com/leanprover/elan
lake build
```

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.12.0`). Every push runs `.github/workflows/lean.yml`, which builds the project and checks every proof and golden vector.

## Build status

This repository was written without access to a Lean compiler. **It has not yet been compiled.** The first CI run on GitHub is the first check; if a proof fails, the log names the file and line. In the specification's own terms (§35), this repository targets **Level 3 — Mechanically Verified** for the theorems below, but holds that level only once a CI run passes.

## Modules

| File | Specification sections |
|---|---|
| `Ssi/Wad.lean` | §3 WAD-18 normative arithmetic: integer-only, explicit failure (W1, W2) |
| `Ssi/Safety.lean` | §5 VS as a fail-closed conjunction of declared invariants (S1, S2) |
| `Ssi/Gate.lean` | §7–§9, §13, §31 PERMIT, the EXECUTE gate, and CSL authorization continuity (A1, A2, C1) |
| `Ssi/Membership.lean` | §17, §18, §29, §33, §36, §38 SSI membership, closure, and the A/B/C distinction |
| `Ssi/Refinement.lean` | §11, §12, §24–§26 (K, M, G), kernel immutability, adoption, non-regression, fixed points |
| `Ssi/Reachability.lean` | §21, §23 invariant preservation and reachable-state safety |
| `Ssi/Asset.lean` | §27, §28, §35, §40 Safety Asset Class, revocation, conformance levels, completion |
| `Ssi/GoldenVectors.lean` | 30 concrete cases checked by `decide` |

## Theorems and the specification

| Theorem | Specification statement |
|---|---|
| `unknown_not_safe`, `false_not_safe`, `undeclared_not_safe` | Axioms S1–S2: Unknown is not safe; safety needs declared invariants |
| `no_auth_no_execute` | Theorem 1, Axiom A1 / PO-3: ¬AUTH ⇒ ¬EXECUTE |
| `no_ver_no_execute` | Theorem 2 / PO-4: ¬VER ⇒ ¬EXECUTE |
| `unsafe_no_execute`, `no_cap_no_execute`, `invalid_next_no_commit` | §8, §31: every gate, and the invariant check before commit |
| `commit_implies_all` | Axiom A2: a commit implies every gate passed |
| `expired_csl_no_auth`, `revoked_csl_no_auth`, `outside_envelope_no_auth`, `expired_csl_no_execute` | Axiom C1: authorization continuity |
| `classification` | Theorem 8: SSI classification |
| `not_si_not_ssi`, `not_safe_not_ssi`, `not_hg_not_ssi`, `not_auth_not_ssi`, `not_ver_not_ssi` | §38: SI ⇏ SSI, VS ⇏ SSI; every component required |
| `closure` | Theorem 4: closure requires re-established predicates |
| `encoding_deterministic` | §29: canonical encoding is deterministic |
| `kernel_immutable` | Axiom K1 / PO-7: R³(K, M, G) = (K, M′, G′) by construction |
| `adopted_preserves_safety`, `regression_blocks_adoption` | Theorem 6 / PO-8 core: non-regression |
| `safe_fixed_point`, `iterate_fixed` | Theorem 7: safe fixed point; existence not assumed |
| `preservation` | Theorem 3 / PO-5 |
| `reachable_safe` | Theorem 5: reachable-state safety, by induction |
| `sac_subset_ssi` | §27: SAC ⊆ SSI |
| `no_provenance_no_sac`, `unbound_certificate_no_sac` | Axioms P1, V1 / PO-6 |
| `revoked_not_certified` | §28: revocation |
| `open_obligation_incomplete` | §40: not complete until every obligation is discharged |

## Scope

These proofs establish the *architecture*: that the gates, invariants, and certification rules behave as the specification states for any profile and any state type. They do not instantiate the superintelligence predicate SI, enumerate a concrete invariant set Φ, or establish that any deployed system belongs to the SSI class. Those are formalization items 1, 2, and 5–10 of §40, which remain open. Cryptographic binding (PO-6) is modelled as a Boolean `bound`; signature verification itself is outside this formalization.

## Naming

This specification and repository are independent work by Michael Aaron Russell and are not affiliated with any company of a similar name.

Choose and add a license before publishing.
