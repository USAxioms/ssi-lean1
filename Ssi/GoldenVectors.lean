import Ssi.Wad
import Ssi.Safety
import Ssi.Gate
import Ssi.Membership
import Ssi.Refinement
import Ssi.Asset

/-!
# Golden vectors

Concrete cases checked by the Lean kernel with `decide`.
-/
namespace Ssi

-- §5 safety: fail closed on false or unknown; no declared invariants is not safety
example : vs [.tt, .tt, .tt] = true := by decide
example : vs [.tt, .ff, .tt] = false := by decide
example : vs [.tt, .unknown] = false := by decide
example : vs [] = false := by decide

-- §8, §31 execution gate: only a fully permitted, invariant-valid transition commits
example : execute true true true true (7 : Nat) true = .commit 7 := by decide
example : execute false true true true (7 : Nat) true = .reject := by decide
example : execute true false true true (7 : Nat) true = .reject := by decide
example : execute true true false true (7 : Nat) true = .reject := by decide
example : execute true true true false (7 : Nat) true = .reject := by decide
example : execute true true true true (7 : Nat) false = .reject := by decide
example : permit true true true true = true := by decide

-- §13 CSL: valid until t = 100
example : cslAuth ⟨true, false, 100⟩ 50 true = true := by decide
example : cslAuth ⟨true, false, 100⟩ 101 true = false := by decide   -- expired
example : cslAuth ⟨true, true, 100⟩ 50 true = false := by decide    -- revoked
example : cslAuth ⟨false, false, 100⟩ 50 true = false := by decide  -- bad signature
example : cslAuth ⟨true, false, 100⟩ 50 false = false := by decide  -- outside envelope

-- §27–§28 Safety Asset Class
example : sac true ⟨true, true, true, true, false⟩ = true := by decide
example : sac false ⟨true, true, true, true, false⟩ = false := by decide     -- not SSI
example : sac true ⟨true, false, true, true, false⟩ = false := by decide     -- no provenance
example : sac true ⟨true, true, false, true, false⟩ = false := by decide     -- certificate not bound
example : currentlyCertified true ⟨true, true, true, true, true⟩ = false := by decide  -- revoked

-- §35 conformance levels and §40 completion
example : Level.rank .defined < Level.rank .mechanicallyVerified := by decide
example : complete [true, true, true] = true := by decide
example : complete [true, false, true] = false := by decide
example : complete [] = false := by decide

-- §24 R³ keeps the kernel: refine the model and configuration of (K, M, G) = ("kernel", 1, 2)
example : (Refiner.apply (⟨(· + 1), (· * 10)⟩ : Refiner Nat Nat) (⟨"kernel", 1, 2⟩ : System String Nat Nat)).k = "kernel" := by decide
example : (Refiner.apply (⟨(· + 1), (· * 10)⟩ : Refiner Nat Nat) (⟨"kernel", 1, 2⟩ : System String Nat Nat)).m = 2 := by decide

-- §26 fixed point by iteration
example : iterate (fun (n : Nat) => n / 2) 10 1000 = 0 := by decide

-- WAD-18 normative arithmetic (§3)
example : add ⟨"risk", 1000100000000000000000⟩ ⟨"risk", 200000000000000000⟩
    = .ok ⟨"risk", 1000300000000000000000⟩ := by decide
example : divRaw 1000000000000000000 0 = .err .divByZero := by decide

end Ssi
