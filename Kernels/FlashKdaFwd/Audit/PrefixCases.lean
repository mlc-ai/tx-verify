-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.PrefixRun
import Kernels.FlashKdaFwd.Proof.PrefixWords

/-! Check the returned per-lane traces for the packed prefix launch. -/
namespace FlashKda.Prefix
open PTX
noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- All 31 nonzero threads return at instruction 172 without issuing a memory event.
The argument values, buffer addresses and input contents are arbitrary. -/
theorem idle_lanes (n input output : Nat) (offsets : List Nat) (g : Fin 31) :
    Exact [readonly] (launch n input output) (g.val+1) input offsets {} [⟨172, .exit⟩] := by
  have h : (replay [readonly] (launch n input output) (g.val+1) input offsets 12 {}).map
      Subtype.val = some [⟨172, .exit⟩] := by
    have hg := g.isLt
    generalize g.val = lane at *
    interval_cases lane <;> rfl
  cases found : replay [readonly] (launch n input output) (g.val+1) input offsets 12 {} with
  | none => simp [found] at h
  | some pair =>
    simp only [found, Option.map_some, Option.some.injEq] at h
    exact h ▸ pair.property

/-- The cumulative input lengths and mathematical cumulative tile counts include initial zero. -/
def offsetsOf (lengths : List Nat) := lengths.scanl (· + ·) 0
def expectedOf (lengths : List Nat) := offsetsOf (lengths.map Batches.tiles)

def checkBatch (lengths : List Nat) : Option Bool :=
  let audit := replay [readonly] (launch lengths.length 2048 4096) 0 2048
    (offsetsOf lengths) (60+20*lengths.length) {}
  audit.map fun r => storesMatch 4096 (expectedOf lengths) r.val

/-- A repeated pattern includes empty, short, full and partially filled tiles. -/
def lengthsFor (n : Nat) : List Nat :=
  (List.range n).map fun i => [0, 1, 15, 16, 17, 31, 32, 33][i%8]!

/-- All eight possible tail sizes, a full eight-sequence loop, and a second loop iteration. -/
theorem control_paths : ∀ n ∈ [0,1,2,3,4,5,6,7,8,23], checkBatch (lengthsFor n) = some true := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h|h|h|h|h|h|h|h|h|h <;> subst n <;> rfl

theorem batch_stores {n : Nat} (hn : n ∈ [0,1,2,3,4,5,6,7,8,23]) :
    let lengths := lengthsFor n
    let L := launch lengths.length 2048 4096
    (∃ es, Exact [readonly] L 0 2048 (offsetsOf lengths) {} es ∧
      storesMatch 4096 (expectedOf lengths) es = true) ∧
    (∀ xs, Run Decoded.kernel [readonly] L 0 {} xs none →
      (∀ e ∈ xs, respects 2048 (offsetsOf lengths) e) →
      storesMatch 4096 (expectedOf lengths) xs = true) :=
  verified_stores (control_paths n hn)

end
end FlashKda.Prefix
