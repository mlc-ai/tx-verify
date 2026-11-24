-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.TailDecode
import Core.Thread.Run

/-! Execute the tail-clearing control flow with TxVerify's thread semantics. Only local
steps and two-byte zero stores to the owning block may reach the end successfully. -/
namespace FlashKda.Tail
open PTX
noncomputable section

def launch : Launch where
  grid := 2
  block := 256
  params := fun _ => none
  sharedBase := 1024

/-- Registers at entry to the first tile's tail loop. The packed batch starts at token zero.
The first sequence has exactly the given live length. -/
def entryState (mode : Bool) (live col : Nat) : TState :=
  let registers := if mode then [(1301,live),(210,128+col),(251,0),(252,live),(208,0)]
    else [(1267,live),(206,128+col)]
  { pc := start mode, regs := fun r =>
    (registers.lookup r).map fun n => .bits 32 (BitVec.ofNat 64 n) }

private def cache (mode : Bool) : Kernel :=
  { name := "", params := [],
    code := List.replicate (start mode) ⟨none,.ret⟩ ++ body mode }

def clearWrites (mode : Bool) (k : Kernel) (g : Nat) : Nat → TState → Option (List Nat)
  | 0, _ => none
  | n+1, t => do
    if t.pc = finish mode then return []
    guard (start mode ≤ t.pc ∧ t.pc < finish mode)
    match out k [] launch g t with
    | .tau next => clearWrites mode k g n next
    | .ev (.write acc bs next) =>
      guard (acc.loc.space = .shared ∧ acc.loc.cta = g/256 ∧ acc.size = 2 ∧
        bs.map byteBits = [some 0,some 0])
      return acc.loc.addr :: (← clearWrites mode k g n next)
    | _ => none

def expected (live col : Nat) :=
  (List.range (16 - live)).map fun r => launch.sharedBase + 4096 + (live+r)*256 + 2*col

def traceMatches (mode : Bool) (live col : Nat) : Bool :=
  clearWrites mode (cache mode) (128+col) 82 (entryState mode live col) = some (expected live col)

/-- Transfer successful trace checks to any kernel with the same decoded code in the
interval. The evaluator rejects any attempt to leave the region except at its end. -/
theorem same_trace (mode : Bool) (k : Kernel)
    (same : ∀ pc, start mode ≤ pc → pc < finish mode → k.code[pc]? = (cache mode).code[pc]?)
    (g fuel : Nat) (t : TState) :
    clearWrites mode k g fuel t = clearWrites mode (cache mode) g fuel t := by
  induction fuel generalizing t with
  | zero => rfl
  | succ n ih =>
    by_cases stop : t.pc = finish mode
    · simp [clearWrites, stop]
    by_cases inside : start mode ≤ t.pc ∧ t.pc < finish mode
    · have hout : out k [] launch g t = out (cache mode) [] launch g t := by
        simp only [out, same t.pc inside.1 inside.2]
      simp only [clearWrites, stop, ↓reduceIte, hout]
      simp_rw [ih]
    · simp [clearWrites, stop, inside]

end
end FlashKda.Tail
