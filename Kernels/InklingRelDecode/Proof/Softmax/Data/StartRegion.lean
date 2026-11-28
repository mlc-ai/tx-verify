-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Steps
import Kernels.InklingRelDecode.Proof.Lib.Havoc

@[expose] public section

/-! # The region of the entry's constants

No code of the softmax writes the entry's constants (registers 482, 484, 483 and 199): one
region check
(`start_region`) covers the positions between any two events, the segments of the software
exponent through the hook table (`hooks_any`). `siteC` checks a site's position and event. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The positions between the first event and the last of the softmax and the epilogue's poll. -/
def startIvs : List (Nat × Nat) := [(574, 1757), (2560, 6)]

theorem start_region : regionH kernel Lib.hooks startIvs [482, 484, 483, 199] = true := by
  decide +kernel

theorem hooks_any : HooksAny Assumptions.all L g Lib.hooks := by
  intro t a u ha hm
  have act : t.sub = 0 ∧ t.acc = [] := by
    have ha' := ha
    simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha'
    rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      try cases hm
    change (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
      (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) []).bind
        (Assumptions.execEmu · t) else none) = some (.ok u) at hm
    split at hm
    · rename_i active
      exact ⟨active.2.1, List.isEmpty_iff.mp active.2.2⟩
    · cases hm
  obtain ⟨h, h1, h2, -, -, -, h3⟩ := Lib.hooks_ok t a u act.1 act.2 ha hm
  exact ⟨h, h1, h2, h3⟩

/-- The checks of a site: its position and the next lie in the region, no segment starts there,
and its event writes neither constant. -/
def siteC (s : Site) : Bool :=
  inIvs startIvs s.pc && inIvs startIvs (s.pc + 1) && !Assumptions.emuSites.contains s.pc &&
  (match kernel.code[s.pc]? with
    | some ins => [482, 484, 483, 199].all fun r => !(eventWrites ins.op).contains r
    | none => true)

theorem siteC_ok (s : Site) (h : s ≠ .epilogue) : siteC s = true := by
  cases s with
  | pre j => revert j; decide +kernel
  | nxt j => revert j; decide +kernel
  | epilogue => exact absurd rfl h
  | _ => decide +kernel

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
