-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsOn
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrSync
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.OFull
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Free

@[expose] public section

/-! # The correction warps' O-full and staging-free poll events

At its O-full wait of stage `st` of item `i` a correction thread polls stage `st`'s O-full object
of its CTA with parity `i % 2`; at its free wait of stage `st` (and at the tail, of stage 1) it
polls the stage's free barrier with parity `(i + 1) % 2` (`corr_wait_ev`, for every template its
site fires, undefined behaviour excluded). The registers the run invariant names hold their
values at a state (`corr_reg`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

set_option maxHeartbeats 8000000 in
theorem corr_wait_live :
    (3250 ∈ Flow.live (Correction.Site.oWait 0).pc ∧
      3937 ∈ Flow.live (Correction.Site.oWait 0).pc) ∧
    (3252 ∈ Flow.live (Correction.Site.oWait 1).pc ∧
      3937 ∈ Flow.live (Correction.Site.oWait 1).pc) ∧
    (3251 ∈ Flow.live (Correction.Site.fWait 0).pc ∧
      3939 ∈ Flow.live (Correction.Site.fWait 0).pc) ∧
    (3900 ∈ Flow.live (Correction.Site.fWait 1).pc ∧
      3939 ∈ Flow.live (Correction.Site.fWait 1).pc) ∧
    (3900 ∈ Flow.live (Correction.Site.tailWait).pc ∧
      3939 ∈ Flow.live (Correction.Site.tailWait).pc) := by
  simp only [Correction.Site.pc]
  decide +kernel

set_option maxHeartbeats 8000000 in
theorem corr_wait_values (L : Launch) (g : Nat) (d : Correction.D) :
    Correction.valueOf L g d 3250 = b32 (Correction.sb L + 192) ∧
    Correction.valueOf L g d 3252 = b32 (Correction.sb L + 200) ∧
    Correction.valueOf L g d 3251 = b32 (Correction.sb L + 272) ∧
    Correction.valueOf L g d 3900 = b32 (Correction.sb L + 280) ∧
    Correction.valueOf L g d 3937 = b32 (d.i % 2) ∧
    Correction.valueOf L g d 3939 = b32 ((d.i + 1) % 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Correction.valueOf, Correction.values, Correction.chunkValues,
      Correction.loadValues, PTX.Flow.lookupLit, Option.getD_some]

theorem corr_reg {g : Nat} {d : Correction.D} {t : TState}
    (h4 : Holds t.regs (Correction.facts L g d)) {r : Nat} (hl : r ∈ Flow.live d.site.pc) :
    t.regs r = some (Correction.valueOf L g d r) :=
  holds_mem h4 (mem_factsFrom (List.mem_append_left _ hl))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
