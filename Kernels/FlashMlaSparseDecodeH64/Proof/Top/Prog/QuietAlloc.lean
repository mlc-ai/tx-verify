-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietColl
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemResource
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.AllocSteps
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Tmem
import Lemmas.Tmem.Alloc512

@[expose] public section

/-! # Every recorded allocation is at column 0

The code's only allocation is the startup's of 512 columns (`tmem_res`), and a 512-column
allocation of a replayable history is at column 0 (`Consistent.alloc512_base`; the history replays
without a fault by `Safe.noTmemResource`). It is the hypothesis of the library's step of a lane at
the allocation (`alloc_quiet_steps`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

/-- **Every recorded Tensor Memory allocation is at column 0.** -/
theorem Prog.allocZero (hIn : Top.Inputs P L m) (hp : Pre P L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
    {cta : Nat} {r : Tmem.Pair.Requests} (hr : r ∈ X.tmemHistory cta) (n col : Nat)
    (hact : r.action = .alloc n col) : col = 0 := by
  have hv := ((hX.tmemPair.1 cta).1 r hr).2.2
  have hreq := ((hX.tmemPair.1 cta).1 r hr).2.1
  have hlt := (Tmem.Pair.WarpRequest.event_props hv 0).2.2
  have hl0 := hv.2.2.1 0
  have hreq' : r.own.request = .alloc n := by rw [← hreq, hact]; rfl
  rw [hreq'] at hl0
  have hn : n = 512 := by
    obtain ⟨-, h⟩ := tmem_res (tmem_rows hp hX hFw) hlt hl0 rfl
    rcases h with ⟨-, -, h | h⟩ | ⟨hA, -⟩
    · exact Tmem.Request.alloc.inj h
    · cases h
    · obtain ⟨-, h, -⟩ := wg0_deallocOps hp hX hFw hl0 hA rfl
      cases h
  subst hn
  exact hX.alloc512_base (tmemNoFault_of_safe (Safe.noTmemResource hp hIn hX hFw) cta)
    hr hact

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
