-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # Warpgroup 2's named barrier

`dequant_bar`: a named-barrier event of a lane of warps 8–11 at a pc of warpgroup 2's code is
`everyone_sync` at pc 3610: barrier 12 of the whole CTA, `bar.sync`, without a thread count (the
code's count register holds 384 = `L.block`, recorded as `none`: `BarRow.recCnt`).
`barRow_dequant`: the row `BarRow.Dequant`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A barrier event at a warpgroup-2 pc is `bar.sync 12` of the CTA at pc 3610.** -/
theorem dequant_bar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.DequantAt L g e.pc) (hb : Execution.isBar e = true) :
    e.pc = 3610 ∧ e.kind = .bar 12 none .sync := by
  obtain ⟨-, -, hlo, hhi⟩ := hat
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | bar id cnt md =>
    obtain ⟨d, -, ⟨hpc, hk⟩, -⟩ := dequant_at hp hX hFw he (fun _ h => by cases h) ⟨hlo, hhi⟩
    obtain ⟨site, el, ac, l0, l1, cnt', sb, pb⟩ := d
    cases site <;>
      simp [Dequant.EvK, Dequant.PollEv, Dequant.LoadEv, Dequant.StoreEv] at hk
    case bar => exact ⟨hpc, by rw [hk.1, hk.2.1, hk.2.2]⟩
  | _ => simp [Execution.isBar] at hb

/-- **Row `BarRow.Dequant`**: a barrier event of a lane of warpgroup 2 is `everyone_sync` at
3610. -/
theorem barRow_dequant (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : BarRow.Dequant P L X := fun _ he hat hb =>
  dequant_bar hp hX hFw he hat hb

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
