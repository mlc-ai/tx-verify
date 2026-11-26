-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ev
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Trace

@[expose] public section

/-! # The loads of warpgroup 2 by their pcs

An event of a lane at the pc of a raw load (`dqRawPc r s`, `ld.shared.b64`) is a read of eight
bytes, at the pc of a scale load (`dqScalePc r`, one of the four elements of a
`ld.shared.v4.b32`) a read of four bytes, unless it is an undefined-behaviour event; and the lane
is one of warps 8-11 (`dequant_loads`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Dequant Dequant.Data

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **A raw load by its pc**: an event of a lane at `dqRawPc r s` that is no undefined behaviour is
a read of eight bytes of a lane of warps 8-11. -/
theorem dequant_raw_load (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) {r s : Nat}
    (hr : r < 4) (hs : s < 8) (hpc : e.pc = dqRawPc r s) :
    MbarRow.DequantAt L g e.pc ∧ ∃ a bs, e.kind = .rd a bs ∧ a.size = 8 := by
  have hrange : 2606 ≤ e.pc ∧ e.pc < 3611 := by rw [hpc]; unfold dqRawPc; split_ifs <;> omega
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, ⟨hpcd, hk⟩, hw1, hw2⟩ := dequant_state hp hJ hi hev hpcσ hrange
  refine ⟨⟨hw1, hw2, hrange⟩, ?_⟩
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  have hq : Site.pc site = dqRawPc r s := hpcd.symm.trans hpc
  cases site with
  | raw r' s' =>
    rcases hk with ⟨a, bs, hk, -, hsz⟩ | ⟨f, hk⟩
    · exact ⟨a, bs, hk, hsz⟩
    · exact absurd hk (hub f)
  | scale r' => exact absurd hq (scale_ne_raw r' ⟨r, hr⟩ ⟨s, hs⟩)
  | store r' s' => exact absurd hq (store_ne_raw r' ⟨r, hr⟩ s' ⟨s, hs⟩)
  | _ =>
    exfalso
    simp only [Site.pc] at hq
    unfold dqRawPc at hq
    split_ifs at hq <;> omega

/-- **A scale load by its pc**: an event of a lane at `dqScalePc r` that is no undefined behaviour
is a read of four bytes of a lane of warps 8-11. -/
theorem dequant_scale_load (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) {r : Nat}
    (hr : r < 4) (hpc : e.pc = dqScalePc r) :
    MbarRow.DequantAt L g e.pc ∧ ∃ a bs, e.kind = .rd a bs ∧ a.size = 4 := by
  have hrange : 2606 ≤ e.pc ∧ e.pc < 3611 := by rw [hpc]; unfold dqScalePc; omega
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, ⟨hpcd, hk⟩, hw1, hw2⟩ := dequant_state hp hJ hi hev hpcσ hrange
  refine ⟨⟨hw1, hw2, hrange⟩, ?_⟩
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  have hq : Site.pc site = dqScalePc r := hpcd.symm.trans hpc
  cases site with
  | scale r' =>
    rcases hk with ⟨a, bs, hk, -, hsz⟩ | ⟨f, hk⟩
    · exact ⟨a, bs, hk, hsz⟩
    · exact absurd hk (hub f)
  | raw r' s' => exact absurd hq (raw_ne_scale r' ⟨r, hr⟩ s')
  | store r' s' => exact absurd hq (store_ne_scale r' ⟨r, hr⟩ s')
  | _ =>
    exfalso
    simp only [Site.pc] at hq
    unfold dqScalePc at hq
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
