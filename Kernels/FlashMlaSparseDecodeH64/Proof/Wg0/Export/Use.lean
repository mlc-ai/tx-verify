-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs

@[expose] public section

/-! # The use of a validity read

The per-use index of warpgroup 0's validity read at pc 289 (`vm`, the ring region `tokenValid`):
a read of block `r` is the lane's word of slot `s = r % 4` (as in `MemRow.Wg0Rd`), after the
block's successful poll of `coordReady s` at 264 and before its arrival on `coordFree s` at 571
(place 2 of the block), so the lane has made `u + 1` successful polls of `coordReady s` and
`u = r / 4` arrivals on `coordFree s` (`wg0_vmUse`), read off the reference invariant's counts
(`Wg0.acq_ready`, `Wg0.arr_free`) and the ledger's (`wg0_okPolls`, `wg0_arrivals`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The site at pc 289 is the validity read. -/
private theorem vm_of_pc {s : Wg0.Site} (h : s.pc = 289) : s = .vm := by
  cases s with
  | sld a k => revert a k h; decide
  | pst k | pld k => revert k h; decide
  | ost c | rld c | rldw c | rst c | rstw c | old c | oldw c | ofpx c | obar c | oel c
    | otma c => revert c h; decide
  | ost2 c k => revert c k h; decide
  | _ => revert h; decide

/-- **The use of a validity read**: a shared read of warpgroup 0 at pc 289 is the lane's word
of a slot `s`, with `u + 1` successful polls of `coordReady s` and `u` arrivals on `coordFree s`
before it. -/
theorem wg0_vmUse (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hat : MbarRow.Wg0At L g pc) (h289 : pc = 289) :
    ∃ s : Fin 4, MemRow.WsAcc L (g / L.block)
        (221696 + 8 * s.val + 4 * ((L.tidOf g).x / 32 / 2)) 4 a ∧
      ∃ u, okPolls (mbarLoc L (g / L.block) (.coordReady s)) ((X.tr g).take k) = u + 1 ∧
        arrivals (mbarLoc L (g / L.block) (.coordFree s)) ((X.tr g).take k) = u := by
  obtain ⟨hw4, hr⟩ := hat
  have ht : tidOf L g < 128 := MemRow.wg0_tid hw4
  have hm : MemRow.MemEvent ⟨pc, .rd a bs⟩ := .inl ⟨a, bs, rfl⟩
  obtain ⟨d, hR, ⟨hpc, hE⟩, -⟩ := wg0_at hp hX hFw he (Wg0.memEvent_noUb hm) hr
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at hpc
  subst h289
  obtain rfl := vm_of_pc hpc.symm
  simp only [Wg0.RefCore, Wg0.RefAt, Wg0.Site.reg, Wg0.Site.idx, Wg0.Control.D.words] at hc
  obtain ⟨r, ⟨-, -, -, -, -, hv, -⟩, hq, ha⟩ := hc
  dsimp only at hq ha
  have hr4 : r % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨a', bs', hk, hws⟩ := Wg0.rdAt_ws hm hE (Wg0.vm_loc hp ht (d := ⟨.vm, el, a0, l0, l1,
    cnt, bi, vs, pv, sl, ps, vt⟩) hv hr4)
  cases hk
  refine ⟨⟨r % 4, hr4⟩, by simpa [tidOf] using hws, r / 4, ?_, ?_⟩
  · show okPolls (MbarRow.loc L g (.coordReady ⟨r % 4, hr4⟩)) _ = _
    rw [wg0_okPolls hp hX hFw hw4, hq, Wg0.acq_ready hp]
    simp [Wg0.use, Wg0.ind, ringUses_here rfl hr4]
  · show arrivals (MbarRow.loc L g (.coordFree ⟨r % 4, hr4⟩)) _ = _
    rw [wg0_arrivals hp hX hFw hw4, ha, Wg0.arr_free hp]
    simp [Wg0.use, Wg0.ind, ringUses_here rfl hr4]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
