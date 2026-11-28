-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Use
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Closed
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FinLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs

@[expose] public section

/-! # The block of a validity read

The validity read of warpgroup 0 at pc 289 reads the word of the slot `s` of its block `r`, the
number of blocks the lane has closed before it (`w0Closed`), at use `u = r / 4`: `r = 4 u + s`
(`wg0_vmBlk`; `wg0_vmUse` without the block). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The site at pc 289 is the validity read. -/
private theorem vm_of_pc' {s : Wg0.Site} (h : s.pc = 289) : s = .vm := by
  cases s with
  | sld a k => revert a k h; decide
  | pst k | pld k => revert k h; decide
  | ost c | rld c | rldw c | rst c | rstw c | old c | oldw c | ofpx c | obar c | oel c
    | otma c => revert c h; decide
  | ost2 c k => revert c k h; decide
  | _ => revert h; decide

/-- **The block of a validity read**: slot `s`, use `u`, and `4 u + s` blocks closed before it. -/
theorem wg0_vmBlk_pre (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} (hal : LaneUbFree X g k) {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨289, .rd a bs⟩) (hat : MbarRow.Wg0At L g 289) :
    ∃ s : Fin 4, ∃ u, MemRow.WsAcc L (g / L.block)
        (221696 + 8 * s.val + 4 * ((L.tidOf g).x / 32 / 2)) 4 a ∧
      okPolls (mbarLoc L (g / L.block) (.coordReady s)) ((X.tr g).take k) = u + 1 ∧
      arrivals (mbarLoc L (g / L.block) (.coordFree s)) ((X.tr g).take k) = u ∧
      w0Closed ((X.tr g).take k) = 4 * u + s.val := by
  obtain ⟨hw4, hr⟩ := hat
  have ht : tidOf L g < 128 := MemRow.wg0_tid hw4
  have hm : MemRow.MemEvent ⟨289, .rd a bs⟩ := .inl ⟨a, bs, rfl⟩
  obtain ⟨d, hR, ⟨hpc, hE⟩, -⟩ := wg0_at hp hX hFw he (Wg0.memEvent_noUb hm) hr
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only at hpc
  obtain rfl := vm_of_pc' hpc.symm
  simp only [Wg0.RefCore, Wg0.RefAt, Wg0.Site.reg, Wg0.Site.idx, Wg0.Control.D.words] at hc
  obtain ⟨r, ⟨-, -, -, -, -, hv, -⟩, hq, ha⟩ := hc
  dsimp only at hq ha
  have hr4 : r % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨a', bs', hk, hws⟩ := Wg0.rdAt_ws hm hE (Wg0.vm_loc hp ht (d := ⟨.vm, el, a0, l0, l1,
    cnt, bi, vs, pv, sl, ps, vt⟩) hv hr4)
  cases hk
  refine ⟨⟨r % 4, hr4⟩, r / 4, by simpa [tidOf] using hws, ?_, ?_, ?_⟩
  · show okPolls (MbarRow.loc L g (.coordReady ⟨r % 4, hr4⟩)) _ = _
    rw [wg0_okPolls hp hX hFw hw4, hq, Wg0.acq_ready hp]
    simp [Wg0.use, Wg0.ind, ringUses_here rfl hr4]
  · show arrivals (MbarRow.loc L g (.coordFree ⟨r % 4, hr4⟩)) _ = _
    rw [wg0_arrivals hp hX hFw hw4, ha, Wg0.arr_free hp]
    simp [Wg0.use, Wg0.ind, ringUses_here rfl hr4]
  · rw [w0Closed_arrs hp hX hFw hw4 hal]
    unfold MbarRow.arrs2
    rw [wg0_arrivals hp hX hFw hw4, wg0_arrivals hp hX hFw hw4, ha, ha,
      Wg0.arr_so hp _ _ _ 0, Wg0.arr_so hp _ _ _ 1]
    simp [ringUses]
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
