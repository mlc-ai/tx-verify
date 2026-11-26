-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Origin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane

@[expose] public section

/-! # Warpgroup 0's output tensor stores: their box origin

A tensor store of a lane of warps 0 and 1 of warpgroup 0 is a tile store of the output map
whose box starts at column `128 w + col` (`col` of its chunk), head `0`, the query row and batch
of the lane's CTA (`wg0_storeOrigin`; a later warp does not store). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The origin of an output tensor store**: a store of a lane of warps 0 and 1 is a tile store
(no gather rows) of the origin `(128 w + col, 0, %ctaid.x, %ctaid.y)` with `col` of its chunk
(`0, 64, 256, 320`); the chunk is the store's pc's (`1358, 1516, 1673, 1831`). -/
theorem wg0_storeOrigin (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : MbarRow.Wg0At L g e.pc) {a : Nat} {s : TensorStore.Spec}
    (hk : e.kind = .tensorStore a s) (hw2 : MbarRow.warp L g < 2) :
    s.rows = none ∧ ∃ c < 4, e.pc = [1358, 1516, 1673, 1831].getD c 0 ∧ BoxOrigin s.origin
      [128 * MbarRow.warp L g + [0, 64, 256, 320].getD c 0, 0, ctaidX L g, ctaidY L g] := by
  obtain ⟨hw4, hr⟩ := hat
  have hw : MbarRow.warp L g = warpOf L g := by
    simp only [MbarRow.warp, warpOf, tidOf_x_eq hp, tidOf_eq hp]
  have hwt : (warpW L g).toNat = MbarRow.warp L g := by
    have := warpOf_lt hp (g := g)
    simp only [warpW, BitVec.toNat_ofNat]
    rw [hw]
    omega
  obtain ⟨d, -, ⟨hpc, hE⟩, -⟩ := wg0_at hp hX hFw he (fun f h => by rw [hk] at h; cases h) hr
  obtain ⟨st, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk
  subst hpc hk
  cases st
  case otma c =>
    rcases hE with ⟨a', s', hk', -, -, -, -, -, hor⟩ | ⟨f, hf⟩
    · cases hk'
      obtain ⟨hrows, hor⟩ := hor (by omega)
      refine ⟨hrows, c.val, c.isLt, ?_, ?_⟩
      · show Wg0.Site.pc (.otma c) = _
        fin_cases c <;> rfl
      rw [← hwt]
      fin_cases c <;> exact hor
    · cases hf
  all_goals simp [Wg0.EvK, Wg0.TcLdEv, Wg0.TcStEv, Wg0.NcEv, Wg0.PollEv, Wg0.ArrEv, RdAt, WrAt,
    GenWrAt, GWrAt] at hE

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
