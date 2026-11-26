-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PexAsync
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PStoreAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.PvFoot
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem

@[expose] public section

/-! # A P store of block `d` is before the PV MMA of block `d` in the tcgen05 order

A write of warpgroup 0 at pc `704 + j` (a P store) of the lane's block `d` (the barrier-9 count
`2 d + 2`) has a `TcStep` path to the PV MMA that polls `soReady` for use `d` (`pex_tc`): the
store is before the arrival and the proxy fence that end its block, which are before the MMA's
poll. The facts of the stored words may thus be taken from the induction on that order. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The P store of the block a PV MMA reads is before it** (`TcStep` path). -/
theorem pv_a_tc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X)
    (hB : Bar0Rows L X) {g i pc bb d h k pcw j : Nat} {s : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {ac : Acc} {bs : List Byte}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma bb s acc mask)⟩) (hbb : bb < 256)
    (hd : ∀ jj : Fin 2, okPolls (mbarLoc L (g / L.block) (.soReady jj)) ((X.tr g).take i) =
      ringUses 2 jj (d + 1))
    (hW : X.get (h, k) = some ⟨pcw, .wr ac bs⟩) (hpcw : pcw = 704 + j) (hj : j < 4)
    (hw : warp L h < 4) (hhw : h / L.block = g / L.block)
    (hcnt : ((X.tr h).take k).countP (Execution.isBarId 9) = 2 * d + 2) :
    Relation.TransGen (TcMma.TcStep L X) (h, k) (g, i) := by
  have hon := TmRace.pv_on (tmem_rows hp hX hFw) hX hx hbb
  have hg : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hx (fun _ h => by cases h) hon
  have hhg : g = mmaLane L X (h / L.block) := by rw [hhw]; exact hg
  have hcg : g / L.block = h / L.block := hhw.symm
  subst hpcw
  obtain ⟨el, hel, hsz, hloc⟩ := wg0_ostAt hp hX hFw hw hj hW
  have hb384 : L.block = 384 := hp.block
  have ht : tidOf L h < 128 := MemRow.wg0_tid hw
  have hacc : X.Access (h, k) ac true := .inr (.inl ⟨bs, ⟨_, hW⟩, rfl⟩)
  have hcov : ac.Covers ac.loc := by
    unfold Acc.Covers Loc.InRange
    exact ⟨rfl, rfl, le_rfl, by omega⟩
  have hlg : MemRow.LocIn L (h / L.block) .pExchange ac.loc := by
    rw [hloc]
    refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [wsLoc, Region.lo, Region.size] <;> omega
  obtain ⟨e, hW0, -⟩ := pex_cls hp hX hFw hacc hcov hlg
  obtain ⟨r, -, hu, hblk⟩ := hW0.use
  have hr : r = d := by
    unfold PexUse at hu
    rcases hu with hu | hu | hu <;> omega
  exact pex_tc hp hX hFw hR hI hB hW0 hblk ⟨_, hW⟩ hx hhg hcg (fun jj => hd jj) (by omega)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
