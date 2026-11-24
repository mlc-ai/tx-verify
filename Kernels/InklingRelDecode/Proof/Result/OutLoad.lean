-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.OutEpi
public import Kernels.InklingRelDecode.Proof.Interface.ResultThreads
public import Kernels.InklingRelDecode.Proof.Result.MmaAll

@[expose] public section

/-!
# The epilogue's load of the `O` tile reads the PV accumulator (result layer, part 2c)

The epilogue's `tcgen05.ld.16x32bx2.x64` (`Epi.Site.ld`: address `Prm.taddr`, 64 words) of thread
`g` reads, in register `j`, the Tensor Memory cell of row `rowM tid` and column
`tm + 256 + 64 · half + j` of the PV accumulator of its CTA: `taddr_cell`, which unfolds Core's
`tcDataCell` for the shape `.16x32bx2` (lane `32 · warp + tid % 16`, the upper half-warp
at column offset `64`). With that, the value the load returns in register `j` is the one its read
source wrote: `load_word` applies `Mma.o_load` (the last PV MMA of block `numIters - 1` is the read
source of the cell) and `oFull_last` (`OutProb.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma PTX.TcMma

noncomputable section

/-- **The cell register `j` of the epilogue's load reads**: row `rowM tid`, column
`tm + 256 + 64 · half + j` of the accumulator of the thread's CTA, whatever lane bits the
broadcast returned (the lane field is a multiple of 32, so the chunk offset is 0). -/
theorem taddr_cell (L : Launch) (g : Nat) {pr : Epi.Prm} (htm : pr.tm + 384 ≤ 512)
    (hc0 : pr.c0 = (pr.tm + 256) % 2 ^ 32) (j : Nat) :
    tcDataCell L g (.s16x32bx2 64) pr.taddr j =
      oCell (g / L.block) pr.tm (Epi.rowM (g % L.block)) (64 * Epi.halfM (g % L.block) + j) := by
  unfold tcDataCell TcShape.base TcShape.laneIn TcShape.columnIn TcShape.lanes laneBase
    chunkOffset Epi.Prm.taddr oCell Epi.rowM Epi.halfM laneOf
  have hc : pr.c0 = pr.tm + 256 := by rw [hc0]; omega
  rw [hc]
  simp only [Epi.M32]
  split_ifs with h1 <;> congr 1 <;> omega

/-- The coordinates of two threads of one CTA agree. -/
theorem cta_eq {L : Launch} {g g' : Nat} (h : g' / L.block = g / L.block) :
    reqOf L g' = reqOf L g ∧ splitOf L g' = splitOf L g ∧ kvhOf L g' = kvhOf L g := by
  unfold reqOf splitOf kvhOf ProA.cta
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The words of the epilogue's load are the numerators of the row's columns.** For an
epilogue state `d` of a valid-row thread `g` of the default partition, whose Tensor Memory load
(event `k0`) returned `d.o` and whose registers are `Epi.Means`: if the last PV MMA of the CTA
(block `num_iters - 1`, `num_iters ≥ 1`) is the read source of each of the load's 64 cells, then
register `j` is the f32 float of the numerator `o` of the row's softmax run at column
`outCol0 + j`. -/
theorem load_word (hpre : Pre Q L mem0) (hf : Interface.ThreadFacts Q L mem0 X)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hcomp : Complete L X)
    (hc : KvCopies Q L X) (ho : KvOrder Q L X) (hw : MmaWords Q L X)
    (hP : PTile Q L X (pElemE Q L)) (hO : OAcc Q L X (alphaRow Q L))
    {g k0 : Nat} {d : Epi.D} (_ht : g % L.block < 128) (hm : Epi.Means Q L g d.pr)
    (hrv : d.pr.rv = true) (hlen : d.o.length = 64) {pc : Nat}
    (hld : X.get (g, k0) = some ⟨pc, .tc (.ld d.pr.taddr d.o (.s16x32bx2 64))⟩)
    {m : EvId} {pcm dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} {dm : Mma.D}
    {P : Loader.Pro} (hmg : m.1 < L.threads) (hcta : m.1 / L.block = g / L.block)
    (he : X.get m = some ⟨pcm, .tc (.mma dst sp acc mask)⟩)
    (hσ : Interface.St Q L X m.1 m.2 = some (some (.w (.mma dm P)))) (hs : dm.site = .pv 7)
    (hN : 1 ≤ Q.numIters (reqOf L g) (splitOf L g))
    (hi : dm.i = Q.numIters (reqOf L g) (splitOf L g)) (htm : d.pr.tm = dm.tm)
    (hrs : ∀ j < 64, ReadSource L X .ld m (g, k0)
      (tcDataCell L g (.s16x32bx2 64) d.pr.taddr j)) :
    ∀ j < 64, d.o.getD j (b32 0) = fl (colState Q (reqOf L g) (splitOf L g)
      (Epi.tokM (g % L.block)) (Epi.outHead L g) (Epi.outCol0 L g + j)).o := by
  intro j hj
  obtain ⟨hreq, hspl, hkvh⟩ := cta_eq (L := L) hcta
  have hT : dm.tm = 0 := hw.tm (m := m) ⟨P, hσ⟩
  have hrow : QRowValid Q L m.1 (Epi.rowM (g % L.block)) := by
    have h1 := of_decide_eq_true (hm.rv.symm.trans hrv)
    unfold QRowValid
    rw [hreq]
    exact ⟨h1.1, h1.2⟩
  have hcell := taddr_cell L g (pr := d.pr) (by omega) hm.c0 j
  have hld' : X.TLd (g, k0) d.pr.taddr d.o (.s16x32bx2 64) := ⟨pc, hld⟩
  have hlc : LoadCell L X (g, k0) j (oCell (m.1 / L.block) dm.tm (Epi.rowM (g % L.block))
      (64 * Epi.halfM (g % L.block) + j)) :=
    ⟨_, _, _, hld', by omega, by rw [hcta, ← htm]; exact hcell.symm⟩
  have hrs' := hrs j hj
  rw [hcell, htm, ← hcta] at hrs'
  have hv := o_load hpre hf hX hcomp hc ho hw hP hO hmg he hσ hs
    (b := Q.numIters (reqOf L g) (splitOf L g) - 1) (by omega) hrow
    (n := 64 * Epi.halfM (g % L.block) + j) (by unfold Epi.halfM; omega) hld' hlc hrs'
  have hl := oFull_last (Q := Q) (L := L) m.1 (Epi.rowM (g % L.block))
    (64 * Epi.halfM (g % L.block) + j) (Q.numIters (reqOf L g) (splitOf L g) - 1)
    (by rw [hreq, hspl]; omega)
  rw [hreq, hspl, hkvh] at hl
  rw [hl] at hv
  rw [List.getD_eq_getElem?_getD, hv]
  have e1 : Epi.rowM (g % L.block) / 6 = Epi.tokM (g % L.block) := rfl
  have e2 : group * kvhOf L g + Epi.rowM (g % L.block) % 6 = Epi.outHead L g := rfl
  have e3 : 64 * Epi.halfM (g % L.block) + j = Epi.outCol0 L g + j := rfl
  rw [e1, e2, e3]
  rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
