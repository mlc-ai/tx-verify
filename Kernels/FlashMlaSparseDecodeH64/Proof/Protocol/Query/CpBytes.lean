-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.CpSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.QueryTile
public import Lemmas.Tcgen05.MmaSources
import Lemmas.Tcgen05.TcProgramOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.DqClass
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QFill
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.CpOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CopyByte
import Lemmas.Tensor.LoadWrittenZero

@[expose] public section

/-! # The bytes a query copy reads

Each of the 4096 source bytes of a copy of the MMA lane is a byte of the dequantized tile 0 of its
CTA (`copy_foot`), the byte of one of the lane's eight query tensor loads. The lane's poll of
`qTma` before the copy observes that load, which is notified (`q_tload_finished`) and so has
written the byte (zero fill, `memWrites_of_notified_zero`): it is the source. Every other write of
the byte is that load again (`q_tload_ww`) or a dequant lane's chunk store, after the copy's read
(`q_cp_dq`); the other kinds of `dq_classify` write tile 1 only (`cp_bytes`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hR hI hB

/-- **A query load covering a byte of the tile has its write in the model**: after the lane's
poll of `qTma`, the byte `l` of the tile (CTA `c`) is written by the load that has `a` earlier
loads to `qTma`, a notified load with a memory write of the byte. -/
theorem q_tload_write {c jw pcw p : Nat} {acq : Bool} {sc : MbarScope} {l : Loc}
    (hpoll : X.get (mmaLane L X c, jw) =
      some ⟨pcw, .wait (mbarLoc L c .qTma) p true acq sc⟩)
    (hw4 : warp L (mmaLane L X c) = 4) (hmc : mmaLane L X c / L.block = c)
    (hl : MemRow.LocIn L c (.dequant 0) l) :
    ∃ iT pc al x y j : Nat, ∃ s : TensorCopy.Spec, ∃ b,
      X.get (mmaLane L X c, iT) = some ⟨pc, .tensorIssue al s⟩ ∧
      TensorCopy.writeLoc s x y j = some l ∧
      X.MemWrites (.async (mmaLane L X c, iT) (.write (.load x y j)))
        { loc := l, size := 1 } [b] := by
  obtain ⟨hls, hlc, hlo, hhi⟩ := hl
  simp only [Region.lo, Region.size, Fin.val_zero, Nat.mul_zero, Nat.add_zero] at hlo hhi
  obtain ⟨-, -, -, hall⟩ := qTma_observes hp hX hFw hR hI hB (mmaOne hp hX hFw) (c := c)
    (by simpa only [loc, hmc] using mma_issues_le hp hX hFw hw4)
    (by simpa only [loc, hmc] using mma_arrivals_le hp hX hFw hw4 (mbarLoc L c .qTma)) hpoll
  obtain ⟨iT, pc, al, s, hget, -, hcnt, -⟩ := hall ⟨(l.addr - L.sharedBase) / 8192, by omega⟩
  obtain ⟨a', -, hcnt', honto⟩ := mma_qLoad_onto hp hX hFw hw4 hget
  have haa : a' = (l.addr - L.sharedBase) / 8192 := by
    simp only [loc, hmc] at hcnt hcnt'
    omega
  obtain ⟨x, y, j, hwl⟩ := honto hls (by rw [hlc, hmc]) (by omega) (by omega)
  have hpoll' : X.get (mmaLane L X c, jw) = some ⟨pcw, .wait
      (mbarLoc L (mmaLane L X c / L.block) .qTma) p true acq sc⟩ := by rw [hmc]; exact hpoll
  have hfin := q_tload_finished hp hX hFw hR hI hB (x := x) (yy := y) (j := j) hget
    (mma_qLoad_at hp hX hFw hw4 hget) hpoll'
  obtain ⟨o, ho, hn⟩ := tensor_notified_of_finished hfin
  obtain ⟨⟨addr, pc', hiss⟩, -, -⟩ := hX.tensor _ o ho
  rw [hget] at hiss
  obtain ⟨-, hk⟩ := Event.mk.inj (Option.some.inj hiss)
  obtain ⟨-, rfl⟩ := Kind.tensorIssue.inj hk
  obtain ⟨hz, hf⟩ := mma_qLoad_zero hp hX hFw hw4 hget
  obtain ⟨b, hb⟩ := memWrites_of_notified_zero hX ho hn (hwl) hz hf
  exact ⟨iT, pc, al, x, y, j, _, b, hget, hwl, hb⟩

/-- **A query copy's byte has its source write, and every other write of it is ordered with it**
(the byte half of `CpSourcesT`): the source is the byte's query tensor load; another write is that
load again, or a dequant lane's chunk store after the copy's read. -/
theorem cp_bytes_ordered {g iC : Nat} {c : TcCopy.Spec} (hi : X.CpIssue (g, iC) c)
    {k : Nat} (hk : k < c.ctas.length * c.shape.sourceBytes) :
    ∃ src : MmaSources.ByteSource X, X.MmaFootprint (g, iC) false k src.loc ∧
      modelCausality L X src.loc src.ref (.async (g, iC) (.mmaRead false k)) ∧
      (∃ b, src.bytes = [b] ∧ src.access = { loc := src.loc, size := 1 }) ∧
      ∀ w a bs, X.MemWrites w a bs → a.Covers src.loc →
        w = src.ref ∨ modelCausality L X src.loc w src.ref ∨
          modelCausality L X src.loc (.async (g, iC) (.mmaRead false k)) w := by
  obtain ⟨pc, hC⟩ := hi
  have hat : MmaAt L g pc := cp_mmaAt hp hX hFw hC
  obtain ⟨k16, hsh, hsrc, hct⟩ := mma_cp_spec hp hX hFw hC ⟨hat.2.1, hat.2.2⟩
  have hk4096 : k < 4096 := by
    have := hk
    simp only [hsh, hct, List.length_singleton, TcCpShape.sourceBytes, TcCpShape.rows,
      TcCpShape.rowBytes] at this
    omega
  obtain ⟨l, hbl⟩ := MmaFoot.copy_byteLoc (B := L.sharedBase) (k := k16.val) (cta := g / L.block)
    hk4096
  have hB128 := shared_base_128 hp (L := L)
  obtain ⟨hls, hlc, hlo, hhi⟩ := MmaFoot.copy_foot hB128 k16.isLt hbl
  have hloc : MemRow.LocIn L (g / L.block) (.dequant 0) l :=
    ⟨hls, hlc, by simp only [Region.lo]; omega, by simp only [Region.lo, Region.size]; omega⟩
  have hf : X.MmaFootprint (g, iC) false k l := by
    refine Or.inr ⟨c, 0, g / L.block, ⟨pc, hC⟩, rfl, by rw [hct]; rfl, ?_, ?_⟩
    · rw [hsh]
      simp only [TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]
      omega
    · rw [hsh, hsrc]
      simp only [TcCpShape.sourceBytes, TcCpShape.rows, TcCpShape.rowBytes]
      rw [Nat.mod_eq_of_lt (by omega)]
      exact hbl
  have hlane : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) hC (fun _ h => by cases h) ⟨hat, mma_cp_on hp hX hFw hC hat⟩
  obtain ⟨jw, pcw, p, acq, sc, hjf, hpoll, -⟩ := UnitHandoff.exists_poll
    (m := mbarLoc L (g / L.block) .qTma) (h := g) (f := iC) (c := 0)
    (mma_cp_qWait hp hX hFw hC hat).ge
  have hw4 : warp L g = 4 := hat.1
  generalize hc : g / L.block = c' at *
  subst hlane
  obtain ⟨iT, pcT, al, x, y, j, s, b, hT, hwl, hW⟩ :=
    q_tload_write hp hX hFw hR hI hB hpoll hw4 hc hloc
  have hatT := mma_qLoad_at hp hX hFw hw4 hT
  have hpoll' : X.get (mmaLane L X c', jw) = some ⟨pcw, .wait
      (mbarLoc L (mmaLane L X c' / L.block) .qTma) p true acq sc⟩ := by rw [hc]; exact hpoll
  have hfin := q_tload_finished hp hX hFw hR hI hB (x := x) (yy := y) (j := j) hT hatT hpoll'
  have hlen : iC < (X.tr (mmaLane L X c')).length := (List.getElem?_eq_some_iff.mp hC).1
  have hbase : baseCausality L X (mmaLane L X c', jw) (mmaLane L X c', iC) :=
    .single (.inl (po_of_source_not_access rfl hjf hlen (by rw [hpoll]; rfl)))
  have hg := Frame.lt_of_get hX hC
  have hcov : Acc.Covers { loc := l, size := 1 } l :=
    Acc.covers_at (k := 0) (show 0 < 1 by decide)
  refine ⟨⟨l, .async (mmaLane L X c', iT) (.write (.load x y j)), _, [b], hW,
    Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩, hf, ⟨.inl ⟨hg, hg, rfl⟩, .direct
      ⟨⟨_, true, hW.intent, hcov⟩, ⟨_, false, ⟨rfl, rfl, hf⟩, hcov⟩, .inl ⟨_, hfin, hbase⟩⟩⟩,
    ⟨b, rfl, rfl⟩, ?_⟩
  intro w a bs hw hcov
  cases hcl : dq_classify hp hX hFw hw.intent hcov hloc with
  | dq hW' hat' hcov' hc' =>
    exact .inr (.inr (q_cp_dq hp hX hFw hR hI hB hC hat hf hls hW' hat' hcov' (hc'.trans hc.symm)))
  | stage _ _ hr _ _ _ => exact absurd hr (by decide)
  | tload _ hT' hatT' hrl hc' =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
      q_tload_ww hp hX hFw hT hatT hwl hT' hatT' hrl (hc.trans hc'.symm)
    exact .inl rfl

/-- **A query copy's byte has its source write, and every other write of it is ordered with it**
(the byte half of `CpSourcesT`). -/
theorem cp_bytes {g iC : Nat} {c : TcCopy.Spec} (hi : X.CpIssue (g, iC) c)
    {k : Nat} (hk : k < c.ctas.length * c.shape.sourceBytes) :
    ∃ src : MmaSources.ByteSource X, X.MmaFootprint (g, iC) false k src.loc ∧
      ∀ w a bs, X.MemWrites w a bs → a.Covers src.loc →
        w = src.ref ∨ modelCausality L X src.loc w src.ref ∨
          modelCausality L X src.loc (.async (g, iC) (.mmaRead false k)) w := by
  obtain ⟨src, hf, -, -, h⟩ := cp_bytes_ordered hp hX hFw hR hI hB hi hk
  exact ⟨src, hf, h⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
