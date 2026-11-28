-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.ARead
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Wrote
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Live
public import Lemmas.Tcgen05.TmemLatestSource
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.CellCover
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Mma.Export.Cover
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues

@[expose] public section

/-! # A PV MMA's read of the probabilities has a source

The A read of a PV MMA of block `b` takes the cells of the score buffer of parity `(b - 1) % 2`,
written by the QK MMAs of block `b - 1` (every QK step writes the whole tile) and the probability
stores. The QK MMAs of block `b - 1` are done before the PV MMA; the latest write before it is the
source (`TcMma.readSourceOfCandidate`), every writer being ordered with the read
(`Tmem.a_read_order`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A PV MMA's A read has a source**, and its issue is the accumulator-256 one. -/
public theorem a_read_source (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hWrites : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
    {r : EvId} {cell : Cell} (hr : X.MmaACell r cell) :
    ∃ source, ReadSource L X .a source r cell ∧
      ∃ pc d s acc mask, X.get r = some ⟨pc, .tc (.mma d s acc mask)⟩ ∧ d = 256 ∧
        cell.column < 192 := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  obtain ⟨g,kp⟩ := r
  obtain ⟨d,s,acc,mask,index,b0,⟨pc,he⟩,hac⟩ := id hr
  obtain ⟨hmask,lo,hi,bc,qk|pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j,-,-,none,-⟩ := qk
    simp [aCell,none] at hac
  obtain ⟨j,hpcj,hd256,-,hdesc⟩ := pv
  obtain ⟨b,-,pb,one,-,⟨j',hat⟩,warp,-⟩ := Mma.Export.pv_block hp hX hf base he ⟨j,hpcj⟩
  obtain ⟨-,qkPrior,-,-⟩ := Mma.Export.pv_prior hp hX hf words hu he hpcj
  obtain ⟨kq,ltq,d2,s2,a2,m2,gw,q⟩ := qkPrior 0
  obtain ⟨b2,hd2,q1,-,warp2,-⟩ := Mma.Export.qk_block hp hX hf base gw ⟨0,rfl⟩
  obtain ⟨hmask2,lo2,hi2,bc2,qk2|pv2⟩ := Mma.Export.columns hp hX hf base gw
  swap
  · obtain ⟨j2,hpc2,-⟩ := pv2
    have ne : ∀ j : Fin 8, Lib.qkIssue 0 ≠ Lib.pvIssue j := by decide
    exact (ne j2 hpc2).elim
  obtain ⟨-,-,-,-,hdesc2⟩ := qk2
  have hb2 : b2 + 1 = b := by omega
  have hwrite : X.MmaCell (g,kq) cell := by
    have hj8 := j'.isLt
    have cover := qk_writes_a (s := s2) (s' := s) (d := d2) (a := 128*((b-1)%2)+8*j'.val)
      (index := index) (cell := cell) (b := b0) hdesc2 hdesc hat (by rw [lo2, lo])
      (by rw [hi2, hi]) (by omega) (by omega) (by omega) (by omega) hac
    obtain ⟨row,col,hw⟩ := cover
    subst hmask2
    exact ⟨d2,s2,a2,[0,0,0,0],row,col,⟨_,gw⟩,hw⟩
  have hrange := mma_a_range hp hX hf base he hat hr
  have hmaster : ∀ w, TmemWrite L X w cell →
      WriteBefore L X w (g,kp) ∨ ReadBefore L X .a (g,kp) w := fun w hw => by
    rcases a_read_order hp hX hf safe base rows init hr hw with h | h | h
    · exact .inr (.inl h.symm)
    · exact .inl h
    · exact .inr h
  have hlive : ∀ w, TmemWrite L X w cell → WriteBefore L X w (g,kp) →
      SourceLive L X w (g,kp) cell := fun w _ _ =>
    source_live_mma hX ht hmd ⟨pc,he⟩ hrange.1
  have hwb : WriteBefore L X (g,kq) (g,kp) :=
    qk_wb_pv hp hX hf rows init words (Frame.lt_of_get hX he) he gw ⟨0,rfl⟩ pb one q1 warp2
      (by omega) (by omega)
  obtain ⟨src,hsrc⟩ := readSourceOfCandidate hX hG hWrites hmaster hlive (.inl hwrite) hwb
  have hj8 := j'.isLt
  exact ⟨src, hsrc, pc, d, s, acc, mask, he, hd256, by omega⟩

/-- **A done PV MMA's A read has a source with a value.** -/
public theorem a_source (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hWrites : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
    {r : EvId} {cell : Cell}
    (hCV : ∀ i d s acc mask, X.MmaIssue i d s acc mask → X.MmaCell i cell →
      WriteBefore L X i r → CompletedValues L Assumptions.all X i)
    (hr : X.MmaACell r cell) :
    ∃ source value, ReadSource L X .a source r cell ∧
      Wrote L Assumptions.all X source cell value := by
  obtain ⟨src, hsrc, pc, d, s, acc, mask, he, hd256, hlt⟩ :=
    a_read_source hp hX hf hu safe base rows init hG hWrites ht hmd hr
  obtain ⟨value, hv⟩ := wrote_of hX (fun d s acc mask hi hm => hCV _ d s acc mask hi hm hsrc.2.2.1)
    hsrc.2.1 fun hm => by
    obtain ⟨pcs, ds, ss, as, ms, hget, -, hdle, -⟩ := mma_write_cell hp hX hf base hm
    refine mma_done_of_wb hX hget he ?_ hsrc.2.2.1
    omega
  exact ⟨src, value, hsrc, hv⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem
