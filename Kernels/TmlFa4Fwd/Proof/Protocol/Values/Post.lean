-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.TileGeom
public import Lemmas.Kernel.Goals
import Kernels.TmlFa4Fwd.Proof.Correction.Export.LseWrites
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.OutWrites
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Lib.OutputGeom
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.OutOrdered
import Lemmas.Kernel.FrameEnd
import Lemmas.Step.ReadSource
import Lemmas.Tcgen05.MemFloat
import Lemmas.TensorStore.StoreWrite

@[expose] public section

/-! # The result of a complete execution from the values of its output writes

Every O byte and every log-sum-exp word of the result is written in a complete execution: a lane
that exits stored its work item (`o_written`, `lse_written`). The writers of a byte agree
(`OutputValues`, `LseWriteValues`), so the final byte is theirs, and no other global byte is
written: the kernel's result (`post_of_values`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The values carried by all completed, covering O writes. -/
def OutputValues (p : Params) (X : Execution) : Prop :=
  ∀ b < p.batch, ∀ h < p.heads, ∀ row < p.qLength b, ∀ d < 128, ∀ k < 4,
    ∀ w a bytes, X.MemWrites w a bytes → a.Covers ((p.oLoc (p.qOffset b + row) h d).at k) →
      wbyte a bytes ((p.oLoc (p.qOffset b + row) h d).at k) =
        some ((Value.float .f32 (attention p b h row d)).byteAt k)

/-- An LSE write is of a row's word, and of the row's value. -/
def LseWriteValue (p : Params) (a : Acc) (bytes : List Byte) : Prop :=
  ∃ batch < p.batch, ∃ head < p.heads, ∃ row < p.qLength batch,
    a.loc = p.lseLoc (p.qOffset batch + row) head ∧ a.size = 4 ∧
      bytes = (Value.float .f32 (lse p batch head row)).toBytes

/-- The values carried by the global stores. -/
def LseWriteValues (p : Params) (X : Execution) : Prop :=
  ∀ i a bytes, X.Writes i a bytes → a.loc.space = .global → LseWriteValue p a bytes

/-- A completed byte has a writer, and every covering writer agrees with its value. -/
def ByteWritten (X : Execution) (loc : Loc) (value : Byte) : Prop :=
  (∃ w a bytes, X.MemWrites w a bytes ∧ a.Covers loc) ∧
    ∀ w a bytes, X.MemWrites w a bytes → a.Covers loc → wbyte a bytes loc = some value

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {out : FinalMem}

theorem ByteWritten.in_final (hX : Consistent L kernel Assumptions.all m X)
    (hf : IsFinal L m X out) {loc : Loc} {value : Byte} (h : ByteWritten X loc value) :
    out loc = some (some value) := by
  obtain ⟨ws, hws⟩ := Step.writers_finite hX
  obtain ⟨⟨w, a, bs, hw, hc⟩, hv⟩ := h
  exact hf.of_agree (fun w a b hw _ => hws w a b hw) hw hc hv

/-- A row of the packed queries is of one request. -/
theorem packed_row_inj (hp : Pre p L m) {b b' row row' : Nat} (hb : b < p.batch)
    (hb' : b' < p.batch) (hr : row < p.qLength b) (hr' : row' < p.qLength b')
    (he : p.qOffset b + row = p.qOffset b' + row') : b = b' ∧ row = row' := by
  have below : ∀ {x y z : Nat}, x < y → y < p.batch → z < p.qLength x →
      p.qOffset x + z < p.qOffset y := by
    intro x y z hxy hy hz
    have := hp.qOffset_mono (show x + 1 ≤ y from hxy) (by omega)
    unfold Params.qLength at hz
    omega
  rcases Nat.lt_trichotomy b b' with h | rfl | h
  · have := below h hb' hr
    omega
  · exact ⟨rfl, by omega⟩
  · have := below h hb hr'
    omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hD : Complete L X)
include hp hX hFw hD

omit hp hFw in
private theorem exits {g : Nat} (hg : g < L.threads) :
    ∃ k pc, X.get (g, k) = some ⟨pc, .exit⟩ := by
  obtain ⟨k, pc, -, he⟩ := Frame.Complete.exit_last hD hg (by
    rintro ⟨-, request, h⟩
    obtain ⟨i, s, ts, -, hi, -⟩ := hX.clc.canceled_has_issue h
    exact noClcIssue hX hi)
  exact ⟨k, pc, he⟩

/-- **Every O byte of the result is written.** -/
theorem o_written {b h row d k : Nat} (hb : b < p.batch) (hh : h < p.heads)
    (hr : row < p.qLength b) (hd : d < 128) (hk : k < 4) :
    ∃ w a bytes, X.MemWrites w a bytes ∧ a.Covers ((p.oLoc (p.qOffset b + row) h d).at k) := by
  obtain ⟨hC, hlo, hhi, hco⟩ := hp.row_workItem hb hr hh
  generalize workItem p b (row / 256) h = c at hC hlo hhi hco
  have hco : Epilogue.assignedCoordinates p b c = (row / 256, h) := hco
  have hB := hp.block
  have hdiv : (c * 512 + 416) / L.block = c := by rw [hB]; omega
  have hg : c * 512 + 416 < L.threads := by
    change _ < L.grid * L.block
    rw [hB]; omega
  obtain ⟨e, pc, he⟩ := exits hX hD hg
  obtain ⟨j, addr, b', hb', hlo', hhi', hi⟩ := out_writes hp hX hFw
    (by unfold Prologue.warpIndex; rw [hB]; omega) hb (by rw [hdiv]; exact hhi) he
    ⟨row % 256 / 128, by omega⟩ ⟨d / 32, by omega⟩
  rw [hdiv] at hlo' hhi' hi
  obtain rfl := Work.unique ⟨hb, hlo, hhi⟩ ⟨hb', hlo', hhi'⟩
  rw [hco] at hi
  have hrow : Epilogue.stageRow (row / 256) ⟨row % 256 / 128, by omega⟩ + row % 128 = row := by
    dsimp only [Epilogue.stageRow]
    omega
  have hl := writebackWriteLoc (g := c * 512 + 416) (tile := row / 256) hp
    ⟨row % 256 / 128, by omega⟩ ⟨d / 32, by omega⟩ (d % 32) (row % 128) k hb hh
  dsimp only at hl
  rw [hrow, show 32 * (d / 32) + d % 32 = d by omega,
    ite_eq_left ⟨by omega, by omega, hk, hr⟩] at hl
  obtain ⟨o, byte, -, -, hw⟩ := hD.store_write hX hi hl
  exact ⟨_, _, _, hw, rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩

/-- **Every byte of the log-sum-exp words of the result is written.** -/
theorem lse_written {b h row k : Nat} (hb : b < p.batch) (hh : h < p.heads)
    (hr : row < p.qLength b) (hk : k < 4) :
    ∃ w a bytes, X.MemWrites w a bytes ∧ a.Covers ((p.lseLoc (p.qOffset b + row) h).at k) := by
  obtain ⟨hC, hlo, hhi, hco⟩ := hp.row_workItem hb hr hh
  generalize workItem p b (row / 256) h = c at hC hlo hhi hco
  have hco : Epilogue.assignedCoordinates p b c = (row / 256, h) := hco
  have hB := hp.block
  have hdiv : (c * 512 + (256 + row % 128)) / L.block = c := by rw [hB]; omega
  have hmod : (c * 512 + (256 + row % 128)) % L.block % 128 = row % 128 := by rw [hB]; omega
  have hg : c * 512 + (256 + row % 128) < L.threads := by
    change _ < L.grid * L.block
    rw [hB]; omega
  obtain ⟨e, pc, he⟩ := exits hX hD hg
  have hsum : 256 * (row / 256) + 128 * (row % 256 / 128) + row % 128 = row := by omega
  obtain ⟨j, pc', a, bs, hj, hl, hz⟩ := lse_writes hp hX hFw
    (by unfold Prologue.warpIndex; rw [hB]; omega) (by unfold Prologue.warpIndex; rw [hB]; omega)
    hb (by rw [hdiv]; exact hlo) (by rw [hdiv]; exact hhi) ⟨row % 256 / 128, by omega⟩
    (by rw [hdiv, hco, hmod]; dsimp only; omega) he
  rw [hdiv, hco, hmod] at hl
  dsimp only at hl
  rw [hsum] at hl
  refine ⟨.thread (_, j), a, bs, .inl ⟨pc', hj⟩, ?_⟩
  rw [Acc.Covers, hl, hz]
  exact ⟨rfl, rfl, Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩

omit hD in
/-- **Every writer of a log-sum-exp byte carries the row's value.** -/
theorem lse_agree (hV : LseWriteValues p X) {b h row k : Nat} (hb : b < p.batch)
    (hh : h < p.heads) (hr : row < p.qLength b) (hk : k < 4) {w : AsyncCopy.Ref} {a : Acc}
    {bs : List Byte} (hw : X.MemWrites w a bs)
    (hc : a.Covers ((p.lseLoc (p.qOffset b + row) h).at k)) :
    wbyte a bs ((p.lseLoc (p.qOffset b + row) h).at k) =
      some ((Value.float .f32 (lse p b h row)).byteAt k) := by
  have hs : a.loc.space = .global := hc.1.symm
  have hq := packedRow_lt hp hb hr
  rcases globalWriteIntentSources hX hw.intent hs with
    ⟨i, pc, bytes, rfl, -, he⟩ | ⟨i, x, y, z, pc, addr, spec, rfl, -, -, hloc, hz⟩
  · have hW : X.Writes i a bs := by
      rcases hw with hw | ⟨old, pc', h'⟩
      · exact hw
      · rw [he] at h'; cases h'
    obtain ⟨b', hb', h', hh', r', hr', hl, hz, rfl⟩ := hV i a bs hW hs
    obtain ⟨-, -, c3, c4⟩ := hc
    have hq' := packedRow_lt hp hb' hr'
    have hst : p.totalQ ≤ p.lseStride := hp.lseStride
    unfold wbyte
    rw [hl] at c3 c4 ⊢
    rw [hz] at c4
    simp only [Params.lseLoc, globalLoc, Loc.at] at c3 c4 ⊢
    obtain ⟨rfl, hqq⟩ := Nat.digits_of_eq (lt_of_lt_of_le hq hst) (lt_of_lt_of_le hq' hst)
      (show h * p.lseStride + _ = h' * p.lseStride + _ by omega)
    obtain ⟨rfl, rfl⟩ := packed_row_inj hp hb hb' hr hr' hqq
    rw [Nat.add_sub_cancel_left]
    have hWidth : (Value.float .f32 (lse p b h row)).bytes = 4 := rfl
    simp only [Value.toBytes, List.getElem?_map, hWidth, List.getElem?_range hk, Option.map_some]
  · exfalso
    obtain ⟨-, -, c3, c4⟩ := id hc
    rcases global_write_shape hp hX hFw hw.intent hs with ⟨q, hq', h', hh', hl, hz'⟩ | ⟨-, ho⟩
    · omega
    · have hcov : a.loc = (p.lseLoc (p.qOffset b + row) h).at k := Acc.loc_of_one hc hz
      rw [hcov] at ho
      exact lse_not_o hp (a := ⟨p.lseLoc (p.qOffset b + row) h, 4, false, false, .cta, 0, false⟩)
        (l := (p.lseLoc (p.qOffset b + row) h).at k) hq hh rfl rfl
        ⟨rfl, rfl, Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩ ho

/-- **The result of a complete execution**, from the values of its output writes. -/
theorem post_of_values (hf : IsFinal L m X out) (hO : OutputValues p X)
    (hV : LseWriteValues p X) : Post p m out := by
  refine ⟨?_, fun l => ?_⟩
  · intro b hb h hh row hr
    exact ⟨fun d hd => memFloat_float fun k hk => ByteWritten.in_final hX hf
        ⟨o_written hp hX hFw hD hb hh hr hd hk, hO b hb h hh row hr d hd k hk⟩,
      memFloat_float fun k hk => ByteWritten.in_final hX hf
        ⟨lse_written hp hX hFw hD hb hh hr hk,
          fun _ _ _ hw hc => lse_agree hp hX hFw hV hb hh hr hk hw hc⟩⟩
  · intro hg hno hnl
    refine hf.unwritten fun w a bs hw hc => ?_
    rcases global_write hp hX hFw hw.intent hc hg with h | ⟨q, hq, h, hh, k, hk, rfl⟩
    · exact hno h
    · exact hnl q hq h hh k hk rfl

end
end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
