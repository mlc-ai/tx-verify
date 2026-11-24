-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.MmaPremises
public import Kernels.InklingRelDecode.Proof.Result.MmaBf16
public import Lemmas.Tcgen05.MmaReadSources
public import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

/-!
# The MMA events as abstract states, and what an operand byte is

* `mma_event_cases`: an MMA event of a launched thread is a QK MMA `j` of an iteration `i` or a PV
  MMA `j` of an iteration `i` (block `i - 1`), issued from the MMA warp's state
  (`Interface.mma_event_state`); its spec is the one of `EvW.QkIssue` / `EvW.PvIssue`: the decoded
  descriptor `qkDesc` / `pvDesc`, the shared descriptors of the operands, both CTAs the thread's.
* `read_byte_of_write`: the byte an MMA operand read observes is the byte of an ordered write of
  the location (`Lemmas/Async/ReadReuse.lean` for an operand read; the same statement as
  `mma_read_of_tensor_write` for any writer).
* `element_bf16`: two operand bytes that are the two bytes of a bf16 value are that element.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.Flow PTX.Proof PTX.TcMma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts mma_event_state)
open PTX.Kernels.InklingRelDecode.Proof.Ring.Foot (qkDesc pvDesc qkDesc_eq pvDesc_eq)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### An operand byte is the byte of the write that precedes its read -/

/-- **An MMA operand read observes the byte of an ordered write.** The write `w` covers the byte
`l`, is causally before the read, and every other write covering `l` is before it or after the
read: the read observes the byte of `w` at `l`. -/
theorem read_byte_of_write (hX : Consistent L kernel Assumptions.all mem0 X) {m : EvId}
    {isB : Bool} {idx : Nat} {l : Loc} {obs : Option Byte} (hr : X.MmaRead m isB idx l obs)
    {w : AsyncCopy.Ref} {dst : Acc} {written : List Byte} (hw : X.MemWrites w dst written)
    (hc : dst.Covers l) (hv : modelCausality L X l w (.async m (.mmaRead isB idx)))
    (horder : ∀ other fp bytes, X.MemWrites other fp bytes → fp.Covers l →
      other = w ∨ modelCausality L X l other w ∨
        modelCausality L X l (.async m (.mmaRead isB idx)) other) :
    obs = wbyte dst written l := by
  have h := read_byte_of_ordered_reuse hX hr.memReads (k := 0) (by exact Nat.zero_lt_succ 0) hw
    (by simpa [Loc.at] using hc) (by simpa [Loc.at] using hv)
    (by simpa [Loc.at] using horder)
  simpa [Loc.at] using h

/-- **An element whose two bytes are the two bytes of a bf16 value is that value.** -/
theorem element_bf16 {o : FloatFmt} {op : Operand} {bytes : List (Option Byte)} {row k : Nat}
    {x : ℝ}
    (h0 : bytes[2 * (row * 16 + k)]? = some (some ((Value.float .bf16 x).byteAt 0)))
    (h1 : bytes[2 * (row * 16 + k) + 1]? = some (some ((Value.float .bf16 x).byteAt 1))) :
    Assumption.idealMmaElement (.f16 .bf16 o) op bytes row k = .ok x := by
  apply idealMmaElement_of_bytes_bf16
  have := take_two h0 h1
  rw [this]
  simp [Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ]

/-! ### The MMA events -/

/-- The spec of a QK MMA of iteration `i`, step `j`, issued by a thread of CTA `cta`. -/
structure QkOp (L : Launch) (cta i j : Nat) (sp : OperandSpec) : Prop where
  desc : sp.descriptor = qkDesc
  a : TcShared.decode (EvW.mmQkALo L j + Mma.descHi * 2 ^ 32) = some sp.a
  b : TcShared.decode (EvW.mmQkBLo L (i % 3) j + Mma.descHi * 2 ^ 32) = some sp.b
  aTmem : sp.aTmem = none
  low : sp.lowCta = cta
  high : sp.highCta = cta

/-- The spec of a PV MMA of iteration `i`, step `j` (block `i - 1`). -/
structure PvOp (L : Launch) (cta i j : Nat) (sp : OperandSpec) : Prop where
  desc : sp.descriptor = pvDesc
  b : TcShared.decode (EvW.mmPvBLo L ((i - 1) % 3) j + 2 ^ 26 + Mma.descHi * 2 ^ 32) = some sp.b
  a : sp.a = sp.b
  low : sp.lowCta = cta
  high : sp.highCta = cta

theorem qkOp_of_issue {cta tm i j pc pc' dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat}
    (h : EvW.QkIssue L cta tm i j pc' ⟨pc, .tc (.mma dst sp acc mask)⟩) :
    QkOp L cta i j sp ∧ dst = tm + 128 * (i % 2) ∧ acc = decide (j ≠ 0) ∧
      mask = [0, 0, 0, 0] := by
  obtain ⟨da, db, dsc, hd, hda, hdb, he⟩ := h
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := he
  exact ⟨⟨qkDesc_eq hd, hda, hdb, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem pvOp_of_issue {cta tm i j pc pc' dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat}
    (h : EvW.PvIssue L cta tm i j pc' ⟨pc, .tc (.mma dst sp acc mask)⟩) :
    PvOp L cta i j sp ∧ dst = tm + 256 ∧ acc = decide (j ≠ 0 ∨ i ≠ 1) ∧
      mask = [0, 0, 0, 0] := by
  obtain ⟨db, dsc, hd, hdb, he⟩ := h
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := he
  exact ⟨⟨pvDesc_eq hd, hdb, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- **An MMA event is a QK or a PV MMA of the MMA warp.** A thread's MMA event `(g, k)` is issued
from a state `.w (.mma d P)` at a QK site `j` (the spec of `QkOp`, accumulator column
`d.tm + 128 (d.i % 2)`, accumulate flag `j ≠ 0`) or a PV site `j` (`PvOp`, column `d.tm + 256`,
accumulate flag `j ≠ 0 ∨ d.i ≠ 1`). -/
theorem mma_event_cases (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) :
    (∃ (d : Mma.D) (P : Loader.Pro) (j : Fin 8), St Q L X g k = some (some (.w (.mma d P))) ∧
      Mma.Inv d ∧ d.site = .qk j ∧ QkOp L (g / L.block) d.i j sp ∧
      dst = d.tm + 128 * (d.i % 2) ∧ acc = decide (j.val ≠ 0) ∧ mask = [0, 0, 0, 0]) ∨
    (∃ (d : Mma.D) (P : Loader.Pro) (j : Fin 8), St Q L X g k = some (some (.w (.mma d P))) ∧
      Mma.Inv d ∧ d.site = .pv j ∧ PvOp L (g / L.block) d.i j sp ∧ dst = d.tm + 256 ∧
      acc = decide (j.val ≠ 0 ∨ d.i ≠ 1) ∧ mask = [0, 0, 0, 0]) := by
  obtain ⟨d, P, hσ, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he
    (Or.inl ⟨dst, sp, acc, mask, rfl⟩)
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
  have hI : Mma.Inv d := hinv.2.1
  unfold EvW.MmShape at hsh
  cases hs : d.site with
  | qk j =>
    rw [hs] at hsh
    obtain ⟨hq, h1, h2, h3⟩ := qkOp_of_issue hsh
    exact .inl ⟨d, P, j, hσ, hI, hs, hq, h1, h2, h3⟩
  | pv j =>
    rw [hs] at hsh
    obtain ⟨hq, h1, h2, h3⟩ := pvOp_of_issue hsh
    exact .inr ⟨d, P, j, hσ, hI, hs, hq, h1, h2, h3⟩
  | _ =>
    rw [hs] at hsh
    simp at hsh

/-- **A QK MMA event at the state of step `j`.** The event of thread `g` at the state `d` of QK
step `j` has the spec of `QkOp`, accumulator column `d.tm + 128 (d.i % 2)`, accumulate flag
`j ≠ 0`, and the state satisfies the machine's invariant. -/
theorem qk_event (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) {j : Fin 8} (hs : d.site = .qk j) :
    QkOp L (g / L.block) d.i j sp ∧ dst = d.tm + 128 * (d.i % 2) ∧
      acc = decide (j.val ≠ 0) ∧ mask = [0, 0, 0, 0] ∧ Mma.Inv d := by
  rcases mma_event_cases hpre hX hf hg he with
    ⟨d', P', j', hσ', hI, hs', hq, h1, h2, h3⟩ | ⟨d', P', j', hσ', hI, hs', -⟩
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    have hjj : j = j' := by
      have := hs.symm.trans hs'
      simpa using this
    subst hjj
    exact ⟨hq, h1, h2, h3, hI⟩
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    rw [hs] at hs'
    exact absurd hs' (by simp)

/-- **A PV MMA event at the state of step `j`**: the spec of `PvOp`, accumulator column
`d.tm + 256`, accumulate flag `j ≠ 0 ∨ d.i ≠ 1`. -/
theorem pv_event (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool}
    {mask : List Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) {j : Fin 8} (hs : d.site = .pv j) :
    PvOp L (g / L.block) d.i j sp ∧ dst = d.tm + 256 ∧
      acc = decide (j.val ≠ 0 ∨ d.i ≠ 1) ∧ mask = [0, 0, 0, 0] ∧ Mma.Inv d := by
  rcases mma_event_cases hpre hX hf hg he with
    ⟨d', P', j', hσ', hI, hs', -⟩ | ⟨d', P', j', hσ', hI, hs', hq, h1, h2, h3⟩
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    rw [hs] at hs'
    exact absurd hs' (by simp)
  · have hdd : d = d' := by
      have := Option.some.inj (Option.some.inj (hσ.symm.trans hσ'))
      simp only [TSt.w.injEq, WComp.WSt.mma.injEq] at this
      exact this.1
    subst hdd
    have hjj : j = j' := by
      have := hs.symm.trans hs'
      simpa using this
    subst hjj
    exact ⟨hq, h1, h2, h3, hI⟩

/-- **A complete execution records the operands of every MMA it issues**: the MMA completed
(`AsyncDrained`), so it started (`Consistent`). -/
theorem mma_operands (hX : Consistent L kernel Assumptions.all mem0 X) (hcomp : Complete L X)
    {g k pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) :
    ∃ ops, X.async.mmaOperands (g, k) = some ops := by
  have hd : X.async.mmaDone (g, k) = true :=
    ((asyncDrained_iff X).mp hcomp.2.1).2.2.1 (g, k) (.inl ⟨dst, sp, acc, mask, pc, he⟩)
  have hst := hX.tma.2.1.2 (g, k) hd
  cases h : X.async.mmaOperands (g, k) with
  | none => simp [AsyncCopy.Snapshot.mmaStarted, h] at hst
  | some ops => exact ⟨ops, rfl⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Mma
