-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.MmaSources
public import Lemmas.Tcgen05.TcMmaAReadUnique

@[expose] public section

/-! # Operands of a pending MMA whose A may be in Tensor Memory

A proof tool. To complete an MMA `i` that has not read its operands, choose for each byte of its
shared footprint a write covering it (`pick`), and for each byte of an A operand in Tensor Memory
a byte (`tm`). The operands record the chosen write's byte for a shared byte and `tm` otherwise
(`pickOperands`); the read sources are the chosen writes (`pickSource`).

* The reads satisfy RF (`pickOperands_rf`), and they are coherent when every other write of a
  shared byte is ordered before its chosen write or after the read (`pickOperands_hidden`), as for
  `newOperands`.
* An A operand in Tensor Memory has no shared byte (`byteLoc_a_tmem`), so its recorded bytes are
  those of `tm`. When `tm` is the byte of the source value of each A byte that has a source
  (`aSourceByte_exists`, by the uniqueness of `aReadSource_value_eq`), the recorded A bytes are
  the source bytes (`pickOperands_aRead`). -/

namespace PTX.MmaSources
open PTX AsyncCopy
noncomputable section

variable {X : Execution}

/-- The byte recorded for an operand byte: the chosen write's byte, or `tm` for an A byte with no
chosen write. -/
def pickByte (pick : Bool → Nat → Option (ByteSource X)) (tm : Nat → Option Byte) (isB : Bool)
    (k : Nat) : Option Byte :=
  match pick isB k with
  | some e => wbyte e.access e.bytes e.loc
  | none => if isB then none else tm k

/-- The recorded operands: `nA` bytes of A and `nB` bytes of B. -/
def pickOperands (nA nB : Nat) (pick : Bool → Nat → Option (ByteSource X))
    (tm : Nat → Option Byte) : MmaOperands :=
  ⟨List.ofFn (n := nA) fun k => pickByte pick tm false k.val,
   List.ofFn (n := nB) fun k => pickByte pick tm true k.val⟩

/-- The read source of an operand byte: the chosen write. -/
def pickSource (pick : Bool → Nat → Option (ByteSource X)) (isB : Bool) (k : Nat) :
    Option Ref :=
  (pick isB k).map ByteSource.ref

theorem pickOperands_lengths {nA nB : Nat} (pick : Bool → Nat → Option (ByteSource X))
    (tm : Nat → Option Byte) :
    (pickOperands nA nB pick tm).a.length = nA ∧ (pickOperands nA nB pick tm).b.length = nB :=
  ⟨List.length_ofFn, List.length_ofFn⟩

theorem pickOperands_value {nA nB : Nat} {pick : Bool → Nat → Option (ByteSource X)}
    {tm : Nat → Option Byte} {isB : Bool} {k : Nat} {b : Option Byte}
    (hv : mmaReadValue (pickOperands nA nB pick tm) isB k = some b) :
    b = pickByte pick tm isB k := by
  cases isB <;>
  · simp only [mmaReadValue, pickOperands, Bool.false_eq_true, ↓reduceIte,
      List.getElem?_ofFn] at hv
    split at hv
    · exact (Option.some.inj hv).symm
    · cases hv

theorem pickSource_read {pick : Bool → Nat → Option (ByteSource X)} {isB : Bool} {k : Nat}
    {e : ByteSource X} (he : pick isB k = some e) :
    mmaReadSource (pickSource pick false) (pickSource pick true) isB k = some e.ref := by
  cases isB <;> simp [mmaReadSource, pickSource, he]

/-- The chosen writes of an MMA's footprint: a chosen write exists for exactly the footprint
bytes, at the footprint location. -/
def PickFootprint (X : Execution) (i : EvId) (pick : Bool → Nat → Option (ByteSource X)) : Prop :=
  (∀ isB k loc, X.MmaFootprint i isB k loc → ∃ e, pick isB k = some e ∧ e.loc = loc) ∧
    ∀ isB k e, pick isB k = some e → X.MmaFootprint i isB k e.loc

/-- The new reads satisfy RF. -/
theorem pickOperands_rf {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {i : EvId}
    {nA nB : Nat} {pick : Bool → Nat → Option (ByteSource X)} {tm : Nat → Option Byte}
    (hX : Consistent L K A mem0 X)
    (hle : X.le (X.finishMma i (pickOperands nA nB pick tm) (pickSource pick false)
      (pickSource pick true)))
    (hp : PickFootprint X i pick) :
    RfWf mem0 (X.finishMma i (pickOperands nA nB pick tm) (pickSource pick false)
      (pickSource pick true)) := by
  refine finishMma_rf hX hle fun isB k loc b hf hv => ?_
  obtain ⟨e, he, hloc⟩ := hp.1 isB k loc hf
  subst hloc
  refine ⟨e.ref, e.access, e.bytes, pickSource_read he, e.write, e.cover, ?_⟩
  rw [pickOperands_value hv, pickByte, he]

/-- The new reads are coherent when every other write of a footprint byte is ordered before its
chosen write or after the read. -/
theorem pickOperands_hidden_of_byte_order {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {i : EvId} {nA nB : Nat} {pick : Bool → Nat → Option (ByteSource X)}
    {tm : Nat → Option Byte}
    (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    (hle : X.le (X.finishMma i (pickOperands nA nB pick tm) (pickSource pick false)
      (pickSource pick true)))
    (hn : X.async.mmaDone i = false) (hp : PickFootprint X i pick)
    (horder : ∀ isB k e, pick isB k = some e → ∀ w a bs, X.MemWrites w a bs →
      a.Covers e.loc → w = e.ref ∨ ByteCausality L X e.loc w e.ref ∨
        ByteCausality L X e.loc (.async i (.mmaRead isB k)) w) :
    Hidden L (X.finishMma i (pickOperands nA nB pick tm) (pickSource pick false)
      (pickSource pick true)) := by
  apply finishMma_hidden hX hle hn
  intro isB k loc hf w a bs hw hc hv
  obtain ⟨e, he, hloc⟩ := hp.1 isB k loc hf
  subst hloc
  rw [pickSource_read he]
  rcases horder isB k e he w a bs hw hc with heq | hb | ha
  · subst w
    intro hs
    exact ByteCausality.acyclic hX.effectValidity hX.object
      (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk _ _ (.single hs)
  · intro hs
    exact ByteCausality.acyclic hX.effectValidity hX.object
      (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk _ _
      ((Relation.TransGen.single hb).tail hs)
  · cases ha with
    | direct ha =>
      exact (uncompleted_mma_no_visibility hX.tcCommit hn (p := .mmaRead isB k)
        True.intro ha).elim
    | commitOperand _ hWritten =>
      obtain ⟨_, hIntent, _⟩ := hWritten
      cases hIntent.1

/-- Base-model ordering is sufficient for operand coherence. -/
theorem pickOperands_hidden {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {i : EvId} {nA nB : Nat} {pick : Bool → Nat → Option (ByteSource X)}
    {tm : Nat → Option Byte}
    (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    (hle : X.le (X.finishMma i (pickOperands nA nB pick tm) (pickSource pick false)
      (pickSource pick true)))
    (hn : X.async.mmaDone i = false) (hp : PickFootprint X i pick)
    (horder : ∀ isB k e, pick isB k = some e → ∀ w a bs, X.MemWrites w a bs →
      a.Covers e.loc → w = e.ref ∨ modelCausality L X e.loc w e.ref ∨
        modelCausality L X e.loc (.async i (.mmaRead isB k)) w) :
    Hidden L (X.finishMma i (pickOperands nA nB pick tm) (pickSource pick false)
      (pickSource pick true)) :=
  pickOperands_hidden_of_byte_order hX hg hle hn hp fun isB k e he w a bs hw hc =>
    (horder isB k e he w a bs hw hc).imp_right (Or.imp ByteCausality.direct ByteCausality.direct)

/-- For each A byte of an MMA there is a byte equal to the corresponding byte of every source
value of it, when each MMA's output layout is injective. -/
theorem aSourceByte_exists {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X) (hinj : TcMma.LayoutInjective X)
    (i : EvId) (index : Nat) :
    ∃ b : Option Byte, ∀ source cell pos value,
      (∃ d s acc mask, X.MmaIssue i d s acc mask ∧ TcMma.aCell s index = some (cell, pos)) →
      TcMma.ReadSource L X .a source i cell → TcMma.Wrote L A X source cell value →
      pos < value.bytes → b = some (value.byteAt pos) := by
  by_cases h : ∃ source cell pos value,
      (∃ d s acc mask, X.MmaIssue i d s acc mask ∧ TcMma.aCell s index = some (cell, pos)) ∧
      TcMma.ReadSource L X .a source i cell ∧ TcMma.Wrote L A X source cell value
  · obtain ⟨source, cell, pos, value, ha, hs, hw⟩ := h
    refine ⟨some (value.byteAt pos), fun source' cell' pos' value' ha' hs' hw' _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := TcMma.aReadSource_value_eq hX hg hinj ha ha' hs hw hs' hw'
    rfl
  · exact ⟨none, fun source cell pos value ha hs hw =>
      (h ⟨source, cell, pos, value, ha, hs, hw⟩).elim⟩

/-- **The recorded A bytes are the source bytes**, when `tm` gives the source byte of each A byte
with a source. -/
theorem pickOperands_aRead {L : Launch} {A : List Assumption} {i : EvId} {d : Nat}
    {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} (hi : X.MmaIssue i d s acc mask)
    {nB : Nat} {pick : Bool → Nat → Option (ByteSource X)} {tm : Nat → Option Byte}
    (hp : PickFootprint X i pick)
    (htm : ∀ index source cell pos value,
      (∃ d s acc mask, X.MmaIssue i d s acc mask ∧ TcMma.aCell s index = some (cell, pos)) →
      TcMma.ReadSource L X .a source i cell → TcMma.Wrote L A X source cell value →
      pos < value.bytes → tm index = some (value.byteAt pos))
    {index : Nat} {cell : TcMma.Cell} {pos : Nat} {source : EvId} {value : Value}
    (ha : ∃ d s acc mask, X.MmaIssue i d s acc mask ∧ TcMma.aCell s index = some (cell, pos))
    (hs : TcMma.ReadSource L X .a source i cell) (hw : TcMma.Wrote L A X source cell value)
    (hpos : pos < value.bytes) :
    (pickOperands (TcMma.Operand.a.bytes s.descriptor) nB pick tm).a[index]? =
      some (some (value.byteAt pos)) := by
  obtain ⟨d', s', acc', mask', hi', hc⟩ := id ha
  obtain ⟨-, rfl, -, -⟩ := TcMma.mmaIssue_params hi hi'
  have hlt := TcMma.aCell_index_lt hc
  have htmem : s.aTmem.isSome = true := by
    cases ha : s.aTmem with
    | none => simp [TcMma.aCell, ha] at hc
    | some _ => rfl
  have hnone : pick false index = none := by
    cases he : pick false index with
    | none => rfl
    | some e =>
      exfalso
      rcases hp.2 false index e he with ⟨d2, s2, a2, m2, hi2, hl⟩ | ⟨a, src, cta, ⟨pc, hcp⟩, -⟩
      · obtain ⟨-, rfl, -, -⟩ := TcMma.mmaIssue_params hi hi2
        simp only [Bool.false_eq_true, ↓reduceIte, TcMma.byteLoc_a_tmem htmem] at hl
        cases hl
      · obtain ⟨pc', hp'⟩ := hi
        rw [hp'] at hcp
        cases hcp
  simp only [pickOperands, List.getElem?_ofFn, hlt, ↓reduceDIte, pickByte, hnone,
    Bool.false_eq_true, ↓reduceIte, htm index source cell pos value ha hs hw hpos]

end
end PTX.MmaSources
