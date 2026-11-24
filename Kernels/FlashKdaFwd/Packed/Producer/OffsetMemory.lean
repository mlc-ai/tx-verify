-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.SequenceOffsets
public import Lemmas.Execution.InitialMemory
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Proof

def offsetLoc (k : Nat) : Loc := ⟨.global,0,65536+k⟩

def offsetAccess (last : Bool) : Acc := {loc := offsetLoc (if last then 8 else 0), size := 8}

def offsetValue (last : Bool) := b64 (if last then 1 else 0)

def OffsetMemory (mem : Mem0) : Prop :=
  ∀ last k, k < 8 → mem ((offsetAccess last).loc.at k) = some (some ((offsetValue last).byteAt k))

def OffsetWrite (X : Execution) : Prop :=
  ∃ w dst bs, X.MemWrites w dst bs ∧ ∃ k < 16, dst.Covers (offsetLoc k)

private def target (last : Bool) := if last then 2249 else 2248
def loadPc (last : Bool) := if last then 116 else 115
def ChangedOffsetRead (X : Execution) : Prop :=
  ∃ last i bs k w dst data, X.get (129,i) = some ⟨loadPc last,.rd (offsetAccess last) bs⟩ ∧
    k < 8 ∧ X.rf (.thread (129,i)) k = some w ∧ X.MemWrites w dst data ∧
    dst.Covers ((offsetAccess last).loc.at k) ∧
    bs[k]? ≠ some (some ((offsetValue last).byteAt k))

theorem changed_writes_input {X : Execution} (h : ChangedOffsetRead X) : OffsetWrite X := by
  obtain ⟨last,_,_,k,w,dst,bs,_,inside,_,writes,hit,_⟩ := h
  exact ⟨w,dst,bs,writes,(if last then 8 else 0)+k,by cases last <;> simp_all <;> omega,by
    simpa [offsetAccess,offsetLoc,Loc.at,Nat.add_assoc] using hit⟩

private def loadOp (last : Bool) : MemAccess :=
  {kind := .load, space := some .global, sem := .weak, elem := .int .b 64,
   addr := ⟨.reg 2264 64,if last then 8 else 0⟩, dsts := [some (target last)]}

set_option maxRecDepth 60000 in
private theorem loads : Transfers.slice 115 2 =
    some [⟨none,.mem (loadOp false)⟩,⟨none,.mem (loadOp true)⟩] := by kernel_rfl

private theorem offset_template (base : Nat → Nat → Nat) (L : Launch) (last : Bool) (t : TState)
    (pc : t.pc = loadPc last) (clear : t.fault = none) (scalar : t.sub = 0)
    (address : t.regs 2264 = some (b64 65536)) :
    out kernel (Prologue.assumptions base) L 129 t =
      .ev (.read (offsetAccess last) (afterLoad t [target last])) := by
  have site : kernel.code[t.pc]? = some ⟨none,.mem (loadOp last)⟩ := by
    rw [pc]
    cases last
    · exact fetch (pc := 115) (i := 0) (by decide) (by decide) loads
    · exact fetch (pc := 115) (i := 1) (by decide) (by decide) loads
  rw [out_event clear site (by rfl) (by cases last <;> rfl)]
  apply congrArg Out.ev
  cases last
  · exact loadTmpl_global scalar address (by decide) (by decide) (by decide)
  · change loadTmpl _ L 129 t .global false 64 [2249] 2264 8 = _
    unfold loadTmpl
    have addr : effAddr L 129 t .global 2264 8 = .ok (offsetLoc 8) := by
      simp [effAddr,readBits,readReg,address,b64,truncBits,offsetLoc,pure,Except.pure,
        bind,Except.bind]
    rw [addr]
    simp only [bind,Except.bind,List.length_singleton,scalar]
    rw [elemAcc_ok (by decide) (by decide)]
    rfl

private theorem value_bytes {base : Nat → Nat → Nat} {L : Launch} {mem : Mem0} {X : Execution}
    (consistent : Consistent L kernel (Prologue.assumptions base) mem X) (init : OffsetMemory mem)
    (faithful : ¬ ChangedOffsetRead X) (last : Bool) {i : Nat} {bs : List (Option Byte)}
    (read : X.get (129,i) = some ⟨loadPc last,.rd (offsetAccess last) bs⟩) :
    bs = (offsetValue last).toBytes.map some := by
  have actual : X.MemReads (.thread (129,i)) (offsetAccess last) bs := .inl ⟨_,read⟩
  have length : bs.length = 8 := (consistent.rf _ _ _ actual).1
  apply List.ext_getElem?
  intro k
  have bytes : (offsetValue last).bytes = 8 := by cases last <;> rfl
  by_cases inside : k < 8
  · have initial : bs[k]? = some (some ((offsetValue last).byteAt k)) := by
      by_contra diff
      cases source : X.rf (.thread (129,i)) k with
      | none =>
        exact diff (initial_read_byte consistent.rf actual inside source (init last k inside))
      | some w =>
        have h := (consistent.rf _ _ _ actual).2 k inside
        rw [source] at h
        obtain ⟨dst,data,writes,hit,_⟩ := h
        exact faithful ⟨last,i,bs,k,w,dst,data,read,inside,source,writes,hit,diff⟩
    simp [Value.toBytes,inside,bytes,initial]
  · have high : bs.length ≤ k := by omega
    rw [List.getElem?_eq_none high]
    simp [Value.toBytes,inside,bytes]

private def loadedOffset (t : TState) (last : Bool) :=
  { setReg t (target last) (offsetValue last) with pc := t.pc+1, sub := 0, acc := [] }

private theorem read_offset {base : Nat → Nat → Nat} {L : Launch} {mem : Mem0} {X : Execution}
    (consistent : Consistent L kernel (Prologue.assumptions base) mem X) (init : OffsetMemory mem)
    (faithful : ¬ ChangedOffsetRead X) (last : Bool) {t : TState} (pc : t.pc = loadPc last)
    (clear : t.fault = none) (scalar : t.sub = 0) (fresh : t.acc = [])
    (address : t.regs 2264 = some (b64 65536)) {e : Event} {es pre : List Event} {o : Option TState}
    (history : X.tr 129 = pre ++ e :: es)
    (trace : Run kernel (Prologue.assumptions base) L 129 t (e :: es) o) :
    e.kind ≠ .exit ∧ Run kernel (Prologue.assumptions base) L 129 (loadedOffset t last) es o := by
  have next : Next kernel (Prologue.assumptions base) L 129 t t
      (.read (offsetAccess last) (afterLoad t [target last])) :=
    ⟨.refl,offset_template base L last t pc clear scalar address⟩
  have returns : ¬ Fires t.pc (.read (offsetAccess last) (afterLoad t [target last])) e none := by
    rintro ⟨_,_,_,h⟩; cases h
  obtain ⟨u,⟨bs,_,event,result⟩,rest⟩ := next.continuing_event returns trace
  have read : X.get (129,pre.length) = some ⟨loadPc last,.rd (offsetAccess last) bs⟩ := by
    simp [Execution.get,history,event,pc]
  have val := value_bytes consistent init faithful last read
  have rebuilt : rebuild 3 bs = .ok (offsetValue last) := by
    rw [val]
    exact Proof.rebuild_scalar (by cases last <;> decide) (by cases last <;> rfl)
  have state : u = loadedOffset t last :=
    (Option.some.inj result).trans (afterLoad_ok scalar fresh rebuilt)
  exact ⟨by simp [event],state ▸ rest⟩

theorem no_exit_before_offset_reads (base : Nat → Nat → Nat) (L : Launch) (mem : Mem0)
    (X : Execution) (consistent : Consistent L kernel (Prologue.assumptions base) mem X)
    (first : X.Elect (129,0) 32 0xffffffff 0 1) (init : OffsetMemory mem)
    (faithful : ¬ ChangedOffsetRead X)
    (block : L.block = 192) (threads : L.ntid = ⟨192,1,1⟩) {t : TState} (pc : t.pc = 115)
    (clear : t.fault = none) (scalar : t.sub = 0) (fresh : t.acc = [])
    (address : t.regs 2264 = some (b64 65536)) (sequence : t.regs 309 = some (b32 0))
    (threadId : t.regs 307 = some (b32 129)) (elected : t.regs 88 = some (.pred false))
    {es pre : List Event} {o : Option TState} (history : X.tr 129 = pre ++ es)
    (trace : Run kernel (Prologue.assumptions base) L 129 t es o) {j : Nat} {e : Event}
    (atIndex : es[j]? = some e) : e.kind ≠ .exit := by
  cases es with
  | nil => simp at atIndex
  | cons a es =>
    obtain ⟨aKind,one⟩ := read_offset consistent init faithful false pc clear scalar fresh address
      history trace
    cases j with
    | zero => cases atIndex; exact aKind
    | succ j =>
      cases es with
      | nil => simp at atIndex
      | cons b rest =>
        have h1 : X.tr 129 = (pre ++ [a]) ++ b :: rest := by simpa using history
        obtain ⟨bKind,two⟩ := read_offset (t := loadedOffset t false) consistent init faithful true
          (by simp [loadedOffset,loadPc,pc]) clear rfl rfl
          (by simpa [loadedOffset,target,setReg] using address) h1 one
        cases j with
        | zero => cases atIndex; exact bKind
        | succ j =>
          have h2 : X.tr 129 = (pre ++ [a,b]) ++ rest := by simpa using history
          apply no_exit_after_offset_reads base L mem X consistent first block threads
            (t := loadedOffset (loadedOffset t false) true) _ clear _ _ _ _ _ h2 two atIndex
          all_goals simp_all [loadedOffset,target,offsetValue,b64,setReg]

end FlashKda.Packed.ProducerControl
