-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Producer.OffsetFrame
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.TensorStoreOrigin
public import Lemmas.TensorStore.StoreWrite

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX PTX.Flow

def MapsAboveOffsets (L : Launch) : Prop :=
  ∀ a outer (d : TensorDescriptor.Descriptor outer), L.tensorMaps a = some ⟨outer,d⟩ →
    65552 ≤ d.base

private theorem issue_base {A : List Assumption} {L : Launch} {g pc : Nat} {t : TState} {op : Op}
    {e : Event} {o : Option TState} (fire : Fires pc (eventTmpl A L g t op) e o)
    {a : Nat} {s : TensorStore.Spec} (kind : e.kind = .tensorStore a s)
    (maps : MapsAboveOffsets L) : 65552 ≤ s.descriptor.base := by
  have hop := fires_tensorStore_op fire kind
  cases op <;> simp only [tensorStoreOp,Bool.false_eq_true] at hop
  have ok := fires_cpTensorStore_ok fire kind
  obtain ⟨_,d,binding,_,transfer,_,_⟩ := tensorStoreSpec_ok ok
  have lower := maps _ _ _ binding
  rw [transfer]
  generalize (‹TensorMode›) = mode
  cases mode <;> exact lower

private theorem store_lower {s : TensorStore.Spec} {x y k : Nat} {l : Loc}
    (loc : TensorStore.writeLoc s x y k = some l) : s.descriptor.base ≤ l.addr := by
  obtain ⟨slot,_,dst⟩ := Option.bind_eq_some_iff.mp loc
  obtain ⟨addr,h,rfl⟩ := Option.map_eq_some_iff.mp dst
  unfold TensorBox.globalAddress TensorTransfer.globalAddress TensorAddress.lookup at h
  split at h
  · cases h
    change _ ≤ s.descriptor.base + _ + _
    omega
  · cases h

private theorem tensor_store_above {L : Launch} {X : Execution} {mem : Mem0}
    {base : Nat → Nat → Nat} (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (maps : MapsAboveOffsets L) {i : EvId} {x y k : Nat} {dst : Acc} {bs : List Byte}
    (wrote : X.MemWrites (.async i (.write (.store x y k))) dst bs)
    {l : Loc} (hit : dst.Covers l) : 65552 ≤ l.addr := by
  obtain ⟨obs,a,_,_,⟨pc,issue⟩,pos,_,one,_⟩ := wrote
  rcases get_source valid issue with ⟨_,h⟩ | ⟨t,ins,o,_,_,fire⟩
  · cases h
  · have lower := issue_base fire rfl maps
    rw [← Acc.loc_of_one hit one]
    exact lower.trans (store_lower pos)

private theorem tensor_load_shared {L : Launch} {X : Execution} {mem : Mem0}
    {base : Nat → Nat → Nat} (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    {i : EvId} {x y k : Nat} {dst : Acc} {bs : List Byte}
    (wrote : X.MemWrites (.async i (.write (.load x y k))) dst bs)
    {l : Loc} (hit : dst.Covers l) : l.space = .shared := by
  obtain ⟨obs,_,_,observed,_,pos,_,one,_⟩ := wrote
  have route := (valid.tensor i obs observed).2.2.1
  obtain ⟨slot,_,loc⟩ := Option.map_eq_some_iff.mp pos
  rw [← Acc.loc_of_one hit one,← loc]
  exact route.2.1

def TensorWriter : AsyncCopy.Ref → Prop
  | .async _ (.write (.store ..)) | .async _ (.write (.load ..)) => True
  | _ => False

theorem offset_writer_not_tensor {L : Launch} {X : Execution} {mem : Mem0}
    {base : Nat → Nat → Nat} (valid : Consistent L kernel (Prologue.assumptions base) mem X)
    (maps : MapsAboveOffsets L) {w : AsyncCopy.Ref} {dst : Acc} {data : List Byte}
    (wrote : X.MemWrites w dst data) {last : Bool} {k : Nat} (inside : k < 8)
    (hit : dst.Covers ((offsetAccess last).loc.at k)) : ¬TensorWriter w := by
  cases w with
  | thread => exact id
  | async i part =>
    cases part <;> try exact id
    case writeLoad =>
      have h := tensor_load_shared valid wrote hit
      cases h
    case writeStore =>
      have h := tensor_store_above valid maps wrote hit
      cases last <;> simp [offsetAccess,offsetLoc,Loc.at] at h <;> omega

end FlashKda.Packed.ProducerControl
