-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Safety.Tma
public import Kernels.FlashAttn4Fwd.Proof.Safety.TensorAlloc

@[expose] public section

/-! # `TensorUnsafe`: the tensor loads

Every tensor load is a loader lane's copy on a ring full barrier of its pair's even CTA
(`AsyncFacts.copy_ring`, `RingFacts.issue`), the copy `copySpec` of its earlier copies there
(`RingCopies.copy`). Then:

* **Every written byte has content** (ERR-TENSOR-FILL-VALUE, `no_tensorUnsafe`): the box is
  inside its map (`load_in_bounds`), so every slot's source is a global byte and the write copies
  the byte read (`write_byte`).
* **The mbarrier operand is initialized and published to the issue** (`load_initPublished`, a
  case of `MbarUninit`): the copy comes after the start, so the barrier is initialized
  (`InitsExist`), and the initialization is published to the events of its cluster after the
  start (`InitsPublished`).
* **The box starts aligned**: at head-dimension column 0 or 64 of f16 elements, a multiple of 16
  bytes (`copy_aligned`); the load's thread rule checks it. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX PTX.Proof PTX.Flow TensorDescriptor

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A box of an f16 map at column `64 x` starts 16-byte aligned. -/
theorem tile_aligned {d : Descriptor 3} (hf : d.format = .f16) (x : Nat) (y z w : Int) :
    BoxAligned d ![((64 * x : Nat) : Int), y, z, w] := by
  unfold BoxAligned
  simp only [hf, Format.bytes, Matrix.cons_val_zero]
  omega

/-- The ring barrier, copy and use of a tensor load. -/
theorem load_source (hX : Consistent L kernel asms mem0 X) (hr : RingFacts L X)
    (hcp : RingCopies P L X) (ha : AsyncFacts P L X) {g k pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) :
    ∃ b : FBar, b.isFull ∧ sp.mbar = b.loc L (pairBase L g) ∧
      sp = copySpec P L g b (((X.tr g).take k).countP (issuesTo (b.loc L (pairBase L g)))) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨b, c, hring, hm⟩ := ha.copy_ring he
  obtain ⟨hfull, rfl, -⟩ := hr.issue hg he hm hring
  exact ⟨b, hfull, hm, hcp.copy hg he hm hfull⟩

/-- Every byte a tensor load writes is a representable byte. -/
theorem write_byte (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hcp : RingCopies P L X) (ha : AsyncFacts P L X)
    (hco : CoordsInRange P L) {i : EvId} {o : TensorCopy.Observation} (hobs : X.tensor i = some o)
    {slot : TensorTransfer.Slot o.spec.descriptor} {content : TensorCopy.Content}
    (hw : o.effects.write slot = some content) : content.byte ≠ none := by
  obtain ⟨⟨address, pc, he⟩, hok, -, -⟩ := hX.tensor i o hobs
  have hin := load_in_bounds hpre hX hr hcp ha hco he
  have hga : o.spec.globalAddress slot ≠ none := by
    intro hn
    apply hin
    refine ⟨slot, fun hb => ?_⟩
    unfold TensorBox.globalAddress TensorTransfer.globalAddress TensorAddress.lookup at hn
    split at hn
    · cases hn
    · rename_i hne
      exact hne ⟨hb, by simp [geometry]⟩
  have hwr := hok.writes slot content hw
  unfold TensorCopy.source at hwr
  obtain ⟨addr, hs⟩ := Option.ne_none_iff_exists'.mp hga
  rw [hs] at hwr
  obtain ⟨byte, -, rfl⟩ := hwr
  simp [TensorCopy.Content.byte]

/-- **A tensor load's mbarrier is initialized, and the initialization is published to the
load.** -/
theorem load_initPublished (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hcp : RingCopies P L X) (ha : AsyncFacts P L X) (hc : ClusterFacts L X)
    (hex : InitsExist L X) (hpub : InitsPublished L X) {g k pc address : Nat}
    {s : TensorCopy.Spec} (he : X.get (g, k) = some ⟨pc, .tensorIssue address s⟩) :
    ∃ i count, X.MbInit i s.mbar count ∧ InitPublished L X i (g, k) s.mbar := by
  have hgr := hpre.grid
  obtain ⟨b, -, hm, -⟩ := load_source hX hr hcp ha he
  obtain ⟨⟨g0, a0⟩, pci, n, hi⟩ := hex b (cta := pairBase L g) he (by simp [PreKind])
    (by simp) (by rw [pairBase]; omega)
  refine ⟨_, _, ⟨pci, by rw [hm]; exact hi⟩, ?_⟩
  rw [hm]
  have hc0 : ctaOf L g0 = pairBase L g := by
    obtain ⟨b', hm', -⟩ := hc.init_site (Frame.lt_of_get hX hi) hi
    exact (FBar.loc_inj hm').2.symm
  exact hpub hi he (by simp [PreKind]) (by simp) (by
    rw [clusterOf_eq hpre, clusterOf_eq hpre, hc0, pairBase]
    omega)

/-- **No tensor load writes a byte without content.** -/
theorem no_tensorUnsafe (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hcp : RingCopies P L X) (ha : AsyncFacts P L X)
    (hco : CoordsInRange P L) : ¬ TensorUnsafe X := by
  rintro ⟨i, o, slot, content, hobs, hw, hbyte⟩
  exact write_byte hpre hX hr hcp ha hco hobs hw hbyte

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
