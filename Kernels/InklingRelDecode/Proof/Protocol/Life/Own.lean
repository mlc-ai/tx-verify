-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Mbar
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Protocol.Alloc.Access
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Lib.CopyCta
import Kernels.InklingRelDecode.Proof.Lib.WriteCta
import Kernels.InklingRelDecode.Proof.Lib.ReadKinds
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Lemmas.Flow.NotTensor
import Lemmas.Flow.NotBulk
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Readers

@[expose] public section

/-! # Every use of a CTA's shared memory is of the issuer's CTA

The uses of shared memory are the mbarrier events of a lane (`mbar_use`), its shared accesses
(`Lib.read_intents`, `Lib.write_intents`), the copies of a tensor load, and the operand reads of an
MMA, each in the CTA of the issuing lane. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
open PTX PTX.Flow MbarRow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A named mbarrier is of the naming lane's CTA.** -/
theorem mbar_own {g k e l} (rows : MbarRows Q L X) (hg : g < L.threads)
    (he : X.get (g,k) = some e) (hm : Frame.MbarOf e l) : l.cta = g / L.block := by
  have key : ∀ {n}, l = loc L g n → l.cta = g / L.block := fun h => by rw [h]; rfl
  cases mbar_use rows hg he hm with
  | startup _ h | dispatch _ h => cases h
  | prologue _ h =>
    cases h with
    | init _ _ addr => exact key addr
    | preloadArrive _ _ addr _ | preloadCopy _ _ addr _ => exact key addr
  | softmax _ h => cases h <;> exact key ‹_›
  | epilogue _ h => cases h; exact key ‹_›
  | loader _ h => cases h <;> exact key ‹_›
  | mma _ h => cases h <;> exact key ‹_›

/-- **A tensor load's destination is in its issuer's CTA.** -/
theorem tensor_base (hX : Consistent L kernel Assumptions.all m X) {g k pc a s}
    (he : X.get (g,k) = some ⟨pc,.tensorIssue a s⟩) : s.sharedBase.cta = g / L.block := by
  obtain ⟨_,bad⟩ | ⟨t,ins,o,_,code,fire⟩ := get_source hX he
  · cases bad
  have hop : tensorOp ins.op = true := by
    cases hq : tensorOp ins.op
    · exact absurd rfl (fires_notTensor (eventTmpl_notTensor hq) fire a s)
    · rfl
  have hl : Lib.localCopyOp ins.op = true := by
    by_contra hn
    have : (tensorOp ins.op && !Lib.localCopyOp ins.op) = true := by
      simp [hop, Bool.eq_false_iff.mpr hn]
    exact absurd (OpPcsFast.mem Lib.kernel_copy_local code this) (by simp)
  exact Lib.fires_copy_base hl fire rfl

/-- **A shared access of a lane or of one of its asynchronous stages is of the lane's CTA.** -/
theorem intent_own (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {ref} {a w} (hint : X.Intent ref a w)
    (hsp : a.loc.space = .shared) : a.loc.cta = ref.issuer.1 / L.block := by
  cases w
  · rcases Lib.read_intents hX hint with ⟨⟨g,k⟩,pc,bs,rfl,get⟩ | ⟨⟨g,k⟩,isB,j,rfl,foot⟩ |
      ⟨i,x,y,z,addr,sp,rfl,-,loc,-⟩
    · exact (Protocol.Alloc.read_box hp hX get (Shared.shared_read_site hX get hsp)).2.1
    · rcases foot with ⟨dst,s,acc,mask,⟨pc,get⟩,byte⟩ | ⟨c,_,_,cp,_⟩
      · obtain ⟨-,-,tile⟩ := Mma.Export.operands_all hp hX hf get
        cases isB
        · exact (tile .a j _ byte).2.1
        · exact (tile .b j _ byte).2.1
      · exact (Lib.no_cp hX (g,k) c cp).elim
    · exact absurd hsp (by rw [Protocol.Alloc.tensor_read_space loc]; nofun)
  · rcases Lib.write_intents hX hint with ⟨⟨g,k⟩,pc,bs,rfl,get⟩ |
      ⟨⟨g,k⟩,x,y,z,addr,sp,rfl,⟨pc,issue⟩,byte,-⟩
    · obtain ⟨_,bad⟩ | ⟨_,_,_,_,code,fire⟩ := get_source hX get
      · cases bad
      exact Lib.code_write_cta code fire hsp
    · simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at byte
      obtain ⟨slot,-,hl⟩ := byte
      rw [← hl]
      exact tensor_base hX issue

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
