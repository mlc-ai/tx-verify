-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleOrdinal
public import Kernels.InklingRelDecode.Proof.Softmax.Export.DecisionFour

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow Softmax.Export

/-- The quad's scratch reads of one lane are at the barrier-zero ordinal of its decision. -/
private theorem quad_reads {Q L m X x k a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (x,k)=some ⟨2255,.shfl .bfly a b c recv ok⟩) (lx : x%L.block<128)
    (earlier : ∀ h, h/L.block=x/L.block → h%L.block<128 → ∀ n<barOrdinal X x k - 1,
      ordEv X (Execution.isBarId 0) rescaleBar h n=ordEv X (Execution.isBarId 0) rescaleBar x n) :
    ∃ bsOf : Nat → List (Option Byte),
      (∀ i<4, ∃ q jq ac, q/L.block=x/L.block ∧ q%L.block%4=i ∧ q%L.block<128 ∧
        X.get (q,jq)=some ⟨2252,.rd ac (bsOf i)⟩ ∧ barOrdinal X q jq=barOrdinal X x k) ∧
      Lib.rescaleSkip L a recv=Lib.rescaleSkip L
        (Lib.minWord (Lib.loadWord (bsOf 0)) (Lib.loadWord (bsOf 2)))
        (Lib.minWord (Lib.loadWord (bsOf 1)) (Lib.loadWord (bsOf 3))) := by
  have hb : L.block=256 := hp.block
  obtain ⟨j,u,ac,bs,rfl,rd,hu,sync,o1,o2⟩ := decision_sync hp hX get
  obtain ⟨bsOf,reads,skip⟩ := decision_four hp hX hf get lx
  refine ⟨bsOf,fun i hi => ?_,skip⟩
  obtain ⟨jq,acq,get',count⟩ := reads i hi
  have lq : (x-x%4+i)%L.block<128 := by rw [hb] at lx ⊢; omega
  have ord := read_ordinal hp hX hf rd hu sync (by
      intro h ch lh n lt
      exact earlier h ch lh n (by omega)) lx lq (by rw [hb]; omega) get'
    (by rw [count]; simp)
  exact ⟨x-x%4+i,jq,acq,by rw [hb]; omega,by rw [hb] at lx ⊢; omega,lq,get',by omega⟩

/-- Two data lanes of a CTA at second decision shuffles of one barrier ordinal take the same
decision, provided the rescale visits below that ordinal agree. -/
theorem decision_agree_by {Q L m X x y kx ky ax bx cx rx okx ay by' cy ry oky}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (agree : ∀ n<barOrdinal X x kx, StoreAgree L X n)
    (gx : X.get (x,kx)=some ⟨2255,.shfl .bfly ax bx cx rx okx⟩)
    (gy : X.get (y,ky)=some ⟨2255,.shfl .bfly ay by' cy ry oky⟩)
    (lx : x%L.block<128) (ly : y%L.block<128) (cta : y/L.block=x/L.block)
    (ord : barOrdinal X y ky=barOrdinal X x kx)
    (earlierX : ∀ h, h/L.block=x/L.block → h%L.block<128 → ∀ n<barOrdinal X x kx - 1,
      ordEv X (Execution.isBarId 0) rescaleBar h n=ordEv X (Execution.isBarId 0) rescaleBar x n)
    (earlierY : ∀ h, h/L.block=y/L.block → h%L.block<128 → ∀ n<barOrdinal X y ky - 1,
      ordEv X (Execution.isBarId 0) rescaleBar h n=ordEv X (Execution.isBarId 0) rescaleBar y n) :
    Lib.rescaleSkip L ax rx=Lib.rescaleSkip L ay ry := by
  obtain ⟨bsX,readsX,skipX⟩ := quad_reads hp hX hf gx lx earlierX
  obtain ⟨bsY,readsY,skipY⟩ := quad_reads hp hX hf gy ly earlierY
  obtain ⟨j,u,ac,bs,rfl,rd,hu,sync,o1,o2⟩ := decision_sync hp hX gx
  have pub := scratch_next_publication hp hX hf (j:=u) (by rw [hu]; exact rd) (by
    intro h ch lh n lt
    exact earlierX h ch lh n (by omega))
  have same (i : Nat) (hi : i<4) : bsX i=bsY i := by
    obtain ⟨q,jq,acq,ctq,sq,lq,getq,ordq⟩ := readsX i hi
    obtain ⟨q',jq',acq',ctq',sq',lq',getq',ordq'⟩ := readsY i hi
    have pub' : PublishesAt L X (q/L.block) (barOrdinal X x u) := by rw [ctq]; exact pub
    exact scratch_reads_agree hp hX (agree _ (by omega)) getq getq'
      (ctq.trans (cta.symm.trans ctq'.symm)) (sq.trans sq'.symm) (by omega) (by omega) pub'
  rw [skipX,skipY,same 0 (by omega),same 1 (by omega),same 2 (by omega),same 3 (by omega)]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
