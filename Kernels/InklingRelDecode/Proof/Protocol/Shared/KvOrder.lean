-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvCopyRead
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvCover
import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvPreSame
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Readers
import Kernels.InklingRelDecode.Proof.Protocol.KV.Ready
import Kernels.InklingRelDecode.Proof.Protocol.KV.Lag
import Kernels.InklingRelDecode.Proof.Loader.Export.CopySame
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyDest
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyCount
import Kernels.InklingRelDecode.Proof.Lib.TensorSites
import Kernels.InklingRelDecode.Proof.Prologue.Export.CopyFoot
import Lemmas.Tensor.BoxInj
public import Lemmas.Protocol.RegionByte
import Lemmas.Protocol.SingleTmaRing.Ordered

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow PTX.Proof AsyncCopy Lib

/-- **A copy of a ring slot is a loader copy or a prologue preload**, with its use. -/
private theorem copy_class {Q L m X c g k pc a sp} {σ : Fin 3} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X)
    (hcg : c < L.grid) (ring : SingleTmaRing.Hyp L kernel Assumptions.all X
      ((KV.decl Q L X c).slot σ) .cta)
    (he : X.get (g,k) = some ⟨pc,.tensorIssue a sp⟩) (hm : sp.mbar = KV.Ring.ready.obj L c σ) :
    (g = KV.leader L X c 6 ∧ g%L.block/32 = 6 ∧ SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ)
      (g,k) = ((X.tr g).take k).countP (issuesTo sp.mbar)/8 + KV.preload Q L c σ) ∨
    (pc ∈ Iface.preloadSites ∧ 0 < KV.preload Q L c σ ∧
      SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (g,k) = 0) := by
  have hy := KV.leader_warp (X := X) hp hcg (by decide : 6 < 8)
  have issue := ring.issue he hm
  have inj := ring.pre_ne
  rcases Lib.tensor_issue_site hX he with pre | wk
  · have pre' : pc ∈ Iface.preloadSites := pre
    have range : 27 ≤ pc ∧ pc < 574 := by
      simp only [Iface.preloadSites,List.mem_cons,List.not_mem_nil,or_false] at pre'
      omega
    obtain ⟨σ',bar,-⟩ := Prologue.Export.preload_dest hp hX he pre
    obtain ⟨-,-,warp,-,-⟩ := rows.prologue.1.copy range.1 range.2 he bar
    rcases issue with ⟨rfl,-⟩ | ⟨hδ,i,eq⟩
    · have e6 : ((KV.decl Q L X c).slot σ).cp = KV.leader L X c 6 := rfl
      rw [e6] at warp
      exact absurd hy.2.2 (by omega)
    · refine .inr ⟨pre',by change KV.preload Q L c σ = 1 at hδ; omega,?_⟩
      unfold SingleTmaRing.copyUse
      split
      · rfl
      · rename_i h
        exact absurd ⟨hδ,i,eq⟩ h
  · have warp := Loader.Export.copy_warp hp hX hf he wk
    rcases issue with ⟨rfl,-⟩ | ⟨hδ,i,eq⟩
    · refine .inl ⟨rfl,warp,?_⟩
      unfold SingleTmaRing.copyUse
      split
      · rename_i h
        obtain ⟨hδ,i,eq⟩ := h
        exact absurd (by rw [← eq]) ((inj hδ).2 i)
      · rw [hm]; rfl
    · have hi : i.val < 8 := i.isLt
      have hw := (KV.leader_warp (X := X) hp hcg (by omega : i.val/4 < 8)).2.2
      have : g = KV.leader L X c (i.val/4) := congrArg Prod.fst eq
      subst this
      omega

/-- **Two tensor copies of one ring byte are the same write or ordered by their uses.** -/
theorem copies_use_order {Q L m X ref ref' a b l c₀} {σ₀ : Fin 3} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Mbar.InitRows L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (hw : X.Intent ref a true) (hw' : X.Intent ref' b true)
    (ha : a.Covers l) (hb : b.Covers l) (reg : InRing L l) (async : ∀ g k, ref ≠ .thread (g,k))
    (async' : ∀ g k, ref' ≠ .thread (g,k)) (hc₀ : l.cta = c₀)
    (hs₀ : Iface.InSlot L σ₀.val l.addr) :
    (copyUseOf X (ringSlot Q L X c₀ σ₀) ref < copyUseOf X (ringSlot Q L X c₀ σ₀) ref' ∧
      ByteCausality L X l ref ref') ∨
    ref = ref' ∨
    (copyUseOf X (ringSlot Q L X c₀ σ₀) ref' < copyUseOf X (ringSlot Q L X c₀ σ₀) ref ∧
      ByteCausality L X l ref' ref) := by
  obtain ⟨g1,k1,pc1,ad1,sp1,x1,y1,z1,σ,rfl,e1,bar1,cta1,slot1,byte1⟩ :=
    copy_write_facts hp hX hf hw ha async
  obtain ⟨g2,k2,pc2,ad2,sp2,x2,y2,z2,σ',rfl,e2,bar2,cta2,slot2,byte2⟩ :=
    copy_write_facts hp hX hf hw' hb async'
  have hσ : σ' = σ := Fin.ext (Iface.inSlot_unique σ'.isLt σ.isLt slot2 slot1)
  obtain rfl : σ = σ₀ := Fin.ext (Iface.inSlot_unique σ.isLt σ₀.isLt slot1 hs₀)
  have hg1 := Frame.lt_of_get hX e1
  have hg2 := Frame.lt_of_get hX e2
  obtain ⟨c,hc⟩ : ∃ c, g1/L.block = c := ⟨_,rfl⟩
  obtain rfl : c = c₀ := hc.symm.trans (cta1.symm.trans hc₀)
  have hc2 : g2/L.block = c := cta2.symm.trans (cta1.trans hc)
  have hcg : c < L.grid := hc ▸ Nat.div_lt_of_lt_mul (by
    simpa [Launch.threads,Nat.mul_comm] using hg1)
  rw [hc] at bar1
  rw [hc2,hσ] at bar2
  have ring := KV.ready_slot hp hX hf rows init hcg σ
  have fits := KV.slot_fits (Q := Q) (X := X) (L := L) (c := c) (s := σ)
  have hsc : SameCta L g1 g2 := ⟨hg1,hg2,hc.trans hc2.symm⟩
  have ca : AsyncCovers X (g1,k1) (.write (.load x1 y1 z1)) l := ⟨a,true,hw,ha⟩
  have cb : AsyncCovers X (g2,k2) (.write (.load x2 y2 z2)) l := ⟨b,true,hw',hb⟩
  have hsp : l.space = .shared := reg.1
  have hlc : l.cta = c := cta1.trans hc
  have cover := hcover hp hX hf words rows hu hsp hlc slot1
  have c1 := copy_class hp hX hf rows hcg ring e1 bar1
  have c2 := copy_class hp hX hf rows hcg ring e2 bar2
  rcases Nat.lt_trichotomy (SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (g1,k1))
    (SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (g2,k2)) with lt | eq | gt
  · exact .inl ⟨lt,.direct ⟨.inl hsc,SingleTmaRing.copies_chain hX ring fits e1 bar1 e2 bar2 lt
      ca cb (cover _)⟩⟩
  · have same : g1 = g2 ∧ k1 = k2 := by
      rcases c1 with ⟨rfl,w1,u1⟩ | ⟨s1,d1,u1⟩ <;> rcases c2 with ⟨h2,w2,u2⟩ | ⟨s2,d2,u2⟩
      · refine ⟨h2.symm,?_⟩
        subst h2
        have b1 : sp1.mbar = Iface.kvReadyLoc L (KV.leader L X c 6/L.block) σ := by
          rw [hc]; exact bar1
        have b2 : sp2.mbar = Iface.kvReadyLoc L (KV.leader L X c 6/L.block) σ := by
          rw [hc]; exact bar2
        exact Loader.Export.copy_same_use hp hX hf words w1 e1 e2 b1 b2 (by omega) byte1 byte2
      · omega
      · omega
      · exact preload_same_use hp hX hf rows e1 e2 s1 s2 (hc.trans hc2.symm) byte1 byte2
    obtain ⟨rfl,rfl⟩ := same
    obtain ⟨-,hk⟩ := Event.mk.inj (Option.some.inj (e1.symm.trans e2))
    obtain ⟨-,rfl⟩ := Kind.tensorIssue.inj hk
    obtain ⟨rfl,rfl,rfl⟩ := TensorCopy.writeLoc_inj byte1 byte2
    exact .inr (.inl rfl)
  · exact .inr (.inr ⟨gt,.direct ⟨.inl ⟨hg2,hg1,hc2.trans hc.symm⟩,SingleTmaRing.copies_chain hX
      ring fits e2 bar2 e1 bar1 gt cb ca (hcover hp hX hf words rows hu hsp hlc slot1 _)⟩⟩)

/-- **Two tensor copies of one ring byte are ordered.** -/
theorem copies_ordered {Q L m X ref ref' a b l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Mbar.InitRows L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (ne : ref ≠ ref') (hw : X.Intent ref a true) (hw' : X.Intent ref' b true)
    (ha : a.Covers l) (hb : b.Covers l) (reg : InRing L l) (async : ∀ g k, ref ≠ .thread (g,k))
    (async' : ∀ g k, ref' ≠ .thread (g,k)) :
    ByteCausality L X l ref ref' ∨ ByteCausality L X l ref' ref := by
  obtain ⟨g,k,pc,addr,sp,x,y,z,σ,-,-,-,hc,hs,-⟩ := copy_write_facts hp hX hf hw ha async
  rcases copies_use_order hp hX hf rows init words hu hw hw' ha hb reg async async' hc hs with
    h | h | h
  · exact .inl h.2
  · exact (ne h).elim
  · exact .inr h.2

/-- **The ring bytes are ordered**: a copy and a read by `copy_read_ordered`, two copies by
`copies_ordered`. -/
theorem kv_ordered {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) : ByteOrdered L X (Iface.InKv L) := by
  rintro e f a b l ⟨ne,we,wf,he,hfe,hw,-⟩ ha hb kv -
  have reg := InRing.of_kv kv
  cases we <;> cases wf
  · simp at hw
  · exact (copy_read_ordered hp hX hf rows init words hfe he hb ha reg
      (kv_async_write hp hX hfe hb kv) (kv_reader hp hX he ha kv.1 kv.2.1 kv.2.2)).symm
  · exact copy_read_ordered hp hX hf rows init words he hfe ha hb reg
      (kv_async_write hp hX he ha kv) (kv_reader hp hX hfe hb kv.1 kv.2.1 kv.2.2)
  · exact copies_ordered hp hX hf rows init words hu ne he hfe ha hb reg
      (kv_async_write hp hX he ha kv) (kv_async_write hp hX hfe hb kv)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
