-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvAccess
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
public import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
public import Kernels.InklingRelDecode.Proof.Lib.KvUse
public import Lemmas.Protocol.SingleTmaRing.Order
import Kernels.InklingRelDecode.Proof.Protocol.KV.Lag
import Kernels.InklingRelDecode.Proof.Protocol.KV.CommitBudget
import Lemmas.Protocol.SingleTmaRing.Ordered

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow Lib

/-- Ring slot `σ` of CTA `c`. -/
noncomputable abbrev ringSlot (Q : Params) (L : Launch) (X : Execution) (c : Nat) (σ : Fin 3) :
    SingleTmaRing.Slot := (KV.decl Q L X c).slot σ

/-- **A tensor copy and an MMA operand read of one ring byte are ordered**: the copy is before
the read when its use of the slot is at most the read's (the MMA lane's ready poll observes the
copy's completion), the read before the copy when its use is below (the loader's empty poll
observes the commit that completes the read). -/
theorem copy_read_side {Q L m X ref ref' a b l c₀} {σ₀ : Fin 3} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Mbar.InitRows L X) (words : RoleBytes L X)
    (hw : X.Intent ref a true) (hr : X.Intent ref' b false) (ha : a.Covers l)
    (hb : b.Covers l) (ring : InRing L l) (async : ∀ g k, ref ≠ .thread (g,k))
    (mma : ∃ i b j, ref' = .async i (.mmaRead b j)) (hc₀ : l.cta = c₀)
    (hs₀ : Iface.InSlot L σ₀.val l.addr) :
    (copyUseOf X (ringSlot Q L X c₀ σ₀) ref ≤ readUseOf X (ringSlot Q L X c₀ σ₀) ref' ∧
      ByteCausality L X l ref ref') ∨
    (readUseOf X (ringSlot Q L X c₀ σ₀) ref' < copyUseOf X (ringSlot Q L X c₀ σ₀) ref ∧
      ByteCausality L X l ref' ref) := by
  obtain ⟨gl,kl,pcl,addr,sp,x,y,z,σ,rfl,hcopy,hbar,lcta,lslot,_⟩ :=
    copy_write_facts hp hX hf hw ha async
  obtain ⟨g,k,isB,idx,pc,dst,s,acc,mask,σ',rfl,hread,warp,elected,rcta,rslot,T,n,le,lt,slot,
    bound⟩ := ring_read_facts hp hX hf words hr hb ring mma
  obtain rfl : σ = σ' := Fin.ext (Iface.inSlot_unique σ.isLt σ'.isLt lslot rslot)
  obtain rfl : σ = σ₀ := Fin.ext (Iface.inSlot_unique σ.isLt σ₀.isLt lslot hs₀)
  have hg := Frame.lt_of_get hX hread
  have hgl := Frame.lt_of_get hX hcopy
  obtain ⟨c,hc⟩ : ∃ c, g/L.block = c := ⟨_,rfl⟩
  have hcg : c<L.grid := hc ▸ Nat.div_lt_of_lt_mul (by
    simpa [Launch.threads,Nat.mul_comm] using hg)
  obtain rfl : c = c₀ := hc.symm.trans (rcta.symm.trans hc₀)
  have heq : Protocol.KV.leader L X c 7 = g := by
    obtain ⟨ev,hev,rest⟩ := elected
    have := Protocol.KV.leader_eq hX hg ⟨ev,(List.take_sublist k _).subset hev,rest⟩
    rwa [warp,hc] at this
  have hlc : gl/L.block = c := lcta.symm.trans (rcta.trans hc)
  have credit := Protocol.KV.read_credit hp hX hf words rows hg warp hc bound le lt slot
    (s := σ)
  subst heq
  rw [hlc] at hbar
  have ring := Protocol.KV.ready_slot hp hX hf rows init hcg σ
  have fits := Protocol.KV.slot_fits (Q := Q) (X := X) (L := L) (c := c) (s := σ)
  have hsame : SameCta L gl (Protocol.KV.leader L X c 7) :=
    ⟨hgl,hg,by rw [hlc,hc]⟩
  have hR : X.TcAsync (Protocol.KV.leader L X c 7,k) := .inl ⟨dst,s,acc,mask,pc,hread⟩
  have ordered := SingleTmaRing.copy_read_order hX fits ring hR credit hcopy hbar
    ⟨a,true,hw,ha⟩ ⟨b,false,hr,hb⟩
  rcases Nat.lt_or_ge (SingleTmaRing.readUse X ((Protocol.KV.decl Q L X c).slot σ)
    (Protocol.KV.leader L X c 7,k)) (SingleTmaRing.copyUse X ((Protocol.KV.decl Q L X c).slot σ)
    (gl,kl)) with h|h
  · exact .inr ⟨h,.direct ⟨.inl ⟨hsame.2.1,hsame.1,hsame.2.2.symm⟩,.direct (ordered.2 h)⟩⟩
  · exact .inl ⟨h,.direct ⟨.inl hsame,.direct (ordered.1 h)⟩⟩

/-- **A tensor copy and an MMA operand read of one ring byte are ordered.** -/
theorem copy_read_ordered {Q L m X ref ref' a b l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (init : Mbar.InitRows L X) (words : RoleBytes L X)
    (hw : X.Intent ref a true) (hr : X.Intent ref' b false) (ha : a.Covers l)
    (hb : b.Covers l) (ring : InRing L l) (async : ∀ g k, ref ≠ .thread (g,k))
    (mma : ∃ i b j, ref' = .async i (.mmaRead b j)) :
    ByteCausality L X l ref ref' ∨ ByteCausality L X l ref' ref := by
  obtain ⟨g,k,pc,addr,sp,x,y,z,σ,-,-,-,hc,hs,-⟩ :=
    copy_write_facts hp hX hf hw ha async
  exact (copy_read_side hp hX hf rows init words hw hr ha hb ring async mma hc hs).imp
    (·.2) (·.2)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
