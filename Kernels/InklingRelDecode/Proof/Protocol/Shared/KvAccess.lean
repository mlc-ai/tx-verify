-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Proof.Iface.Regions
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Readers
import Kernels.InklingRelDecode.Proof.Protocol.Shared.TileWriters
import Kernels.InklingRelDecode.Proof.Lib.TensorSites
import Kernels.InklingRelDecode.Proof.Loader.Export.CopyDest
import Kernels.InklingRelDecode.Proof.Prologue.Export.CopyFoot
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Lib.NoEvents

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow PTX.Proof PTX.Kernels.InklingRelDecode.Proof.Lib

/-- A one-byte access covering `l` is at `l`. -/
private theorem loc_eq {a : Acc} {l : Loc} (cov : a.Covers l) (size : a.size = 1) : l = a.loc := by
  obtain ⟨hs,hc,lo,hi⟩ := cov
  rw [size] at hi
  rcases l with ⟨s1,c1,a1⟩
  rcases hac : a.loc with ⟨s2,c2,a2⟩
  rw [hac] at hs hc lo hi
  simp only at hs hc lo hi ⊢
  simp only [Loc.mk.injEq]
  exact ⟨hs,hc,by omega⟩

/-- A byte of the K and V rings or of the base word at their start. -/
def InRing (L : Launch) (l : Loc) : Prop :=
  l.space=.shared ∧ L.sharedBase ≤ l.addr ∧ l.addr<L.sharedBase+196608

theorem InRing.of_kv {L l} (kv : Iface.InKv L l) : InRing L l :=
  ⟨kv.1,by have := kv.2.1; omega,kv.2.2⟩

theorem InRing.of_base {L l} (base : Iface.InBase L l) : InRing L l :=
  ⟨base.1,base.2.1,by have := base.2.2; omega⟩

/-- **An asynchronous write of a byte of the shared window is a tensor copy of a ring slot**:
the copy is on the ready barrier of the slot, in the byte's CTA, and the byte lies in that
slot's tiles. -/
theorem copy_write_facts {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (w : X.Intent ref a true) (cov : a.Covers l)
    (async : ∀ g k, ref ≠ .thread (g,k)) :
    ∃ g k pc addr sp x y z, ∃ σ : Fin 3, ref = .async (g,k) (.write (.load x y z)) ∧
      X.get (g,k) = some ⟨pc,.tensorIssue addr sp⟩ ∧
      sp.mbar = Iface.kvReadyLoc L (g/L.block) σ ∧ l.cta = g/L.block ∧
      Iface.InSlot L σ.val l.addr ∧ TensorCopy.writeLoc sp x y z = some l := by
  rcases Lib.write_intents hX w with ⟨⟨g,k⟩,pc,bs,rfl,get⟩|
    ⟨⟨g,k⟩,x,y,z,addr,sp,rfl,⟨pc,issue⟩,byte,size⟩
  · exact (async g k rfl).elim
  · have hl := loc_eq cov size
    rw [← hl] at byte
    rcases tensor_issue_site hX issue with pre|wk
    · obtain ⟨σ,bar,dest⟩ := Prologue.Export.preload_dest hp hX issue pre
      obtain ⟨cta,slot⟩ := dest byte
      exact ⟨g,k,pc,addr,sp,x,y,z,σ,rfl,issue,bar,cta,slot,byte⟩
    · obtain ⟨σ,bar,dest⟩ := Loader.Export.copy_dest hp hX hf issue wk
      obtain ⟨cta,slot,_⟩ := dest byte
      exact ⟨g,k,pc,addr,sp,x,y,z,σ,rfl,issue,bar,cta,slot,byte⟩

/-- No thread writes a ring byte, so a write of one is asynchronous. -/
theorem kv_async_write {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (w : X.Intent ref a true)
    (cov : a.Covers l) (kv : Iface.InKv L l) : ∀ g k, ref ≠ .thread (g,k) := by
  intro g k heq
  obtain ⟨space,lo,hi⟩ := kv
  rcases Lib.write_intents hX w with ⟨⟨g',k'⟩,pc,bs,rfl,get⟩|⟨_,_,_,_,_,_,rfl,_⟩
  · obtain ⟨hs,_,alo,ahi⟩ := cov
    exact kv_no_thread_write hp hX get (hs.symm.trans space) (b := l.addr-L.sharedBase)
      (by omega) (by omega) (by omega) (by omega)
  · cases heq

/-- **A write of a ring byte is a tensor copy of its slot.** -/
theorem kv_write_facts {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (w : X.Intent ref a true) (cov : a.Covers l) (kv : Iface.InKv L l) :
    ∃ g k pc addr sp x y z, ∃ σ : Fin 3, ref = .async (g,k) (.write (.load x y z)) ∧
      X.get (g,k) = some ⟨pc,.tensorIssue addr sp⟩ ∧
      sp.mbar = Iface.kvReadyLoc L (g/L.block) σ ∧ l.cta = g/L.block ∧
      Iface.InSlot L σ.val l.addr ∧ TensorCopy.writeLoc sp x y z = some l :=
  copy_write_facts hp hX hf w cov (kv_async_write hp hX w cov kv)

/-- **A read of a byte of the rings or the base word that is an MMA's is its B operand read**
in one slot of the issuer's CTA, the issuer a winning lane of warp seven, with the ready polls
and empty commits of the slot. -/
theorem ring_read_facts {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (r : X.Intent ref a false) (cov : a.Covers l) (ring : InRing L l)
    (mma : ∃ i b j, ref = .async i (.mmaRead b j)) :
    ∃ g k isB idx pc dst s acc mask, ∃ σ : Fin 3,
      ref = .async (g,k) (.mmaRead isB idx) ∧
      X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩ ∧ g%L.block/32 = 7 ∧
      Elected ((X.tr g).take k) (laneOf L g) ∧ l.cta = g/L.block ∧ Iface.InSlot L σ.val l.addr ∧
      ∃ T n, T ≤ n ∧ n < pollRound 2462 ((X.tr g).take k) ∧ n%3 = σ.val ∧
        ∀ j, j<k → ∀ sp, X.get (g,j) = some ⟨2546,.tc (.commit sp)⟩ →
          pollRound 2510 ((X.tr g).take j) ≤ T := by
  obtain ⟨space,lo,hi⟩ := ring
  obtain ⟨⟨g,k⟩,isB,idx,rfl⟩ := mma
  obtain ⟨_,size,foot⟩ := r
  rcases foot with ⟨dst,s,acc,mask,⟨pc,get⟩,byte⟩|⟨c,_,_,cp,_⟩
  · have hl := loc_eq cov size
    rw [← hl] at byte
    obtain ⟨warp,elected,σ,slot,credit⟩ := Mma.Export.read_slot hp hX hf words get
    obtain ⟨_,_,tile⟩ := Mma.Export.operands_all hp hX hf get
    cases isB
    · obtain ⟨_,_,range⟩ := tile .a idx l byte
      omega
    · obtain ⟨cta,inslot⟩ := slot idx l byte
      exact ⟨g,k,true,idx,pc,dst,s,acc,mask,σ,rfl,get,warp,elected,cta,inslot,credit⟩
  · exact (Lib.no_cp hX (g,k) c cp).elim

/-- **A read of a ring byte is an MMA's B operand read.** -/
theorem kv_read_facts {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (r : X.Intent ref a false) (cov : a.Covers l) (kv : Iface.InKv L l) :
    ∃ g k isB idx pc dst s acc mask, ∃ σ : Fin 3,
      ref = .async (g,k) (.mmaRead isB idx) ∧
      X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩ ∧ g%L.block/32 = 7 ∧
      Elected ((X.tr g).take k) (laneOf L g) ∧ l.cta = g/L.block ∧ Iface.InSlot L σ.val l.addr ∧
      ∃ T n, T ≤ n ∧ n < pollRound 2462 ((X.tr g).take k) ∧ n%3 = σ.val ∧
        ∀ j, j<k → ∀ sp, X.get (g,j) = some ⟨2546,.tc (.commit sp)⟩ →
          pollRound 2510 ((X.tr g).take j) ≤ T := by
  obtain ⟨space,lo,hi⟩ := kv
  exact ring_read_facts hp hX hf words r cov (.of_kv ⟨space,lo,hi⟩)
    (kv_reader hp hX r cov space lo hi)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
