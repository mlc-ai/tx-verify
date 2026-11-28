-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Spec
import Kernels.InklingRelDecode.Proof.Lib.RoleWord
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Lib.SharedStores
import Kernels.InklingRelDecode.Proof.Prologue.Export.Publish
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryStore
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Startup.Export.AllocWrite

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow PTX.Proof

private theorem site_cases {L m X g k pc a bs} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.wr a bs⟩) (space : a.loc.space=.shared) :
    pc=11 ∨ (∃ i : Fin 8, pc=526+6*i.val) ∨ pc=570 ∨ pc=571 ∨ pc=2250 ∨ pc=2848 := by
  have hit := Lib.shared_write_site hX he space
  revert hit
  unfold Lib.sharedStores
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  rintro (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
  all_goals decide

/-- **Every thread write of the shared window is at one of six sites**, each in its own
region: the base word (the allocation store), the query tile, the count pair and scratch words,
the dispatch word. The byte `x` is a byte of the write in absolute address. -/
theorem writer_at {Q L m X g k pc a bs x} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.wr a bs⟩)
    (space : a.loc.space=.shared) (lo : a.loc.addr ≤ x) (hi : x < a.loc.addr+a.size) :
    L.sharedBase ≤ x ∧ ((x-L.sharedBase < 4 ∧ pc = 11) ∨
      (196608 ≤ x-L.sharedBase ∧ x-L.sharedBase < 212992 ∧ ∃ i : Fin 8, pc=526+6*i.val) ∨
      (212992 ≤ x-L.sharedBase ∧ x-L.sharedBase < 213008 ∧ (pc=571 ∨ pc=2250)) ∨
      (213336 ≤ x-L.sharedBase ∧ x-L.sharedBase < 213340 ∧ (pc=570 ∨ pc=2848))) := by
  rcases site_cases hX he space with rfl|⟨i,rfl⟩|rfl|rfl|rfl|rfl
  · obtain ⟨loc,size⟩ := Startup.Export.alloc_write hp hX he
    rw [loc] at lo
    rw [loc,size] at hi
    dsimp only at hi lo
    exact ⟨by omega,.inl ⟨by omega,rfl⟩⟩
  · obtain ⟨_,_,lowest,end'⟩ := Prologue.Export.query_store hp hX i he
    exact ⟨by omega,.inr (.inl ⟨by omega,by omega,i,rfl⟩)⟩
  · obtain ⟨acc,_⟩ := Lib.role_word hp hX he (.inl ⟨rfl,rfl⟩)
    rw [acc] at lo hi
    change L.sharedBase+213336 ≤ _ at lo
    change _ < L.sharedBase+213336+4 at hi
    exact ⟨by omega,.inr (.inr (.inr ⟨by omega,by omega,.inl rfl⟩))⟩
  · obtain ⟨j,_,size,loc,_⟩ := Prologue.Export.pair_bytes hp hX he
    rw [loc] at lo
    rw [loc,size] at hi
    dsimp only at hi lo
    have := j.isLt
    exact ⟨by omega,.inr (.inr (.inl ⟨by omega,by omega,.inl rfl⟩))⟩
  · obtain ⟨loc,size⟩ := Softmax.Export.scratch_store hp hX he
    rw [loc] at lo
    rw [loc,size] at hi
    dsimp only at hi lo
    have := Nat.mod_lt (g%L.block/32) (by omega : 0<4)
    exact ⟨by omega,.inr (.inr (.inl ⟨by omega,by omega,.inr rfl⟩))⟩
  · obtain ⟨acc,_⟩ := Lib.role_word hp hX he (.inr ⟨rfl,rfl⟩)
    rw [acc] at lo hi
    change L.sharedBase+213336 ≤ _ at lo
    change _ < L.sharedBase+213336+4 at hi
    exact ⟨by omega,.inr (.inr (.inr ⟨by omega,by omega,.inr rfl⟩))⟩

theorem writer_region {Q L m X g k pc a bs b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.wr a bs⟩)
    (space : a.loc.space=.shared) (lo : a.loc.addr ≤ L.sharedBase+b)
    (hi : L.sharedBase+b < a.loc.addr+a.size) :
    (b < 4 ∧ pc = 11) ∨ (196608 ≤ b ∧ b < 212992 ∧ ∃ i : Fin 8, pc=526+6*i.val) ∨
      (212992 ≤ b ∧ b < 213008 ∧ (pc=571 ∨ pc=2250)) ∨
      (213008 ≤ b ∧ b < 213340 ∧ (pc=570 ∨ pc=2848)) := by
  obtain ⟨_,h⟩ := writer_at hp hX he space lo hi
  have e : L.sharedBase+b-L.sharedBase=b := by omega
  rw [e] at h
  rcases h with h|h|h|⟨h1,h2,h3⟩
  exacts [.inl h,.inr (.inl h),.inr (.inr (.inl h)),.inr (.inr (.inr ⟨by omega,h2,h3⟩))]

/-- Thread writes covering a byte of either publication are exhausted by four sites.
The count pair has a later scratch writer, whereas the dispatch word is republished
by the epilogue. Half-open ranges include every byte of a vector element. -/
theorem publication_writers {Q L m X g k pc a bs b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.wr a bs⟩)
    (space : a.loc.space=.shared) (lo : a.loc.addr ≤ L.sharedBase+b)
    (hi : L.sharedBase+b < a.loc.addr+a.size) :
    (212992 ≤ b → b < 213008 → pc=571 ∨ pc=2250) ∧
    (213008 ≤ b → b < 213340 → pc=570 ∨ pc=2848) := by
  rcases writer_region hp hX he space lo hi with ⟨_,_⟩|⟨_,_,_⟩|⟨_,_,h⟩|⟨_,_,h⟩
  all_goals exact ⟨fun _ _ => by omega,fun _ _ => by omega⟩

/-- Thread writes covering a byte of the query tile are query stores. -/
theorem query_writers {Q L m X g k pc a bs b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.wr a bs⟩)
    (space : a.loc.space=.shared) (lo : a.loc.addr ≤ L.sharedBase+b)
    (hi : L.sharedBase+b < a.loc.addr+a.size) (low : 196608 ≤ b) (high : b < 212992) :
    ∃ i : Fin 8, pc=526+6*i.val := by
  rcases writer_region hp hX he space lo hi with ⟨_,_⟩|⟨_,_,h⟩|⟨_,_,_⟩|⟨_,_,_⟩
  all_goals omega

/-- No thread writes a byte of the K and V rings. -/
theorem kv_no_thread_write {Q L m X g k pc a bs b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.wr a bs⟩)
    (space : a.loc.space=.shared) (lo : a.loc.addr ≤ L.sharedBase+b)
    (hi : L.sharedBase+b < a.loc.addr+a.size) (low : 4 ≤ b) (high : b < 196608) : False := by
  rcases writer_region hp hX he space lo hi with ⟨_,_⟩|⟨_,_,_⟩|⟨_,_,_⟩|⟨_,_,_⟩
  all_goals omega

/-- **A write of a base word byte is the allocation's store or asynchronous.** -/
theorem base_writer {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (w : X.Intent ref a true)
    (cov : a.Covers l) (sp : l.space=.shared) (lo : L.sharedBase ≤ l.addr)
    (hi : l.addr<L.sharedBase+4) :
    (∃ g k bs, ref=.thread (g,k) ∧ X.get (g,k)=some ⟨11,.wr a bs⟩) ∨
      ∀ g k, ref ≠ .thread (g,k) := by
  rcases Lib.write_intents hX w with ⟨⟨g,k⟩,pc,bs,rfl,get⟩|⟨_,_,_,_,_,_,rfl,_⟩
  · obtain ⟨hs,_,alo,ahi⟩ := cov
    rcases writer_region hp hX get (hs.symm.trans sp) (b := l.addr-L.sharedBase)
      (by omega) (by omega) with ⟨_,rfl⟩|⟨_,_,_⟩|⟨_,_,_⟩|⟨_,_,_⟩
    · exact .inl ⟨g,k,bs,rfl,get⟩
    all_goals omega
  · exact .inr fun _ _ h => by cases h

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
