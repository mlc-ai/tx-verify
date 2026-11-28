-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalWrites
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Readers
import Kernels.InklingRelDecode.Proof.Protocol.Shared.Writers
import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvAccess
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchPlace
import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalInject
import Kernels.InklingRelDecode.Proof.Startup.Export.AllocWrite
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Dispatch.Export.RoleAddress
import Kernels.InklingRelDecode.Proof.Common.Export.PairAddress
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Lib.NoLocalConst
import Kernels.InklingRelDecode.Proof.Lib.WriteCta
import Kernels.InklingRelDecode.Proof.Lib.ReadKinds
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Protocol.NamedBarSources

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Alloc
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A byte of a launched CTA's shared window is allocated. -/
theorem shared_alloc (hp : Pre Q L m) {l : Loc} (hs : l.space = .shared) (hc : l.cta < L.grid)
    (lo : L.sharedBase ≤ l.addr) (hi : l.addr < L.sharedBase + sharedBytes) : m l ≠ none := by
  have h := hp.sharedAllocated l.cta hc (l.addr - L.sharedBase) (by omega)
  obtain ⟨s,c,x⟩ := l
  simp only at hs hc lo hi
  subst hs
  rwa [show L.sharedBase + (x - L.sharedBase) = x by omega] at h

/-- An input byte is allocated. -/
theorem input_alloc (hp : Pre Q L m) {l : Loc} (h : Iface.InInput Q l) : m l ≠ none := by
  obtain ⟨s,c,x⟩ := l
  obtain ⟨rfl,rfl,rd⟩ := h
  obtain ⟨b,hb⟩ := Shared.initialized hp rd
  rw [hb]
  nofun

theorem read_box (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc a bs} (get : X.get (g,k) = some ⟨pc,.rd a bs⟩) (site : pc ∈ [13,2252,2340,2345,2423]) :
    a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ L.sharedBase + sharedBytes := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at site
  rcases site with rfl|rfl|rfl|pair
  · obtain ⟨loc,size⟩ := Startup.Export.base_address hp hX get
    rw [loc,size]
    exact ⟨rfl,rfl,le_rfl,by simp only [sharedBytes]; omega⟩
  · obtain ⟨loc,size⟩ := Softmax.Export.scratch_read hp hX get
    have := Nat.mod_lt (g%L.block) (by omega : 0 < 4)
    rw [loc,size]
    refine ⟨rfl,rfl,?_,?_⟩ <;> (dsimp only; (try simp only [sharedBytes]); omega)
  · obtain ⟨_,hi,size,loc⟩ := Dispatch.Export.role_address hp hX get
    rw [loc,size]
    refine ⟨rfl,rfl,?_,?_⟩ <;> (dsimp only; (try simp only [sharedBytes]); omega)
  · obtain ⟨j,_,loc,size⟩ := Export.pair_address hp hX get pair
    have := j.isLt
    rw [loc,size]
    refine ⟨rfl,rfl,?_,?_⟩ <;> (dsimp only; (try simp only [sharedBytes]); omega)

theorem tensor_read_space {s x y z loc} (h : TensorCopy.readLoc s x y z = some loc) :
    loc.space = .global := by
  rw [TensorCopy.readLoc_source] at h
  obtain ⟨slot,_,hs⟩ := Option.bind_eq_some_iff.mp h
  revert hs
  cases TensorCopy.source s slot with
  | fill => simp
  | global address => intro hs; rw [← Option.some.inj hs]

/-- **Every byte a read touches is allocated.** Global bytes are input bytes. -/
theorem read_alloc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (gr : Iface.GlobalReads Q X) {ref a l} (r : X.Intent ref a false)
    (cov : a.Covers l) : m l ≠ none := by
  by_cases gl : l.space = .global
  · exact input_alloc hp (gr ref a l r cov gl)
  rcases Lib.read_intents hX r with ⟨⟨g,k⟩,pc,bs,rfl,get⟩|⟨⟨g,k⟩,isB,j,rfl,foot⟩|
    ⟨i,x,y,z,addr,sp,rfl,issue,loc,size⟩
  · have site : pc ∈ [13,2252,2340,2345,2423] := by
      by_cases sh : a.loc.space = .shared
      · exact Shared.shared_read_site hX get sh
      · have lc : a.loc.space = .local ∨ a.loc.space = .const := by
          have e := cov.1
          rw [← e] at sh ⊢
          cases h : l.space <;> simp_all
        have := Lib.load_off_space hX get lc
        simp only [List.mem_cons,List.not_mem_nil,or_false] at this ⊢
        omega
    obtain ⟨hs,hc,lo,hi⟩ := read_box hp hX get site
    obtain ⟨s',c',lo',hi'⟩ := cov
    exact shared_alloc hp (s'.trans hs) (c' ▸ hc ▸ NamedBar.cta_lt (Frame.lt_of_get hX get))
      (by omega) (by omega)
  · obtain ⟨_,size,_⟩ := r
    obtain ⟨s',c',lo',hi'⟩ := cov
    rcases foot with ⟨dst,s,acc,mask,⟨pc,get⟩,byte⟩|⟨c,_,_,cp,_⟩
    · obtain ⟨_,_,tile⟩ := Mma.Export.operands_all hp hX hf get
      have box : a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
          a.loc.addr < L.sharedBase + 212992 := by
        cases isB
        · obtain ⟨sp,ct,lo,hi⟩ := tile .a j _ byte
          exact ⟨sp,ct,by omega,hi⟩
        · obtain ⟨sp,ct,lo,hi⟩ := tile .b j _ byte
          exact ⟨sp,ct,lo,by omega⟩
      obtain ⟨hs,hc,lo,hi⟩ := box
      exact shared_alloc hp (s'.trans hs) (c' ▸ hc ▸ NamedBar.cta_lt (Frame.lt_of_get hX get))
        (by omega) (by simp only [sharedBytes]; omega)
    · exact (Lib.no_cp hX (g,k) c cp).elim
  · exact (gl (cov.1.trans (tensor_read_space loc))).elim

private theorem output_site {p} (h : p ∈ Shared.outputSites) : Shared.IsStoreSite p := by
  simp only [Shared.outputSites,List.mem_cons,List.mem_map,List.mem_range] at h
  rcases h with rfl | ⟨n,hn,rfl⟩
  · exact .inl rfl
  · exact .inr ⟨⟨n,hn⟩,rfl⟩

private theorem tensor_write_space (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc addr sp x y z l} (get : X.get (g,k) = some ⟨pc,.tensorIssue addr sp⟩)
    (byte : TensorCopy.writeLoc sp x y z = some l) : l.space = .shared := by
  obtain ⟨⟨_,shared,_⟩,_⟩ := Shared.tensor_box hp hX get
  simp only [TensorCopy.writeLoc,Option.map_eq_some_iff] at byte
  obtain ⟨_,_,loc⟩ := byte
  rw [← loc]
  exact shared

/-- **Every byte a write touches is allocated.** Global bytes are the output bytes. -/
theorem write_alloc (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (placed : Shared.OutputPlaced Q X) {ref a l} (w : X.Intent ref a true)
    (cov : a.Covers l) : m l ≠ none := by
  obtain ⟨hs0,hc0,lo0,hi0⟩ := id cov
  by_cases gl : l.space = .global
  · obtain ⟨⟨g,k⟩,pc,bs,rfl,get,site⟩ := Shared.global_writer hp hX w (hs0.symm.trans gl)
    obtain ⟨_,_,_,loc⟩ := Export.store_address hp hX hf get (output_site site)
    have c0 : a.loc.cta = 0 := by
      rcases loc with ⟨_,_,h⟩|⟨_,_,h⟩ <;> rw [h] <;> rfl
    have rng := Shared.output_intent hp hX placed w cov gl
    obtain ⟨s,c,x⟩ := l
    simp only at gl hc0 rng
    subst gl
    obtain rfl : c = 0 := hc0.trans c0
    rcases rng with ⟨lo,hi⟩|⟨lo,hi⟩
    · have := hp.oAllocated (x - Q.oBase) (by omega)
      rwa [show Q.oBase + (x - Q.oBase) = x by omega] at this
    · have := hp.lseAllocated (x - Q.lseBase) (by omega)
      rwa [show Q.lseBase + (x - Q.lseBase) = x by omega] at this
  rcases Lib.write_intents hX w with ⟨⟨g,k⟩,pc,bs,rfl,get⟩|
    ⟨⟨g,k⟩,x,y,z,addr,sp,eq,⟨pc,issue⟩,byte,_⟩
  · have hs : a.loc.space = .shared := by
      rcases Shared.write_space hp hX get with h|h
      · exact h
      · exact (gl (hs0.trans h)).elim
    obtain ⟨_,rng⟩ := Shared.writer_at hp hX get hs lo0 hi0
    have cta : a.loc.cta = g / L.block := by
      obtain ⟨_,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX get
      · cases bad
      exact Lib.code_write_cta code fire hs
    refine shared_alloc hp (hs0.trans hs) (hc0 ▸ cta ▸ NamedBar.cta_lt (Frame.lt_of_get hX get))
      (by omega) ?_
    simp only [sharedBytes]
    rcases rng with h|h|h|h <;> omega
  · have async : ∀ g' k', ref ≠ .thread (g',k') := by
      rintro g' k' h
      rw [eq] at h
      cases h
    obtain ⟨g',k',_,_,_,_,_,_,σ,_,get,_,hc,slot,byte'⟩ :=
      Shared.copy_write_facts hp hX hf w cov async
    have ring := Iface.inSlot_kv σ.isLt slot
    exact shared_alloc hp (tensor_write_space hp hX get byte') (hc ▸ NamedBar.cta_lt
      (Frame.lt_of_get hX get)) (by omega) (by simp only [sharedBytes]; omega)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Alloc
