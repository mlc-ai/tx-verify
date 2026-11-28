-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Ordered
import Kernels.InklingRelDecode.Proof.Startup.Export.AllocWrite
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Dispatch.Export.RoleAddress
import Kernels.InklingRelDecode.Proof.Common.Export.PairAddress
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Lemmas.Flow.AccessLocal
import Lemmas.Flow.NotRead
import Lemmas.Flow.NotBulk
import Lemmas.Flow.OpPcsFast
import Lemmas.Protocol.Region

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow

private def sharedRead (op : Op) : Bool :=
  loadSpace op == some .shared || (dynamicAccess op && readOp op)

private theorem sites : OpPcsFast kernel.code sharedRead [13,2252,2340,2345,2423]=true := by
  decide +kernel

theorem shared_read_site {L m X g k pc a bs} (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,k)=some ⟨pc,.rd a bs⟩) (space : a.loc.space=.shared) :
    pc ∈ [13,2252,2340,2345,2423] := by
  obtain ⟨_,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX get
  · cases bad
  apply OpPcsFast.mem sites code

  rcases fires_read_loc fire rfl with ⟨eq,_⟩|dyn
  · simp [sharedRead,eq,space]
  · simp [sharedRead,dyn,fires_read_op fire rfl]

/-- All five ordinary shared load sites use the base word, scratch, role word or count pair. -/
theorem read_outside_arena {Q L m X g k pc a bs l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some ⟨pc,.rd a bs⟩)
    (cover : a.Covers l) (sp : l.space=.shared) :
    l.addr<L.sharedBase+213008 ∨ (L.sharedBase+213336≤l.addr ∧ pc=2340) := by
  have site := shared_read_site hX get (cover.1.symm.trans sp)
  obtain ⟨_,_,lo,hi⟩ := cover
  simp only [List.mem_cons,List.not_mem_nil,or_false] at site
  rcases site with rfl|rfl|rfl|pair
  · obtain ⟨loc,size⟩ := Startup.Export.base_address hp hX get
    rw [loc,size] at hi
    change l.addr<L.sharedBase+4 at hi
    omega
  · obtain ⟨loc,size⟩ := Softmax.Export.scratch_read hp hX get
    rw [loc,size] at hi
    dsimp only at hi
    omega
  · obtain ⟨_,_,_,loc⟩ := Dispatch.Export.role_address hp hX get
    rw [loc] at lo
    dsimp only at lo
    exact .inr ⟨by omega,rfl⟩
  · obtain ⟨j,_,loc,size⟩ := Export.pair_address hp hX get pair
    rw [loc,size] at hi
    dsimp only at hi
    have := j.isLt
    omega

/-- Only a pending or performed MMA operand read can still overlap the initializer arena. -/
theorem arena_reader {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (read : X.Intent ref a false)
    (cov : a.Covers l) (sp : l.space=.shared)
    (lo : L.sharedBase+213008≤l.addr) (hi : l.addr<L.sharedBase+213336) :
    ∃ i b j, ref=.async i (.mmaRead b j) := by
  rcases Execution.shared_intent read cov sp with
    ⟨i,rfl,acc⟩|mma|⟨i,x,y,z,rfl⟩|⟨i,x,y,z,rfl⟩|⟨_,_,_,_,_,⟨_,get⟩,_⟩|
      ⟨_,_,_,_,⟨_,get⟩⟩|⟨_,_,⟨_,get⟩⟩
  · rcases acc with ⟨bs,⟨pc,get⟩,_⟩|⟨_,_,bad⟩|rmw
    · have := read_outside_arena hp hX get cov sp
      omega
    · cases bad
    · exact (no_arena_write (ref := .thread i) hp hX (.inr (.inr rmw)) cov sp lo hi).elim
  · exact mma
  · obtain ⟨_,_,_,⟨_,get⟩,_⟩ := read
    exact (Lib.no_tensorStore hX get).elim
  · cases read.1
  · exact (Lib.no_clc hX get).elim
  · exact (Lib.no_copy hX get).elim
  · exact (Lib.no_bulkPrefetch hX get).elim

/-- The ordinary shared loads touch the base word (pc 13), the count pair, the scratch words or
the role word: below the base word's end or at the count pair and above. -/
theorem read_site_region {Q L m X g k pc a bs l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some ⟨pc,.rd a bs⟩)
    (cover : a.Covers l) (sp : l.space=.shared) :
    (pc=13 ∧ l.addr<L.sharedBase+4) ∨ L.sharedBase+212992≤l.addr := by
  have site := shared_read_site hX get (cover.1.symm.trans sp)
  obtain ⟨_,_,lo,hi⟩ := cover
  simp only [List.mem_cons,List.not_mem_nil,or_false] at site
  rcases site with rfl|rfl|rfl|pair
  · obtain ⟨loc,size⟩ := Startup.Export.base_address hp hX get
    rw [loc,size] at hi
    change l.addr<L.sharedBase+4 at hi
    exact .inl ⟨rfl,hi⟩
  · obtain ⟨loc,size⟩ := Softmax.Export.scratch_read hp hX get
    rw [loc] at lo
    dsimp only at lo
    omega
  · obtain ⟨_,_,_,loc⟩ := Dispatch.Export.role_address hp hX get
    rw [loc] at lo
    dsimp only at lo
    omega
  · obtain ⟨j,_,loc,size⟩ := Export.pair_address hp hX get pair
    rw [loc] at lo
    dsimp only at lo
    omega

theorem read_region {Q L m X g k pc a bs l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some ⟨pc,.rd a bs⟩)
    (cover : a.Covers l) (sp : l.space=.shared) :
    l.addr<L.sharedBase+4 ∨ L.sharedBase+212992≤l.addr := by
  rcases read_site_region hp hX get cover sp with ⟨_,h⟩|h
  · exact .inl h
  · exact .inr h

theorem read_off_query {Q L m X g k pc a bs l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (get : X.get (g,k)=some ⟨pc,.rd a bs⟩)
    (cover : a.Covers l) (sp : l.space=.shared) :
    l.addr<L.sharedBase+196608 ∨ L.sharedBase+212992≤l.addr := by
  have := read_region hp hX get cover sp
  omega

/-- A shared byte no ordinary load covers is read only by a pending or performed MMA. -/
theorem mma_reader {L m X ref a l} (hX : Consistent L kernel Assumptions.all m X)
    (read : X.Intent ref a false) (cov : a.Covers l) (sp : l.space=.shared)
    (off : ∀ g k pc a' bs, X.get (g,k)=some ⟨pc,.rd a' bs⟩ → a'.Covers l → False) :
    ∃ i b j, ref=.async i (.mmaRead b j) := by
  rcases Execution.shared_intent read cov sp with
    ⟨i,rfl,acc⟩|mma|⟨i,x,y,z,rfl⟩|⟨i,x,y,z,rfl⟩|⟨_,_,_,_,_,⟨_,get⟩,_⟩|
      ⟨_,_,_,_,⟨_,get⟩⟩|⟨_,_,⟨_,get⟩⟩
  · rcases acc with ⟨bs,⟨pc,get⟩,_⟩|⟨_,_,bad⟩|⟨old,new,pc,get⟩
    · exact (off _ _ _ _ _ get cov).elim
    · cases bad
    · have wr : X.Intent (.thread i) a true := .inr (.inr ⟨old,new,pc,get⟩)
      rcases Lib.write_intents hX wr with ⟨j,q,bs,eq,h⟩|⟨_,_,_,_,_,_,eq,_⟩
      · cases eq
        rw [get] at h
        cases h
      · cases eq
  · exact mma
  · obtain ⟨_,_,_,⟨_,get⟩,_⟩ := read
    exact (Lib.no_tensorStore hX get).elim
  · cases read.1
  · exact (Lib.no_clc hX get).elim
  · exact (Lib.no_copy hX get).elim
  · exact (Lib.no_bulkPrefetch hX get).elim

/-- Only a pending or performed MMA operand read can overlap the query tile. -/
theorem query_reader {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (read : X.Intent ref a false)
    (cov : a.Covers l) (sp : l.space=.shared)
    (lo : L.sharedBase+196608≤l.addr) (hi : l.addr<L.sharedBase+212992) :
    ∃ i b j, ref=.async i (.mmaRead b j) :=
  mma_reader hX read cov sp fun _ _ _ _ _ get c => by
    have := read_off_query hp hX get c sp
    omega

/-- Only a pending or performed MMA operand read can overlap the K and V rings. -/
theorem kv_reader {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (read : X.Intent ref a false)
    (cov : a.Covers l) (sp : l.space=.shared)
    (lo : L.sharedBase+4≤l.addr) (hi : l.addr<L.sharedBase+196608) :
    ∃ i b j, ref=.async i (.mmaRead b j) :=
  mma_reader hX read cov sp fun _ _ _ _ _ get c => by
    have := read_region hp hX get c sp
    omega

/-- **A read of a base word byte is the startup's load or a pending or performed MMA's.** -/
theorem base_reader {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (read : X.Intent ref a false)
    (cov : a.Covers l) (sp : l.space=.shared) (hi : l.addr<L.sharedBase+4) :
    (∃ g k bs, ref=.thread (g,k) ∧ X.get (g,k)=some ⟨13,.rd a bs⟩) ∨
      ∃ i b j, ref=.async i (.mmaRead b j) := by
  rcases Execution.shared_intent read cov sp with
    ⟨i,rfl,acc⟩|mma|⟨i,x,y,z,rfl⟩|⟨i,x,y,z,rfl⟩|⟨_,_,_,_,_,⟨_,get⟩,_⟩|
      ⟨_,_,_,_,⟨_,get⟩⟩|⟨_,_,⟨_,get⟩⟩
  · rcases acc with ⟨bs,⟨pc,get⟩,_⟩|⟨_,_,bad⟩|⟨old,new,pc,get⟩
    · rcases read_site_region hp hX get cov sp with ⟨rfl,_⟩|far
      · exact .inl ⟨i.1,i.2,bs,rfl,get⟩
      · omega
    · cases bad
    · have wr : X.Intent (.thread i) a true := .inr (.inr ⟨old,new,pc,get⟩)
      rcases Lib.write_intents hX wr with ⟨j,q,bs,eq,h⟩|⟨_,_,_,_,_,_,eq,_⟩
      · cases eq
        rw [get] at h
        cases h
      · cases eq
  · exact .inr mma
  · obtain ⟨_,_,_,⟨_,get⟩,_⟩ := read
    exact (Lib.no_tensorStore hX get).elim
  · cases read.1
  · exact (Lib.no_clc hX get).elim
  · exact (Lib.no_copy hX get).elim
  · exact (Lib.no_bulkPrefetch hX get).elim

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
