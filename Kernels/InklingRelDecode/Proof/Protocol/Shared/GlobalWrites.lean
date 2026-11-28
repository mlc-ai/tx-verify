-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.TensorSource
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Lib.RoleWord
import Kernels.InklingRelDecode.Proof.Prologue.Export.Publish
import Lemmas.Flow.NotBulk
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.WriteSpace

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow

/-- The one LSE store and the 64 columns of the epilogue output window. -/
def outputSites := 2682 :: (List.range 64).map (fun j => 2751+j+j/2)

private def globalWrite (op : Op) : Bool :=
  storeSpace op == some .global || (dynamicAccess op && writeOp op)

private theorem sites : OpPcsFast kernel.code globalWrite (570::571::2848::outputSites)=true := by
  decide +kernel

/-- Classifies even an outstanding write intent. The tensor loads write only
their issuer's shared memory; all global writes are actual epilogue stores. -/
theorem global_writer {Q L m X ref a} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (intent : X.Intent ref a true)
    (sp : a.loc.space=.global) :
    ∃ i pc bs, ref=.thread i ∧ X.get i=some ⟨pc,.wr a bs⟩ ∧ pc ∈ outputSites := by
  rcases Lib.write_intents hX intent with ⟨i,pc,bs,rfl,get⟩|⟨⟨g,k⟩,x,y,z,addr,s,_,⟨pc,get⟩,byte,_⟩
  · refine ⟨_,_,_,rfl,get,?_⟩
    obtain ⟨_,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX get
    · cases bad
    have hit := OpPcsFast.mem sites code (by
      rcases fires_write_space fire rfl with static|dynamic
      · simp [globalWrite,static,sp]
      · simp [globalWrite,dynamic,fires_write_op fire rfl])
    simp only [List.mem_cons] at hit
    rcases hit with rfl|rfl|rfl|known
    · obtain ⟨loc,_⟩ := Lib.role_word hp hX get (.inl ⟨rfl,rfl⟩)
      rw [loc] at sp
      cases sp
    · obtain ⟨_,_,_,loc,_⟩ := Prologue.Export.pair_bytes hp hX get
      rw [loc] at sp
      cases sp
    · obtain ⟨loc,_⟩ := Lib.role_word hp hX get (.inr ⟨rfl,rfl⟩)
      rw [loc] at sp
      cases sp
    · exact known
  · have ⟨_,shared,_⟩ := (tensor_box hp hX get).1
    simp only [TensorCopy.writeLoc,Option.map_eq_some_iff] at byte
    obtain ⟨slot,_,loc⟩ := byte
    rw [← loc] at sp
    have bad : Space.shared=.global := shared.symm.trans sp
    cases bad

/-- Placement owed by the epilogue for its two store families. It applies to
finite prefixes, including an issuing lane whose peers have not exited. -/
def OutputPlaced (Q : Params) (X : Execution) : Prop :=
  ∀ i pc a bs, X.get i=some ⟨pc,.wr a bs⟩ → pc ∈ outputSites → ∀ l, a.Covers l →
    l.space=.global →
      (Q.oBase≤l.addr ∧ l.addr<Q.oBase+oBytes Q) ∨
      (Q.lseBase≤l.addr ∧ l.addr<Q.lseBase+lseBytes Q)

theorem output_intent {Q L m X ref a l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (row : OutputPlaced Q X)
    (intent : X.Intent ref a true) (cover : a.Covers l) (gl : l.space=.global) :
    (Q.oBase≤l.addr ∧ l.addr<Q.oBase+oBytes Q) ∨
    (Q.lseBase≤l.addr ∧ l.addr<Q.lseBase+lseBytes Q) := by
  obtain ⟨i,pc,bs,_,get,site⟩ := global_writer hp hX intent (cover.1.symm.trans gl)
  exact row i pc a bs get site l cover gl

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
