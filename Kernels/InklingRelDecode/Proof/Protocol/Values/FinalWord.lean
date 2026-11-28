-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalWrites
public import Lemmas.Tcgen05.MemFloat
import Lemmas.Kernel.Memory
import Lemmas.Kernel.Frame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX

/-- An output scalar has an actual issuing store. All epilogue stores that
overlap any of its four bytes agree on that byte's value. -/
def StoredWord (X : Execution) (l : Loc) (v : Value) : Prop :=
  (∃ i pc a bs, X.get i=some ⟨pc,.wr a bs⟩ ∧ a.loc=l ∧ a.size=4) ∧
  ∀ j<4, ∀ i pc a bs, X.get i=some ⟨pc,.wr a bs⟩ → pc ∈ Shared.outputSites →
    a.Covers (l.at j) → wbyte a bs (l.at j)=some (v.byteAt j)

/-- Coherence selects a maximal writer separately for each byte. All possible
writers belong to the finite traces of the launched threads. -/
theorem final_word {Q L m X mf l v} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : IsFinal L m X mf)
    (gl : l.space=.global) (word : StoredWord X l v) :
    ∀ j<4, mf (l.at j)=some (some (v.byteAt j)) := by
  intro j bound
  obtain ⟨⟨i,pc,a,bs,get,loc,size⟩,agree⟩ := word
  have covers : a.Covers (l.at j) := by simp [Acc.Covers,Loc.InRange,Loc.at,loc,size,bound]
  let writes := (List.range L.threads).flatMap fun g =>
    (List.range (X.tr g).length).map fun k => AsyncCopy.Ref.thread (g,k)
  refine hf.of_agree (ws := writes) (w := .thread i) (a := a) (bs := bs)
    ?_ (.inl ⟨pc,get⟩) covers ?_
  · intro w a bs wr cov
    obtain ⟨⟨g,k⟩,pc,_,rfl,ev,_⟩ := Shared.global_writer hp hX wr.intent (cov.1.symm.trans gl)
    have hg := Frame.lt_of_get hX ev
    have hk := (List.getElem?_eq_some_iff.mp ev).1
    unfold writes
    exact List.mem_flatMap.mpr ⟨g,List.mem_range.mpr hg,
      List.mem_map.mpr ⟨k,List.mem_range.mpr hk,rfl⟩⟩
  · intro w dst data wr cov
    obtain ⟨i,pc,bytes,rfl,ev,site⟩ := Shared.global_writer hp hX wr.intent (cov.1.symm.trans gl)
    have eq := wr.unique (show X.MemWrites (.thread i) dst bytes from .inl ⟨pc,ev⟩)
    rw [eq.2]
    exact agree j bound i pc dst bytes ev site cov

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
