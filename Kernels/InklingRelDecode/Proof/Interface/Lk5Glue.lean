-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5VChain
public import Kernels.InklingRelDecode.Proof.Interface.Lk2Agree

@[expose] public section

/-!
# The softmax rows of the lockstep agreement, from the decisions of each iteration

Two lanes of a warp at synchronizing softmax states of one key are at one site and one
iteration (the loop counter is in the key, `sm_key_comps`). At `shfl12` the decision of iteration
`i` is the same in all default threads of a CTA (`DecAgree`, from the scratch words of the
iteration: `decAgree_of_it`), and the edge into the P store succeeds in both lanes or in neither
(`updOkSame`). So the softmax rows of the agreement (`LaneAgreeSm`) need neither the lockstep nor
an induction on the synchronizing ordinal.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Lk (smKey sm_key_comps smSy SmAgree)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The lazy-rescale branch of two lanes of a warp at one softmax key**, from the decisions of
every iteration. -/
theorem smAgree_of_dec (hD : ∀ c j, DecAgree Q L X c j) {g h a b : Nat} {d d' : Sm.D}
    {e e' : Event} (hw : SameWarp L g h) (hge : (X.tr g)[a]? = some e)
    (hhe : (X.tr h)[b]? = some e') (hs : St Q L X g a = some (some (.d (.sm d))))
    (hs' : St Q L X h b = some (some (.d (.sm d')))) (hsy : smSy d = true)
    (hsy' : smSy d' = true)
    (hk : (kernelSkel Q L).key g (.d (.sm d)) = (kernelSkel Q L).key h (.d (.sm d'))) :
    SmAgree L g h d d' e e' := by
  intro hsite
  obtain ⟨hsite12, -, hi', -⟩ := sm_key_comps hsy hsy' (show smKey L g d = smKey L h d' from hk)
  have hsite' : d'.site = .shfl12 := hsite12.symm.trans hsite
  obtain ⟨r1, r2, o1, o2, he1, he2, hp⟩ := hD (g / L.block) d.i hw.1.1 hw.1.2.1 rfl
    hw.1.2.2.symm hge hhe hs hs' hsite hsite' rfl hi'.symm
  have hk1 : e.kind = .shfl .bfly d.stg.m2 1 31 r1 o1 := by rw [he1]
  have hk2 : e'.kind = .shfl .bfly d'.stg.m2 1 31 r2 o2 := by rw [he2]
  have hu := updOkSame (Q := Q) (X := X) hw hs hs' hsite hsite'
  rw [PTX.Kernels.InklingRelDecode.Proof.Sm.branchBar20_iff hsite hk1,
    PTX.Kernels.InklingRelDecode.Proof.Sm.branchBar20_iff hsite' hk2, hp]
  exact and_congr_right fun _ => hu

/-- **`LaneAgreeSm` from the scratch words of every iteration.** -/
theorem laneAgreeSm_of_it (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (h : ∀ i, ScratchIt Q L X i) : LaneAgreeSm Q L X := by
  intro n _ g h' a b s s' e e' hw he he' hsa hsb hsy hsy' _ _ hk
  rcases s with (s | s) <;> rcases s' with (s' | s') <;> (try cases s) <;> (try cases s') <;>
    first
    | trivial
    | exact smAgree_of_dec (fun c j => decAgree_of_it hpre hX hf (h j) c) hw he he' hsa hsb hsy
        hsy' hk

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
