-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Steps
public import Lemmas.Flow.StepsQShfl

@[expose] public section

/-! # The head's shuffle under an invariant, for the word `7`

`Wg1.stepForQ_hsh7`: the strict step obligation under an invariant `Q` of the concrete state
(`Code.StepForQ`) of the head's shuffle for an event that received the word `7`. The invariant
holds right after the shuffle (`hQ`), and the segment from there to the index warp's first event is
strict (`hseg`): the index warp's strict parameter prefix, which `Common/StrictIndex.lean`
supplies. -/

/-! # The head's dispatch to the index warp, as an exact segment

`Wg1.head_index_seg`: from the head's shuffle (pc 1844) with the word `7` the dispatch's tests lead
to pc 2332, with the entry registers' table. The index warp's strict parameter prefix
(`Index.qw_entry`) continues from there (`Common/StrictIndex.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- **The head's walk to the index warp's entry.** -/
theorem head_index_seg (x : BitVec 64) (ok : Bool)
    (h7 : scmpi .eq .b x 7 = true) :
    ∃ n, Seg kernel Assumptions.all L g n 1844 (hshFacts L g x ok) 2332
      (Flow.factsFrom (Flow.live 2332) (entryVal L g)) := by
  seg_sym using w1_seg

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Flow.Havoc

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- **The head's shuffle, strict under an invariant for the word `7`**: the events that satisfy
`Wf` at the shuffle's pc received the word `7`. -/
theorem stepForQ_hsh7 {Q : TState → Prop} {Wf : Event → Prop} (e : Event)
    (hW : ∀ e, Wf e → e.pc = Site.pc P L g .hsh → ∀ md av bv cv recv ok,
      e.kind = .shfl md av bv cv recv ok → ∃ x, recv = .bits 32 x ∧ scmpi .eq .b x 7 = true)
    (hQ : ∀ w : TState, w.pc = 1844 → Q w)
    (hseg : ∀ x ok, scmpi .eq .b x 7 = true →
      SegQ kernel Assumptions.all L g Q 1844 (hshFacts L g x ok) (Site.pc P L g .index)
        (headFacts P L g .index)) : (code P L g).StepForQ Q Wf .hsh e := by
  refine Code.step_shflForQ (nv := fun v _ => dispatch v)
    (by code_lookup) (by fact_free) (by fact_free) (by decide) (fun _ _ _ _ _ _ => rfl) rfl rfl e
    ?_
  intro recv ok hwe ⟨m, av, bv, cv, he⟩
  obtain ⟨x, rfl, hx⟩ := hW e hwe (by rw [he]) m av bv cv recv ok (by rw [he])
  refine ⟨.index, ?_, fun w hw => hQ w hw.1, rfl, rfl, fun _ => trivial, hseg x ok hx⟩
  simp [dispatch, hx]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
