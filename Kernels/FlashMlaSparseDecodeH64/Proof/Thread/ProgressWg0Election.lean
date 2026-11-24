-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Lemmas.Flow.ElectActor
public import Lemmas.Step.WarpAppend
import Lemmas.Step.WarpElect
import Lemmas.Step.CommitOrderExtend

public section

/-! # The full-warp elections of the output path -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- Every launched warp lane belongs to the full mask. -/
theorem full_member (L : Launch) (g : Nat) : electMember (2 ^ 32 - 1) (PTX.laneOf L g) := by
  have hl := Nat.mod_lt (g % L.block) (show 0 < 32 by decide)
  refine ⟨hl, ?_⟩
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hl

private theorem election_template {P : Params} {L : Launch} {g : Nat} {d : Wg0.D}
    {j : Fin 4} {u : TState} {ins : Instr} (ha : (Wg0.code P L g).AtD d u)
    (hc : kernel.code[d.site.pc]? = some ins) (hd : d.site = .elect j) :
    ∃ k, eventTmpl Assumptions.all L g u ins.op = .elect (2 ^ 32 - 1) k := by
  rw [hd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (Wg0.election_code j))
  have hr : u.regs (Wg0.electionMask j) = some (b32 (2 ^ 32 - 1)) := by
    have hv := Wg0.reg_value ha (r := Wg0.electionMask j)
      (by rw [hd]; fin_cases j <;> decide +kernel)
    fin_cases j <;> exact hv
  have hbits := readBits_b32 (L := L) (g := g) hr (by decide)
  simp only [eventTmpl, warpTmpl_elect, electTmpl, hbits,
    show (BitVec.ofNat 64 (2 ^ 32 - 1)).toNat = 2 ^ 32 - 1 from rfl,
    full_member L g, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- An actual output election names all lanes of the issuing warp. -/
theorem softmax_election_event {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : Wg0.D} {j : Fin 4} {ev : Event}
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hσ : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hd : d.site = .elect j) (he : X.get (g, i) = some ev) :
    ∃ inst leader, ev = ⟨(Wg0.Site.elect j).pc, .elect (2 ^ 32 - 1) inst leader⟩ := by
  obtain ⟨_, ins, _, ha, _, hc, hf⟩ := Frame.fired_site hs hX he hσ
  obtain ⟨k, hTemplate⟩ := election_template ha hc hd
  change Fires d.site.pc _ _ _ at hf
  rw [hTemplate, hd] at hf
  obtain ⟨inst, leader, hevent, _⟩ := hf
  exact ⟨inst, leader, hevent⟩

/-- A batch of collective events preserves the assumptions when it adds no launch read,
tensor-store issue or exit, and keeps the asynchronous notifications unchanged. -/
theorem all_wf_collective_batch {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (lanes : List Nat) (ev : Nat → Event)
    (hnc : ∀ h a bs, (ev h).kind ≠ .nc a bs)
    (hStore : ∀ h ptr s, (ev h).kind ≠ .tensorStore ptr s)
    (hExit : ∀ h, (ev h).kind ≠ .exit) :
    ∀ a ∈ Assumptions.all, a.wf L mem0 (X.appendLanes lanes ev) := by
  let Z := X.appendLanes lanes ev
  intro a ha
  have hold := hX.asm a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hold
  · intro i pc acc bytes he hp
    have heOld : X.get i = some ⟨pc, .nc acc bytes⟩ :=
      (PTX.appendLanes_get_kind (fun h _ => hnc h acc bytes)).mp he
    exact hold i pc acc bytes heOld hp
  · intro i finish hb ⟨pc, addr, spec, hi, hsel⟩ ⟨endTag, hexit⟩
    have heOld : X.get finish = some ⟨endTag, .exit⟩ :=
      (PTX.appendLanes_get_kind (fun h _ => hExit h)).mp hexit
    have hiOld : X.get i = some ⟨pc, .tensorStore addr spec⟩ :=
      (PTX.appendLanes_get_kind (fun h _ => hStore h addr spec)).mp hi
    exact Execution.readsDone_mono PTX.le_appendLanes
      (hold ⟨hb.1, hb.2.1, PTX.len_of_get heOld⟩ ⟨pc, addr, spec, hiOld, hsel⟩ ⟨endTag, heOld⟩)
  · exact Assumption.commitPerformedAt_extend (fun _ h => h) hold hX.tcCommit
      PTX.le_appendLanes (Execution.notifiedInOrder_of_eq (Y := Z) rfl)

/-- A full-mask election batch preserves the FlashMLA assumptions. -/
theorem all_wf_election_batch {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (lanes : List Nat) (tag inst leader : Nat) :
    ∀ a ∈ Assumptions.all, a.wf L mem0
      (X.appendLanes lanes (fun _ => ⟨tag, .elect (2 ^ 32 - 1) inst leader⟩)) :=
  all_wf_collective_batch hX lanes _ (fun _ _ _ h => Kind.noConfusion h)
    (fun _ _ _ h => Kind.noConfusion h) (fun _ h => Kind.noConfusion h)

/-- When the warp reaches one output tile's election, it can issue a single full-mask instance. -/
theorem softmax_election_batch {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {j : Fin 4} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) (hub : ¬ HasUb X)
    (hall : ∀ h, SameWarp L g h → ∃ d, Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
      Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some (.wg0 d)) ∧
      d.site = .elect j) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨leader, hm, hdet⟩ := PTX.Step.exists_leader (g := g) hX (full_member L g)
  refine PTX.Step.elect_counted_extension (pc := (Wg0.Site.elect j).pc) hX hg
    (fun lane hl => PTX.Step.warp_full hb hg hl.1) (fun h _ => full_member L h) hm hdet ?_
    (fun h hw => (hall h hw).choose_spec.2.1) ?_
    (fun inst => all_wf_election_batch hX (PTX.Step.warpThreads L g) _ inst leader)
  · intro h hw
    obtain ⟨d, hPend, _, hState, _⟩ := hall h hw
    refine .inl ?_
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hState
    cases hState
  · intro h hw inst
    obtain ⟨d, hPend, _, hState, hSite⟩ := hall h hw
    obtain ⟨t, hRun⟩ := Frame.run_some hX hub hPend
    obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hPend.1 hRun hState
    obtain ⟨k, hTemplate⟩ := election_template ha hc hSite
    have hp : u.pc = (Wg0.Site.elect j).pc := ha.1.trans (congrArg Wg0.Site.pc hSite)
    rw [hTemplate] at hout
    exact ⟨t, u, some (k leader), hRun, hTau, _, hout, inst, leader, by rw [hp], rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
