-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressMmaElection
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Election
import Lemmas.Flow.ElectActor

public section

/-! # Warp 5 issues its actual gather election -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

private theorem tma_election_template {P : Params} {L : Launch} {g : Nat} {d : Wg1Tma.D}
    {u : TState} {ins : Instr} (ha : (Wg1Tma.code P L g).AtD d u)
    (hc : kernel.code[d.site.pc]? = some ins) (hd : d.site = .elect) :
    ∃ k, eventTmpl Assumptions.all L g u ins.op = .elect (2 ^ 32 - 1) k := by
  have hpc : d.site.pc = 2165 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2165)
  have hr : u.regs 663 = some (b32 4294967295) :=
    Wg1Tma.atD_regAt ha hpc (by decide +kernel)
  have hbits := readBits_b32 (L := L) (g := g) hr (by decide)
  simp only [eventTmpl, warpTmpl_elect, electTmpl, hbits]
  have hMask : (4294967295#64).toNat = 2 ^ 32 - 1 := by decide +kernel
  rw [hMask]
  rw [ite_eq_left (full_member L g)]
  exact ⟨_, rfl⟩

/-- A followed gather election actually emits the full-mask election for this warp. -/
theorem tma_election_event {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : Wg1Tma.D} {e : Event}
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hAt : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hd : d.site = .elect) (he : X.get (g, i) = some e) :
    ∃ inst leader, e = ⟨Wg1Tma.Site.elect.pc, .elect (2 ^ 32 - 1) inst leader⟩ := by
  obtain ⟨_, _, _, ha, _, hc, hf⟩ := Frame.fired_site hs hX he hAt
  obtain ⟨k, hTemplate⟩ := tma_election_template ha hc hd
  change Fires d.site.pc _ _ _ at hf
  rw [hTemplate, hd] at hf
  obtain ⟨inst, leader, hevent, _⟩ := hf
  exact ⟨inst, leader, hevent⟩

/-- When all gather lanes are released at their election, they issue one full-mask batch. -/
theorem tma_election_batch {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) (hub : ¬ HasUb X)
    (hall : ∀ h, SameWarp L g h → ∃ d, Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
      Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some (.tma d)) ∧
      d.site = .elect) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  refine full_election_batch (site := Wg1Tma.Site.elect.pc) hX (by rw [hpre.block]) hg ?_
    (fun h hw => (hall h hw).choose_spec.2.1) ?_
  · intro h hw
    obtain ⟨d, _, _, hState, _⟩ := hall h hw
    refine .inl ?_
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hState
    cases hState
  · intro h hw
    obtain ⟨d, hPend, _, hState, hSite⟩ := hall h hw
    obtain ⟨t, hRun⟩ := Frame.run_some hX hub hPend
    obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hPend.1 hRun hState
    obtain ⟨k, hTemplate⟩ := tma_election_template ha hc hSite
    have hp : u.pc = Wg1Tma.Site.elect.pc := ha.1.trans (congrArg Wg1Tma.Site.pc hSite)
    rw [hTemplate] at hout
    exact ⟨t, u, k, hRun, hTau, hp, hout⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
