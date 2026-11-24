-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Election
import Lemmas.Step.WarpElect

public section

/-! # Warp 4 issues its actual MMA election -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

private theorem mma_election_template {P : Params} {L : Launch} {g : Nat} {d : Wg1Mma.D}
    {u : TState} {ins : Instr} (ha : (Wg1Mma.code P L g).AtD d u)
    (hc : kernel.code[d.site.pc]? = some ins) (hd : d.site = .elect) :
    ∃ k, eventTmpl Assumptions.all L g u ins.op = .elect (2 ^ 32 - 1) k := by
  have hpc : d.site.pc = 1853 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1853)
  have hr : u.regs 794 = some (b32 4294967295) := by
    simpa only [Wg1Mma.valueOf, Wg1Mma.values, lookupLit, Option.getD_some] using
      Wg1Mma.atD_reg ha (r := 794) hpc (by decide +kernel)
  have hbits := readBits_b32 (L := L) (g := g) hr (by decide)
  simp only [eventTmpl, warpTmpl_elect, electTmpl, hbits]
  have hMask : (4294967295#64).toNat = 2 ^ 32 - 1 := by decide +kernel
  rw [hMask]
  rw [ite_eq_left (full_member L g)]
  exact ⟨_, rfl⟩

/-- A followed MMA election actually emits the full-mask election for this warp. -/
theorem mma_election_event {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : Wg1Mma.D} {e : Event}
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hAt : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hd : d.site = .elect) (he : X.get (g, i) = some e) :
    ∃ inst leader, e = ⟨Wg1Mma.Site.elect.pc, .elect (2 ^ 32 - 1) inst leader⟩ := by
  obtain ⟨_, _, _, ha, _, hc, hf⟩ := Frame.fired_site hs hX he hAt
  obtain ⟨k, hTemplate⟩ := mma_election_template ha hc hd
  change Fires d.site.pc _ _ _ at hf
  rw [hTemplate, hd] at hf
  obtain ⟨inst, leader, hevent, _⟩ := hf
  exact ⟨inst, leader, hevent⟩

/-- A warp whose live lanes share an election site can issue its full-mask batch. -/
theorem full_election_batch {L : Launch} {mem0 : Mem0} {X : Execution}
    {g site : Nat} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hb : L.block % 32 = 0) (hg : g < L.threads)
    (hstarted : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ PTX.Step.Launched L X h)
    (hreleased : ∀ h, SameWarp L g h → PTX.Step.Released L X h)
    (hRun : ∀ h, SameWarp L g h → ∃ t u k,
      Run kernel Assumptions.all L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L h) t u ∧ u.pc = site ∧
      out kernel Assumptions.all L h u = .ev (.elect (2 ^ 32 - 1) k)) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨leader, hm, hdet⟩ := PTX.Step.exists_leader (g := g) hX (full_member L g)
  refine PTX.Step.elect_counted_extension (pc := site) hX hg
    (fun lane hl => PTX.Step.warp_full hb hg hl.1) (fun h _ => full_member L h) hm hdet
    hstarted hreleased ?_
    (fun inst => all_wf_election_batch hX (PTX.Step.warpThreads L g) _ inst leader)
  intro h hw inst
  obtain ⟨t, u, k, hr, ht, hp, hout⟩ := hRun h hw
  exact ⟨t, u, some (k leader), hr, ht, _, hout, inst, leader, by rw [hp], rfl⟩

/-- When all lanes of the MMA warp are released at its election, they issue one full-mask batch. -/
theorem mma_election_batch {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} (hpre : Pre P L mem0) (hs : SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) (hub : ¬ HasUb X)
    (hall : ∀ h, SameWarp L g h → ∃ d, Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
      Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some (.mma d)) ∧
      d.site = .elect) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  refine full_election_batch (site := Wg1Mma.Site.elect.pc) hX (by rw [hpre.block]) hg ?_
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
    obtain ⟨k, hTemplate⟩ := mma_election_template ha hc hSite
    have hp : u.pc = Wg1Mma.Site.elect.pc := ha.1.trans (congrArg Wg1Mma.Site.pc hSite)
    rw [hTemplate] at hout
    exact ⟨t, u, k, hRun, hTau, hp, hout⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
