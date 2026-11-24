-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AllocReadbackOrder
public import Lemmas.Flow.Final
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueRoleTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NcInputTrace
import Lemmas.Flow.Alloc

public section

/-! # Continuations of the actual launch and dispatch events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbPrologue

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Actual returned prologue events preserve a represented control state. -/
theorem prologue_next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hResources : ¬ Tmem.Pair.ResourceUnsafe L X)
    {g i : Nat} {e : Event} {s : Site} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue s)))
    (hReturns : ¬ Ends e) : Machine.next P L g (.prologue s) e ≠ none := by
  have hlen := (PTX.len_of_get he).le
  cases s
  case shfl0 =>
    obtain rfl := PrologueRoleTrace.first_shuffle_position hlen hd
    rw [PrologueShuffleTrace.first_event hpre hX (fun g hg => (hs g hg).machine) he]
    simp [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, b32]
  case shfl1 =>
    obtain rfl := PrologueRoleTrace.second_shuffle_position hlen hd
    rw [PrologueShuffleTrace.second_event hpre hX (fun g hg => (hs g hg).machine) he]
    simp [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next, b32]
  case elect0 =>
    obtain ⟨_, ins, o, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0)
    cases o with
    | none => exact (hReturns (fires_none_ends hf)).elim
    | some u =>
      obtain ⟨_, _, _, rfl, _⟩ := fires_elect hf
      simp [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next]
  case elect1 =>
    obtain ⟨_, ins, o, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1)
    cases o with
    | none => exact (hReturns (fires_none_ends hf)).elim
    | some u =>
      obtain ⟨_, _, _, rfl, _⟩ := fires_elect hf
      simp [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next]
  case alloc =>
    obtain ⟨t, ins, o, ha, _, hc, hf⟩ := Frame.fired_site hs hX he hd
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    cases o with
    | none => exact (hReturns (fires_none_ends hf)).elim
    | some u =>
      have hsub : t.sub = 0 := ha.2.1
      obtain ⟨_, _, rfl, _⟩ := fires_tcAlloc hsub hf
      simp [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next]
  case allocRead =>
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, PrologueAllocation.readback_relinquishes hpre hX hs ht hResources he hd] at hn
    change _ = Machine.next P L g (.prologue .allocRead) e at hn
    rw [← hn]
    exact Option.some_ne_none _
  all_goals simp [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next]

/-- The actual dispatch shuffle continues at the selected role. -/
theorem head_next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {g i : Nat} {e : Event} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some .head)) :
    Machine.next P L g .head e ≠ none := by
  have hn := Frame.stateAt_succ (C := Machine.code P L) he
  rw [hd, (PrologueRoleTrace.dispatch hpre hX (fun g hg => (hs g hg).machine) he hd).2] at hn
  change _ = Machine.next P L g .head e at hn
  rw [← hn]
  exact Option.some_ne_none _

/-- The optional idle length load obtains its initialized word and continues. -/
theorem idle_length_next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {g i : Nat} {s : Thread.Site} {e : Event} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.idle s)))
    (hSite : s = .loadTopk ∨ s = .loadExtra) : Machine.next P L g (.idle s) e ≠ none := by
  obtain ⟨_, _, hs', hRead⟩ := NcInputTrace.idle_length_event hpre hX hs he hd hSite
  have hb := Wg1Mma.eOf_lt_b (g := g) hpre
  rcases hs' with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
  · have hr := LaunchReads.rebuild_main (g := g) hpre hX hb hp he hRead
    simp [Machine.next, Thread.next, hRead.1, hr]
  · have hr := LaunchReads.rebuild_extra (g := g) hpre hX hb hp he hRead
    simp [Machine.next, Thread.next, hRead.1, hr]

/-- The returned idle CTA barrier continues to the final return. -/
theorem idle_sync_next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {g i : Nat} {e : Event} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.idle .sync))) :
    Machine.next P L g (.idle .sync) e ≠ none := by
  obtain ⟨t, ins, o, ha, _, hc, hf⟩ := Frame.fired_site hs hX he hd
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_14)
  have hm := Thread.event_sync (L := L) (g := g) (t := t) ha hpre.block
  rw [hm] at hf
  obtain ⟨rfl, _⟩ := hf
  simp [Machine.next, Thread.next]

/-- The terminal machine site emits an exit, so a returned event cannot come from it. -/
theorem done_ends (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) {g i : Nat} {e : Event}
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some .done)) : Ends e := by
  obtain ⟨_, ins, _, _, _, hc, hf⟩ := Frame.fired_site hs hX he hd
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
  obtain ⟨rfl, _⟩ := hf
  exact .inr rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbPrologue
