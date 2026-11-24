-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingGateGeneration
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingInitSources

@[expose] public section

/-! # The actual prologue gate releases generation zero -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.CtaBarrier

private theorem perform_generation_succ {block id : Nat} {r : Record EvId} {s t : State}
    (h : r.perform block s = .ok t) :
    (t.slots id).generation ≤ (s.slots id).generation + 1 := by
  cases r with
  | exit g e =>
    by_cases hg : g < block ∧ g ∉ s.exited
    · simp [Record.perform, exitThread, hg, pure, Except.pure] at h
      cases h
      exact (settle_generation block (insert g s.exited) (s.slots id)).elim
        (fun he => by rw [he]; omega) (fun he => by rw [he])
    · simp [Record.perform, exitThread, hg, bind, Except.bind, pure, Except.pure, throw] at h
  | arrival target warp count lanes =>
    simp only [Record.perform] at h
    split_ifs at h
    obtain ⟨n, _, _, hslots⟩ := arrive_shape h
    rw [hslots]
    split
    · subst target
      have hh := settle_generation block s.exited
        {s.slots id with expected := some n, arrived := insert warp (s.slots id).arrived}
      dsimp only at hh
      exact hh.elim (fun he => by rw [he]; omega) (fun he => by rw [he])
    · omega

private theorem released_zero_of_positive {block id : Nat} {history : List (Record EvId)}
    {last : State} (hRun : CtaBarrier.run block {} history = .ok last)
    (hPos : 0 < (last.slots id).generation) : Released block history id 0 := by
  have steps {h : Nat} (hle : h ≤ history.length) (v : State) (hv : At block history h v)
      (hp : 0 < (v.slots id).generation) : Released block history id 0 := by
    induction h generalizing v with
    | zero =>
      change Except.ok ({} : State) = .ok v at hv
      cases hv
      cases hp
    | succ j ih =>
      have hlt : j < history.length := by omega
      let r := history[j]
      have hr : history[j]? = some r := List.getElem?_eq_getElem hlt
      obtain ⟨u, v', hu, hperform⟩ := run_at_record hRun hr
      have hEq : At block history (j + 1) v' := by
        unfold At at hu ⊢
        rw [List.take_add_one, hr, Option.toList_some, run_append, hu]
        simp [CtaBarrier.run, hperform, Except.bind]
      have hSame : v' = v := Except.ok.inj (hEq.symm.trans hv)
      subst v'
      rcases Nat.eq_zero_or_pos (u.slots id).generation with hzero | hpositive
      · have hone := perform_generation_succ (id := id) hperform
        rw [hzero] at hone
        exact ⟨j, r, u, v, hr, hu, hperform, hzero, by omega⟩
      · exact ih (by omega) u hu hpositive
  exact steps (Nat.le_refl _) last (by unfold At; simpa using hRun) hPos

private theorem gate_ordinal {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    {ev : Event} (he : X.get (g, i) = some ev)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier))) :
    ((X.tr g).take i).countP (Execution.isBarId 0) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e heMem
  cases hk : Execution.isBarId 0 e
  · decide
  obtain ⟨j, hj, hjElem⟩ := List.mem_iff_getElem.mp heMem
  have hji : j < i := by simp at hj; omega
  have hjlt : j < (X.tr g).length := by simp at hj; omega
  have hGet : X.get (g, j) = some e := by
    change (X.tr g)[j]? = some e
    rw [List.getElem?_eq_getElem hjlt]
    exact congrArg some (by simpa only [List.getElem_take] using hjElem)
  obtain ⟨q, hq⟩ := FollowedPrefix.state_at hd hji.le
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX hs hGet hq
  obtain ⟨_, _, _, hEvent⟩ := NamedBar.isBarId_form hk
  obtain ⟨rfl, _, _⟩ := RingGateEvents.gate_source hf (congrArg Event.kind hEvent)
  have := RingInitSources.gate_state_unique hGet he hq hd
  omega

/-- An actual launch gate is its thread's first barrier-zero arrival and leaves the prologue
at a role handoff. -/
theorem launch_arrival {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i tag : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.IsBarrier (g, i) 0 none tag) :
    ((X.tr g).take i).countP (Execution.isBarId 0) = 0 ∧
      ∃ w, Frame.stateAt (Machine.code P L) X g (i + 1) =
        some (some (.prologue (.handoff w))) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
  obtain ⟨rfl, _, _⟩ := RingGateEvents.gate_source hf rfl
  refine ⟨gate_ordinal hX (hs g hg).machine he hd, ?_⟩
  rw [Frame.stateAt_succ he, hd, Option.bind_some]
  change ∃ w, Machine.next P L g (.prologue .barrier) ⟨tag, .bar 0 none .sync⟩ =
    some (some (.prologue (.handoff w)))
  simp only [Machine.next, PTX.Kernels.FlashMlaSparseDecodeH64.Proof.next]
  split_ifs <;> exact ⟨_, rfl⟩

private instance : Fact kernel.NoBarArrive := ⟨by
  unfold Kernel.NoBarArrive
  decide +kernel⟩

/-- A real passed prologue gate has the actual resource key zero. Its generation need not
be read from an assumed classification of every barrier-zero event in the trace. -/
theorem passed_gate_zero {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some ⟨97, .bar 0 none .sync⟩)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier)))
    (hpassed : i + 1 < (X.tr g).length) :
    CtaBarK L X (g, i) 0 ∧ Released L.block (X.barriers (g / L.block)) 0 0 := by
  have hg := Frame.lt_of_get hX he
  have hc := NamedBar.cta_lt hg
  obtain ⟨key, hKey, hDone⟩ := ctaBarDone_of_returned hX he hpassed
  obtain ⟨_, _, hbar⟩ := hKey.2.1
  have hId := (Kind.bar.inj (Event.mk.inj (Option.some.inj (hbar.symm.trans he))).2).1
  have hRelease : Released L.block (X.barriers (g / L.block)) 0 0 := by
    by_cases hk : key / 16 = 0
    · simpa only [CtaBarDone, hId, hk] using hDone
    · obtain ⟨last, hlast⟩ := (hX.ctaBar.2 _ hc).2.2
      have hPos := released_generation_lt hlast hDone
      rw [hId] at hPos
      exact released_zero_of_positive hlast (by omega)
  refine ⟨?_, hRelease⟩
  have hOrd := gate_ordinal hX (hs g hg).machine he hd
  have hw : g % L.block / 32 ∈ Finset.range 12 := by
    rw [hpre.block]
    exact Finset.mem_range.mpr (by have := Nat.mod_lt g (by decide : 0 < 384); omega)
  have hbound : ∀ w ∈ Finset.range 12, w < L.block / 32 := by
    rw [hpre.block]
    exact fun w hw => Finset.mem_range.mp hw
  exact NamedBar.reached_key_of_release hX (by decide : 0 < 12)
    (by rw [hpre.block]; rfl) (by decide) he hg hw hOrd hRelease
    (fun i hi => zero_generation_protocol hpre hX hs hc hi) (by decide) hbound

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
