-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
public import Lemmas.Kernel.Frame
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # The rescale stores preceding a probability publication -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0RescaleRelease

open PTX PTX.Flow PTX.Proof Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def afterTile (tile : Fin 4) : Wg0.Site → Prop
  | .rescaleWaitSt j => tile.val ≤ j.val
  | .rescaleLoad j | .rescaleWait j | .rescaleStore j => tile.val < j.val
  | .rescaleFenceB | .soFence | .soReady => True
  | _ => False

private def Predecessor (tile : Fin 4) (q d : D) : Prop :=
  q.block = d.block ∧ wantsRescale q = true ∧
    (afterTile tile q.site ∨ q.site = .rescaleStore tile)

set_option maxHeartbeats 1750000 in
private theorem role_previous {q d : D} {e : Event} {tile : Fin 4}
    (hn : Wg0.next P L g q e = some (some d))
    (hAfter : afterTile tile d.site) (hRescale : wantsRescale d = true) :
    Predecessor tile q d := by
  cases hq : q.site <;> simp only [Wg0.next, nextSite, writeStep, waitStep, hq] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        cases hAfter
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      cases hAfter
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [Predecessor, afterTile, afterScoreSite, afterLen, afterSink, epiAfterBar,
    loadScores, init, wantsRescale]
  all_goals try (split_ifs at hAfter <;> contradiction)
  all_goals omega

private theorem composed_previous {q : Machine.ThreadD} {d : D} {e : Event} {tile : Fin 4}
    (hn : Machine.next P L g q e = some (some (.wg0 d)))
    (hAfter : afterTile tile d.site) (hRescale : wantsRescale d = true) :
    ∃ prev : D, q = .wg0 prev ∧ Predecessor tile prev d := by
  cases q with
  | wg0 q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i _ hnext
      cases hn
      exact ⟨q, rfl, role_previous hnext hAfter hRescale⟩
    · split_ifs at hn <;> cases hn
    · cases hn
  | prologue q =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          unfold init firstSite afterSink afterLen at hAfter
          split_ifs at hAfter <;> cases hAfter
        · cases hn
      · cases hn
    · cases hn
  | head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  | _ =>
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

private theorem store_before_afterTile {i : Nat} {d : D} (tile : Fin 4)
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hAfter : afterTile tile d.site) (hRescale : wantsRescale d = true) :
    ∃ j < i, ∃ q e, X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      q.block = d.block ∧ q.site = .rescaleStore tile := by
  cases i with
  | zero =>
    rw [Frame.stateAt_zero] at hd
    cases hd
  | succ j =>
    have hj : j < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨q, hq⟩ := FollowedPrefix.state_at hd (Nat.le_succ j)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hq] at hn
    obtain ⟨before, rfl, hBlock, hTaken, hPrevious | hStore⟩ :=
      composed_previous hn.symm hAfter hRescale
    · obtain ⟨l, hli, s, f, hf, hs, hb, hStore⟩ :=
        store_before_afterTile tile hj.le hq hPrevious hTaken
      exact ⟨l, by omega, s, f, hf, hs, hb.trans hBlock, hStore⟩
    · exact ⟨j, Nat.lt_succ_self j, before, e, he, hq, hBlock, hStore⟩
termination_by i

/-- If the vote selected rescaling in a later block, each tile was stored before publication. -/
theorem store_before_publication {i : Nat} {d : D} (tile : Fin 4)
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .soReady) (hRescale : wantsRescale d = true) :
    ∃ j < i, ∃ q e, X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      q.block = d.block ∧ q.site = .rescaleStore tile :=
  store_before_afterTile tile hlen hd (by rw [hsite]; trivial) hRescale

/-- The earlier rescale store is the actual 64-word tensor-memory store. -/
theorem tensor_store_before_publication {i : Nat} {d : D} {e : Event} (tile : Fin 4)
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .soReady) (hRescale : wantsRescale d = true) :
    ∃ j < i, ∃ q,
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      q.block = d.block ∧ q.site = .rescaleStore tile ∧
      X.TSt (g, j) (64 * tile.val) (rescaleStoreValues q) .s32x32b := by
  obtain ⟨j, hji, q, ev, hev, hq, hqBlock, hqSite⟩ :=
    store_before_publication tile (PTX.len_of_get he).le hd hsite hRescale
  obtain ⟨t, ins, u, ha, _, hc, hf⟩ := Frame.fired_site hs hX hev hq
  cases u with
  | none =>
    have hg := Frame.lt_of_get hX hev
    obtain ⟨_, hrun⟩ := hX.thr g hg
    have hEnd := fires_none_ends hf
    have hj : j + 1 = (X.tr g).length := Run.end_last hrun hev hEnd
    have hi : i < (X.tr g).length := PTX.len_of_get he
    omega
  | some u =>
    obtain ⟨hKind, _⟩ := fires_rescaleStore hpre hqSite ha hc hf
    obtain ⟨tag, kind⟩ := ev
    change kind = _ at hKind
    rw [hKind] at hev
    exact ⟨j, hji, q, hq, hqBlock, hqSite, tag, hev⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0RescaleRelease
