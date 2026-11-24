-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MaxWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierTrace
import Lemmas.Flow.Final

public section

/-! # The local maximum write, warpgroup barrier, and peer maximum read -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0MaxTrace

open PTX PTX.Flow PTX.Proof Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def previous : Wg0.Site → Option Wg0.Site
  | .rowMax => some (.peerRead 7)
  | .wg0Sync2 => some .rowMax
  | .validFree => some .wg0Sync2
  | .maxRead => some .validFree
  | .rescaleVote => some .maxRead
  | .lseBar2 => some .lseStore0
  | .lseRead => some .lseBar2
  | _ => none

set_option maxHeartbeats 1500000 in
private theorem role_prev {q d : D} {e : Event} {s : Wg0.Site}
    (hn : Wg0.next P L g q e = some (some d)) (h : previous d.site = some s) :
    q.site = s ∧ d.block = q.block ∧ (d.site ≠ .rowMax → d.scoreSums = q.scoreSums) := by
  cases hq : q.site <;>
    simp only [Wg0.next, nextSite, writeStep, waitStep, hq] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hmap
        simp only [withPeerMax, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr
        obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := hr
        simp_all [previous]
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      cases h
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [previous, afterScoreSite, afterLen, afterSink, epiAfterBar, loadScores, init]
  all_goals try (split_ifs at h)
  · subst s
    congr 1
    apply Fin.ext
    omega
  all_goals simp [Site.elems] at *

private theorem machine_prev {q : Machine.ThreadD} {d : D} {e : Event} {s : Wg0.Site}
    (hn : Machine.next P L g q e = some (some (.wg0 d))) (h : previous d.site = some s) :
    ∃ q0 : D, q = .wg0 q0 ∧ q0.site = s ∧ d.block = q0.block ∧
      (d.site ≠ .rowMax → d.scoreSums = q0.scoreSums) := by
  cases q with
  | wg0 q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i r hr
      cases hn
      exact ⟨q, rfl, role_prev hr h⟩
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
          unfold init firstSite afterSink afterLen at h
          split_ifs at h <;> cases h
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

private theorem previous_event {i : Nat} {d : D} {site : Wg0.Site}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : previous d.site = some site) :
    ∃ j e q u, j + 1 = i ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      q.site = site ∧ q.block = d.block ∧
      (Machine.machine P L g).Fired (some (.wg0 q)) e (some u) ∧
      (d.site ≠ .rowMax → d.scoreSums = q.scoreSums) := by
  cases i with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ j =>
    have hj : j < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hj⟩
    have hg := Frame.lt_of_get hX he
    obtain ⟨q, hσ⟩ := FollowedPrefix.state_at hd (Nat.le_succ j)
    rw [Frame.stateAt_succ he, hσ, Option.bind_some] at hd
    change Machine.next P L g q e = some (some (.wg0 d)) at hd
    obtain ⟨q0, rfl, hq, hb, hm⟩ := machine_prev hd hsite
    obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at he hσ
    cases o with
    | none => rw [composed_ending_next hf] at hd; cases hd
    | some u => exact ⟨j, e, q0, u, rfl, he, hσ, hq, hb.symm, hf, hm⟩

/-- The local maximum is written by the event immediately before the block's second barrier. -/
theorem rowMax_before_barrier {k : Nat} {d : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hg : g < L.threads)
    (hlen : k ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d)))
    (hsite : d.site = .wg0Sync2) :
    ∃ j q a, j + 1 = k ∧ q.site = .rowMax ∧ q.block = d.block ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      X.Writes (g, j) a (rowLocalMax L q).toBytes ∧ a.size = 4 ∧
      a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128)) := by
  have hprev : previous d.site = some .rowMax := by rw [hsite]; rfl
  obtain ⟨j, e, q, u, hj, he, hq, hqs, hblock, hf, _⟩ :=
    previous_event hX (hs g hg).machine hlen hd hprev
  obtain ⟨t, ins, ha, hinv, hcode, hFire⟩ := Frame.fired_site_of hs hg hf
  obtain ⟨a, hk, hloc, hz, _⟩ := fires_rowMax hpre hqs ha hinv hcode hFire
  refine ⟨j, q, a, hj, hqs, hblock, hq, ?_, hz, hloc⟩
  cases e
  exact ⟨_, he.trans (congrArg some (congrArg (Event.mk _) hk))⟩

/-- The actual peer maximum read follows the second barrier and the index-slot release. -/
theorem barrier_before_maxRead {i : Nat} {d : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hg : g < L.threads)
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .maxRead) :
    ∃ j q tag, j + 2 = i ∧ q.site = .wg0Sync2 ∧ q.block = d.block ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      X.IsBarrier (g, j) 9 (some 128) tag := by
  have hprev : previous d.site = some .validFree := by rw [hsite]; rfl
  obtain ⟨k, _, r, _, hk, _, hr, hrs, hblock, _, _⟩ :=
    previous_event hX (hs g hg).machine hlen hd hprev
  have hprev' : previous r.site = some .wg0Sync2 := by rw [hrs]; rfl
  obtain ⟨j, e, q, u, hj, he, hq, hqs, hb, hf, _⟩ :=
    previous_event hX (hs g hg).machine (by omega) hr hprev'
  have hbar := Wg0BarrierTrace.bar9_kind hpre hf (by
    rw [hqs]
    trivial)
  refine ⟨j, q, e.pc, by omega, hqs, hb.trans hblock, hq, ?_⟩
  cases e
  exact he.trans (congrArg some (congrArg (Event.mk _) hbar))

section
variable {i : Nat} {d : D} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hg : g < L.threads)
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
include hX hs hg hlen hd

/-- The final peer read immediately precedes the local maximum write. -/
theorem peer_before_rowMax (hsite : d.site = .rowMax) :
    ∃ j e q, j + 1 = i ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      q.site = .peerRead 7 := by
  have hprev : previous d.site = some (.peerRead 7) := by rw [hsite]; rfl
  obtain ⟨j, e, q, _, hj, he, hq, hs', _, _, _⟩ :=
    previous_event hX (hs g hg).machine hlen hd hprev
  exact ⟨j, e, q, hj, he, hq, hs'⟩

/-- The local maximum write and peer maximum read use the same completed score pairs. -/
theorem rowMax_state_before_maxRead (hsite : d.site = .maxRead) :
    ∃ j q, j + 3 = i ∧ Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      q.site = .rowMax ∧ q.block = d.block ∧ d.scoreSums = q.scoreSums := by
  have hprev : previous d.site = some .validFree := by rw [hsite]; rfl
  obtain ⟨j, _, q, _, hj, _, hq, hqs, hqb, _, hdm⟩ :=
    previous_event hX (hs g hg).machine hlen hd hprev
  have hprev : previous q.site = some .wg0Sync2 := by rw [hqs]; rfl
  obtain ⟨k, _, r, _, hk, _, hr, hrs, hrb, _, hqm⟩ :=
    previous_event hX (hs g hg).machine (by omega) hq hprev
  have hprev : previous r.site = some .rowMax := by rw [hrs]; rfl
  obtain ⟨w, _, t, _, hw, _, ht, hts, htb, _, hrm⟩ :=
    previous_event hX (hs g hg).machine (by omega) hr hprev
  exact ⟨w, t, by omega, ht, hts, htb.trans (hrb.trans hqb),
    (hdm (by simp [hsite])).trans ((hqm (by simp [hqs])).trans (hrm (by simp [hrs])))⟩

/-- The actual peer maximum read immediately precedes the reference vote. -/
theorem maxRead_before_vote (hsite : d.site = .rescaleVote) :
    ∃ j e q, j + 1 = i ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      q.site = .maxRead ∧ d.scoreSums = q.scoreSums := by
  have hprev : previous d.site = some .maxRead := by rw [hsite]; rfl
  obtain ⟨j, e, q, _, hj, he, hq, hs', _, _, hm⟩ :=
    previous_event hX (hs g hg).machine hlen hd hprev
  exact ⟨j, e, q, hj, he, hq, hs', hm (by simp [hsite])⟩
end

variable {i : Nat} {d : D} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hg : g < L.threads)
    (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
include hpre hX hs hg hlen hd

/-- The final half-sum write immediately precedes its publishing barrier. -/
theorem halfSum_before_barrier (hsite : d.site = .lseBar2) :
    ∃ j q a, j + 1 = i ∧ q.site = .lseStore0 ∧ q.block = d.block ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      X.Writes (g, j) a ((if q.peak = ⊥ then b32 0 else halfSumVal q).toBytes) ∧
      a.size = 4 ∧ a.loc = shLoc L g (rowMaxBase + 4 * (tidOf L g % 128)) := by
  have hprev : previous d.site = some .lseStore0 := by rw [hsite]; rfl
  obtain ⟨j, e, q, _, hj, he, hq, hqs, hb, hf, _⟩ :=
    previous_event hX (hs g hg).machine hlen hd hprev
  obtain ⟨_, _, ha, hinv, hcode, hFire⟩ := Frame.fired_site_of hs hg hf
  obtain ⟨a, hk, hloc, hsize, _⟩ := fires_lseStore0 hpre hqs ha hinv hcode hFire
  refine ⟨j, q, a, hj, hqs, hb, hq, ?_, hsize, hloc⟩
  cases e
  exact ⟨_, he.trans (congrArg some (congrArg (Event.mk _) hk))⟩

/-- The actual half-sum read immediately follows the final publication barrier. -/
theorem barrier_before_sumRead (hsite : d.site = .lseRead) :
    ∃ j q tag, j + 1 = i ∧ q.site = .lseBar2 ∧ q.block = d.block ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      X.IsBarrier (g, j) 9 (some 128) tag := by
  have hprev : previous d.site = some .lseBar2 := by rw [hsite]; rfl
  obtain ⟨j, e, q, _, hj, he, hq, hqs, hb, hf, _⟩ :=
    previous_event hX (hs g hg).machine hlen hd hprev
  have hbar := Wg0BarrierTrace.bar9_kind hpre hf (by rw [hqs]; trivial)
  refine ⟨j, q, e.pc, hj, hqs, hb, hq, ?_⟩
  cases e
  exact he.trans (congrArg some (congrArg (Event.mk _) hbar))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0MaxTrace
