-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputControl
import Lemmas.Flow.Recip

@[expose] public section

/-! # A rescale store retains the words of its tile's actual load -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def RescaleStep (q d : D) (e : Event) (tile : Fin 4) : Prop :=
  (d.site = .rescaleWait tile ∧ q.site = .rescaleLoad tile ∧
    ∃ address shape, e.kind = .tc (.ld address d.rescaleWords shape)) ∨
  (d.site = .rescaleStore tile ∧ q.site = .rescaleWait tile ∧
    d.rescaleWords = q.rescaleWords ∧ e.kind = .tc .waitLd)

set_option maxHeartbeats 1200000 in
private theorem rescale_prev {q d : D} {e : Event} {tile : Fin 4}
    (hn : Wg0.next P L g q e = some (some d))
    (hsite : d.site = .rescaleWait tile ∨ d.site = .rescaleStore tile) :
    d.block = q.block ∧ d.gainWord = q.gainWord ∧ RescaleStep q d e tile := by
  cases hq : q.site <;> simp only [Wg0.next, nextSite, writeStep, waitStep, hq] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        simp at hsite
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      simp at hsite
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [afterScoreSite, afterLen, afterSink, epiAfterBar, loadScores, init,
    RescaleStep]
  all_goals try (split_ifs at hsite; contradiction)
  all_goals aesop

private theorem composed_rescale_prev {d : D} {e : Event} {q : Machine.ThreadD} {tile : Fin 4}
    (hn : Machine.next P L g q e = some (some (.wg0 d)))
    (hsite : d.site = .rescaleWait tile ∨ d.site = .rescaleStore tile) :
    ∃ prev : D, q = .wg0 prev ∧ d.block = prev.block ∧ d.gainWord = prev.gainWord ∧
      RescaleStep prev d e tile := by
  cases q with
  | wg0 q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i d' hh
      cases hn
      exact ⟨q, rfl, rescale_prev hh hsite⟩
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
          unfold init firstSite afterSink afterLen at hsite
          split_ifs at hsite <;> simp at hsite
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

private theorem previous_rescale {i : Nat} {d : D} {tile : Fin 4}
    (hBound : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleWait tile ∨ d.site = .rescaleStore tile) :
    ∃ j q e, j + 1 = i ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      d.block = q.block ∧ d.gainWord = q.gainWord ∧ RescaleStep q d e tile := by
  cases i with
  | zero =>
    rw [Frame.stateAt_zero] at hd
    cases hd
  | succ j =>
    have hLt : j < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e :=
      ⟨_, List.getElem?_eq_getElem hLt⟩
    obtain ⟨q, hq⟩ := FollowedPrefix.state_at hd (show j ≤ j + 1 by omega)
    rw [Frame.stateAt_succ he, hq, Option.bind_some] at hd
    obtain ⟨prev, rfl, hBlock, hGain, hStep⟩ := composed_rescale_prev hd hsite
    exact ⟨j, prev, e, rfl, he, hq, hBlock, hGain, hStep⟩

/-- The store's retained input is the actual 64-word return of the preceding tile load. -/
theorem rescale_load_of_store {i : Nat} {d : D} {tile : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hBound : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleStore tile) :
    ∃ j q waitState waitTag,
      j + 2 = i ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      q.site = .rescaleLoad tile ∧ q.block = d.block ∧ q.gainWord = d.gainWord ∧
      X.TLd (g, j) (64 * tile.val) d.rescaleWords .s32x32b ∧
      Frame.stateAt (Machine.code P L) X g (j + 1) = some (some (.wg0 waitState)) ∧
      X.get (g, j + 1) = some ⟨waitTag, .tc .waitLd⟩ ∧
      waitState.site = .rescaleWait tile ∧ waitState.block = d.block ∧
      waitState.rescaleWords = d.rescaleWords ∧ d.rescaleWords.length = 64 := by
  obtain ⟨w, waitState, e, hw, he, hWait, hDblock, hDgain, hStep⟩ :=
    previous_rescale hBound hd (.inr hsite)
  rcases hStep with ⟨hbad, _⟩ | ⟨_, hWaitSite, hWords, hWaitKind⟩
  · rw [hsite] at hbad
    cases hbad
  obtain ⟨j, q, ev, hj, hget, hLoad, hQblock, hQgain, hRead⟩ :=
    previous_rescale (by omega) hWait (.inl hWaitSite)
  rcases hRead with ⟨_, hLoadSite, address, shape, hKind⟩ | ⟨hbad, _⟩
  · obtain ⟨t, ins, u, ha, _, hc, hf⟩ := Frame.fired_site hs hX hget hLoad
    cases u with
    | none =>
      rcases fires_none_ends hf with ⟨_, hk⟩ | hk <;> rw [hKind] at hk <;> cases hk
    | some u =>
      obtain ⟨words, hLen, hsKind, _⟩ := fires_rescaleLoad hpre hLoadSite ha hc hf
      have hWordsEq : waitState.rescaleWords = words := by
        cases hKind.symm.trans hsKind
        rfl
      have hInput := hWords.trans hWordsEq
      refine ⟨j, q, waitState, e.pc, by omega, hLoad, hLoadSite,
        hQblock.symm.trans hDblock.symm, hQgain.symm.trans hDgain.symm, ?_, ?_, ?_,
        hWaitSite, hDblock.symm, hWords.symm, hInput ▸ hLen⟩
      · rw [hInput]
        obtain ⟨tag, kind⟩ := ev
        change kind = _ at hsKind
        exact ⟨tag, by rw [hget, hsKind]⟩
      · rw [hj]
        exact hWait
      · rw [hj]
        obtain ⟨tag, kind⟩ := e
        change kind = _ at hWaitKind
        rw [he, hWaitKind]
  · rw [hWaitSite] at hbad
    cases hbad

/-- A component of the actual rescale store is its retained input multiplied by the gain. -/
theorem rescale_store_value {i : Nat} {d : D} {tile : Fin 4} (k : Fin 64) {x gain : ℝ}
    (hstore : X.TSt (g, i) (64 * tile.val) (rescaleStoreValues d) .s32x32b)
    (hWord : d.rescaleWords[k.val]? = some (.float .f32 x))
    (hGain : valFloat .f32 d.gainWord = .ok gain) :
    TcMma.StoreValue L X (g, i) (tcDataCell L g .s32x32b (64 * tile.val) k.val)
      (.float .f32 (x * gain)) := by
  refine ⟨_, _, _, _, hstore, ?_, rfl⟩
  have hRange : (List.range 64)[k.val]? = some k.val := List.getElem?_range k.isLt
  rw [rescaleStoreValues, List.getElem?_map, hRange, Option.map_some]
  simp only [rescaleValue, outputReal, List.getD_eq_getElem?_getD, hWord, Option.getD_some,
    hGain, valFloat_float, Except.toOption, fl]

/-- A covered rescale cell uses the matching register of the same tile's load. -/
theorem rescale_cell_payload {i : Nat} {d : D} {tile : Fin 4} {cell : TcMma.Cell}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleStore tile)
    (hstore : X.TSt (g, i) (64 * tile.val) (rescaleStoreValues d) .s32x32b)
    (hCover : TcMma.StoreCell L X (g, i) cell) :
    ∃ (ld : Nat) (q waitState : D) (waitTag : Nat) (k : Fin 64),
      ld + 2 = i ∧
      Frame.stateAt (Machine.code P L) X g ld = some (some (.wg0 q)) ∧
      q.site = .rescaleLoad tile ∧ q.block = d.block ∧
      X.TLd (g, ld) (64 * tile.val) d.rescaleWords .s32x32b ∧
      TcMma.LoadCell L X (g, ld) k.val cell ∧
      cell = tcDataCell L g .s32x32b (64 * tile.val) k.val ∧
      Frame.stateAt (Machine.code P L) X g (ld + 1) = some (some (.wg0 waitState)) ∧
      X.get (g, ld + 1) = some ⟨waitTag, .tc .waitLd⟩ ∧
      waitState.site = .rescaleWait tile ∧ waitState.block = d.block ∧
      waitState.rescaleWords = d.rescaleWords ∧
      ∀ (x gain : ℝ), d.rescaleWords[k.val]? = some (.float .f32 x) →
        valFloat .f32 d.gainWord = .ok gain →
        TcMma.StoreValue L X (g, i) cell (.float .f32 (x * gain)) := by
  obtain ⟨ld, q, waitState, tag, hLd, hState, hLoad, hBlock, _, hRead, hWait, hWaitEv,
    hWaitSite, hWaitBlock, hWords, hLen⟩ :=
    rescale_load_of_store hpre hX hs (PTX.len_of_get hstore.choose_spec).le hd hsite
  obtain ⟨addr, words, shape, j, hStore', hj, hCell⟩ := hCover
  have hKind := congrArg Event.kind
    (Option.some.inj (hStore'.choose_spec.symm.trans hstore.choose_spec))
  obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hKind)
  have hj64 : j < 64 := by
    simpa only [rescaleStoreValues, List.length_map, List.length_range] using hj
  let k : Fin 64 := ⟨j, hj64⟩
  refine ⟨ld, q, waitState, tag, k, hLd, hState, hLoad, hBlock, hRead, ?_, hCell,
    hWait, hWaitEv, hWaitSite, hWaitBlock, hWords, ?_⟩
  · exact ⟨_, _, _, hRead, by rw [hLen]; exact hj64, hCell⟩
  · intro x gain hWord hGain
    rw [hCell]
    exact rescale_store_value k hstore hWord hGain

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
