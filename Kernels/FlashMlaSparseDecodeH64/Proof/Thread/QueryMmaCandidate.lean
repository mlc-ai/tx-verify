-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MachineSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Clc.ClcExecution
import Lemmas.Flow.Elect
import Lemmas.Step.ExitLast

public section

/-! # The MMA lane selected by an actual election, or by the first extension -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryMmaCandidate

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g cta : Nat}

/-- The selected MMA lane can still be in the prologue, at warp dispatch, or in its MMA role. -/
inductive Active : Machine.ThreadD → Prop where
  | launch (s : Machine.PSite) : Active (.prologue s)
  | dispatch : Active .head
  | mma (d : Wg1Mma.D) : Active (.mma d)

/-- An actual warp-4 full-mask election has supplied the CTA's MMA leader. -/
def ElectionSeen (L : Launch) (X : Execution) (cta : Nat) : Prop :=
  ∃ w i tag inst leader, ctaOf L w = cta ∧ warpOf L w = 4 ∧
    X.Elect (w, i) tag 4294967295 inst leader

/-- The candidate lies in warp 4 of its launched CTA and has the selected lane index. -/
theorem lane_geometry (hpre : Pre P L mem0) (hc : cta < L.grid) (lane : Fin 32) :
    let g := cta * L.block + 128 + lane.val
    g < L.threads ∧ ctaOf L g = cta ∧ warpOf L g = 4 ∧ PTX.laneOf L g = lane.val := by
  dsimp only
  have hLane := lane.isLt
  have hg : cta * L.block + 128 + lane.val < L.threads := by
    change _ < L.grid * L.block
    rw [hpre.block]
    omega
  refine ⟨hg, ?_, ?_, ?_⟩
  · unfold ctaOf
    rw [hpre.block]
    omega
  · rw [warpOf, tidOf_eq hpre, hpre.block]
    omega
  · rw [PTX.laneOf, hpre.block]
    omega

variable (hpre : Pre P L mem0)
include hpre

private theorem same_warp {g h : Nat} (hg : g < L.threads) (hh : h < L.threads)
    (hc : ctaOf L g = ctaOf L h) (hwg : warpOf L g = 4) (hwh : warpOf L h = 4) :
    SameWarp L g h :=
  ⟨⟨hg, hh, hc⟩, by simpa only [warpOf, tidOf_eq hpre, hpre.block] using hwg.trans hwh.symm⟩

private theorem chosen_lane (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∃ lane : Fin 32, (¬ ElectionSeen L X cta → lane = 0) ∧
      ∀ w i tag inst leader, ctaOf L w = cta → warpOf L w = 4 →
        X.Elect (w, i) tag 4294967295 inst leader → leader = lane.val := by
  by_cases hSeen : ElectionSeen L X cta
  · obtain ⟨w, i, tag, inst, leader, hCta, hWarp, he⟩ := hSeen
    have hL := (hX.elect.1 _ _ _ _ _ he).2.2.1
    refine ⟨⟨leader, hL⟩, fun h => (h ⟨w, i, tag, inst, leader, hCta, hWarp, he⟩).elim, ?_⟩
    intro w' i' tag' inst' l hc hw he'
    exact hX.elect.deterministic he' he (same_warp hpre
      (Frame.lt_of_get hX he') (Frame.lt_of_get hX he) (hc.trans hCta.symm) hw hWarp)
  · exact ⟨0, fun _ => rfl, fun w i tag inst leader hc hw he =>
      (hSeen ⟨w, i, tag, inst, leader, hc, hw, he⟩).elim⟩

private theorem active_next (hWarp : warpOf L g = 4) {old next : Machine.ThreadD} {i : Nat}
    {e : Event} {o : Option TState} (hActive : Active old) (he : X.get (g, i) = some e)
    (hf : (Machine.machine P L g).Fired (some old) e o)
    (hChosen : ∀ j tag inst leader, X.Elect (g, j) tag 4294967295 inst leader →
      leader = PTX.laneOf L g) (hn : Machine.next P L g old e = some (some next)) :
    Active next ∨ next = .done ∧ e.kind = .exit := by
  cases hActive with
  | launch s =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
      exact .inl (.launch _)
    · split at hn
      · rename_i w _
        have hg : wgOf L g = 1 := by
          unfold wgOf
          unfold warpOf at hWarp
          omega
        rw [hg] at hn
        split_ifs at hn with hw
        · have hW : w = 1 := Fin.ext hw.symm
          subst w
          cases hn
          exact .inl .dispatch
        · cases hn
      · cases hn
    · cases hn
  | dispatch =>
    cases hKind : e.kind <;> simp only [Machine.next, hKind, reduceCtorEq] at hn
    rw [Machine.headStart_eq4 hWarp] at hn
    split at hn
    · cases hn
      exact .inl (.mma _)
    · cases hn
  | mma d =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
      exact .inl (.mma _)
    · rename_i hNext
      split_ifs at hn with hSite
      · have hNo : False := by
          cases hKind : e.kind <;> simp only [Wg1Mma.next, hSite, hKind, reduceCtorEq] at hNext
          rename_i mask inst leader
          have hMask := Wg1MmaLeader.full_mask hSite hf hKind
          have hElect : X.Elect (g, i) e.pc 4294967295 inst leader := by
            change X.get (g, i) = some ⟨e.pc, .elect 4294967295 inst leader⟩
            rw [he, ← hMask, ← hKind]
          have hl := hChosen i e.pc inst leader hElect
          rw [laneOf_core hpre] at hl
          simp [hl] at hNext
        exact hNo.elim
      · cases hn
    · split_ifs at hn with hSite
      cases hn
      obtain ⟨t, ⟨_, _⟩, hF⟩ := hf
      change Fires t.pc (match kernel.code[d.site.pc]? with
        | some ins => eventTmpl Assumptions.all L g t ins.op
        | none => .ub .pcOutOfRange) e o at hF
      have hCode : kernel.code[d.site.pc]? = some ⟨none, .ret⟩ := by
        rw [hSite]
        exact Flow.code_exit_0
      rw [hCode] at hF
      exact .inr ⟨rfl, congrArg Event.kind hF.1⟩

private theorem active_or_done (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hg : g < L.threads) (hWarp : warpOf L g = 4)
    (hChosen : ∀ j tag inst leader, X.Elect (g, j) tag 4294967295 inst leader →
      leader = PTX.laneOf L g) {i : Nat} {d : Machine.ThreadD} (hi : i ≤ (X.tr g).length)
    (hσ : Frame.stateAt (Machine.code P L) X g i = some (some d)) :
    Active d ∨ d = .done ∧ ∃ j < i, ∃ tag, X.get (g, j) = some ⟨tag, .exit⟩ := by
  induction i generalizing d with
  | zero =>
    rw [Frame.stateAt_zero] at hσ
    cases hσ
    exact .inl (.launch _)
  | succ i ih =>
    let e := (X.tr g)[i]
    have he : X.get (g, i) = some e := List.getElem?_eq_getElem hi
    rw [Frame.stateAt_succ he] at hσ
    obtain ⟨prev, hp, hn⟩ := Option.bind_eq_some_iff.mp hσ
    cases prev with
    | none => cases hn
    | some q =>
      rcases ih (Nat.le_of_succ_le hi) hp with hActive | ⟨rfl, _⟩
      · obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at he hp
        rcases active_next hpre hWarp hActive he hf hChosen hn with h | ⟨rfl, hExit⟩
        · exact .inl h
        · have heq : e = ⟨e.pc, .exit⟩ := by
            cases hEvent : e with
            | mk tag kind =>
              rw [hEvent] at hExit
              change kind = .exit at hExit
              subst kind
              rfl
          exact .inr ⟨rfl, i, Nat.lt_succ_self _, e.pc, he.trans (congrArg some heq)⟩
      · cases hn

private theorem select_core (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hLive : ∀ g, Frame.Pending L X g →
      ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d)) (hc : cta < L.grid)
    :
    ∃ lane : Fin 32,
      let g := cta * L.block + 128 + lane.val
      (¬ ElectionSeen L X cta → lane = 0) ∧
      (∀ w i d, ctaOf L w = cta →
        Frame.stateAt (Machine.code P L) X w i = some (some (.mma d)) →
        d.site ≠ .elect → w = g) ∧
      (∀ j tag inst leader, X.Elect (g, j) tag 4294967295 inst leader →
        leader = PTX.laneOf L g) ∧
      ((∃ i tag, X.get (g, i) = some ⟨tag, .exit⟩) ∨
        ∃ d, Frame.Pending L X g ∧
          Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d) ∧ Active d) := by
  obtain ⟨lane, hZero, hChoose⟩ := chosen_lane (cta := cta) hpre hX
  let g := cta * L.block + 128 + lane.val
  obtain ⟨hg, hCta, hWarp, hLane⟩ := lane_geometry hpre hc lane
  have hSelected : ∀ j tag inst w, X.Elect (g, j) tag 4294967295 inst w →
      w = PTX.laneOf L g := by
    intro j tag inst w he
    exact (hChoose g j tag inst w hCta hWarp he).trans hLane.symm
  refine ⟨lane, hZero, ?_, hSelected, ?_⟩
  · intro w i d hc' hσ hd
    obtain ⟨hWarp', k, _, ev, inst, he, hElect⟩ :=
      Wg1MmaLeader.body_elected hpre hX (fun w hw => (hs w hw).machine) hσ hd
    have ha : X.Elect (w, k) ev.pc 4294967295 inst (PTX.laneOf L w) := by
      change X.get (w, k) = some ⟨ev.pc, .elect 4294967295 inst (PTX.laneOf L w)⟩
      rw [he, ← hElect]
    have hLane' := hChoose w k ev.pc inst _ hc' hWarp' ha
    unfold warpOf at hWarp'
    rw [tidOf_eq hpre] at hWarp'
    unfold ctaOf at hc'
    unfold PTX.laneOf at hLane'
    change w = cta * L.block + 128 + lane.val
    rw [hpre.block] at hc' hLane' ⊢
    omega
  · by_cases hExit : ∃ i tag, X.get (g, i) = some ⟨tag, .exit⟩
    · exact .inl hExit
    · have hp : Frame.Pending L X g := by
        refine ⟨hg, ?_, ?_⟩
        · rintro ⟨_, _, hCanceled⟩
          obtain ⟨i, sp, targets, _, hi, _⟩ := hX.clc.canceled_has_issue hCanceled
          exact GlobalWrites.no_clc (i := i) (s := sp) (tg := targets) hX hi
        · intro tag he
          rw [List.getLast?_eq_getElem?] at he
          exact hExit ⟨_, tag, he⟩
      obtain ⟨d, hσ⟩ := hLive g hp
      rcases active_or_done hpre hX (hs g hg).machine hg hWarp hSelected le_rfl hσ with h | ⟨_, hx⟩
      · exact .inr ⟨d, hp, hσ, h⟩
      · obtain ⟨j, _, tag, he⟩ := hx
        exact (hExit ⟨j, tag, he⟩).elim

/-- Before any election, lane zero is a candidate. Otherwise the actual full-mask election
selects the candidate, and the same lane owns all followed MMA body states in the CTA. -/
theorem select (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hLive : ∀ g, Frame.Pending L X g →
      ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d)) (hc : cta < L.grid)
    :
    ∃ lane : Fin 32,
      let g := cta * L.block + 128 + lane.val
      (¬ ElectionSeen L X cta → lane = 0) ∧
      (∀ w i d, ctaOf L w = cta →
        Frame.stateAt (Machine.code P L) X w i = some (some (.mma d)) →
        d.site ≠ .elect → w = g) ∧
      ((∃ i tag, X.get (g, i) = some ⟨tag, .exit⟩) ∨
        ∃ d, Frame.Pending L X g ∧
          Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d) ∧ Active d) := by
  obtain ⟨lane, hZero, hOwner, _, hTail⟩ := select_core hpre hX hs hLive hc
  exact ⟨lane, hZero, hOwner, hTail⟩

/-- If the selected lane has exited, its actual return site is the MMA role's exit. -/
theorem select_mma (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hLive : ∀ g, Frame.Pending L X g →
      ∃ d, Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d)) (hc : cta < L.grid)
    :
    ∃ lane : Fin 32,
      let g := cta * L.block + 128 + lane.val
      (¬ ElectionSeen L X cta → lane = 0) ∧
      (∀ w i d, ctaOf L w = cta →
        Frame.stateAt (Machine.code P L) X w i = some (some (.mma d)) →
        d.site ≠ .elect → w = g) ∧
      ((∃ i tag d, X.get (g, i) = some ⟨tag, .exit⟩ ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧ d.site = .exit) ∨
        ∃ d, Frame.Pending L X g ∧
          Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some d) ∧ Active d) := by
  obtain ⟨lane, hZero, hOwner, hChoice, hTail⟩ := select_core hpre hX hs hLive hc
  refine ⟨lane, hZero, hOwner, ?_⟩
  rcases hTail with ⟨i, tag, he⟩ | hPending
  · obtain ⟨d, hState, hAfter⟩ := ClosingOrder.return_state hX hs ht he
    obtain ⟨hg, _, hWarp, _⟩ := lane_geometry hpre hc lane
    rcases active_or_done hpre hX (hs _ hg).machine hg hWarp hChoice
      (PTX.len_of_get he).le hState with hActive | ⟨_, j, hj, _, hePrev⟩
    · cases hActive with
      | launch _ => cases hAfter
      | dispatch => cases hAfter
      | mma q => exact .inl ⟨i, tag, q, he, hState, hAfter⟩
    · have hLast := Execution.exit_last hX hg he
      have hLast' := Execution.exit_last hX hg hePrev
      omega
  · exact .inr hPending

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryMmaCandidate
