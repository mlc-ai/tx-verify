-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Flow.TraceInduction
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # Probability writes before the softmax epilogue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ProbabilityHistory

open PTX PTX.Flow Wg0

private def afterProbability : Wg0.Site → Prop
  | .rescaleFence | .rescaleLoad _ | .rescaleWait _ | .rescaleStore _ | .rescaleWaitSt _
  | .rescaleFenceB | .soFence | .soReady | .lseBar | .lseStore0 | .lseBar2 | .lseRead
  | .lseStore | .svDone | .fenceEpilogue | .oLoad _ | .oWait _ | .oStage _ _
  | .stageFence _ | .epiBar _ | .elect _ | .tmaStore _ | .commit | .everyone | .exit => True
  | _ => False

private theorem init_not_afterProbability (P : Params) (L : Launch) (g : Nat) :
    ¬ afterProbability (Wg0.init P L g).site := by
  unfold Wg0.init Wg0.firstSite Wg0.afterSink Wg0.afterLen
  dsimp only
  split_ifs <;> exact id

set_option maxHeartbeats 3000000 in
private theorem step_afterProbability {P : Params} {L : Launch} {g : Nat}
    {d d' : Wg0.D} {e : Event} (hn : Wg0.next P L g d e = some (some d'))
    (hd' : afterProbability d'.site) :
    d'.block = d.block ∧
      (afterProbability d.site ∨
        (d.site = .pStore 3 ∧ 4 ≤ d.sub + 1 ∧ ∃ a bs, e.kind = .wr a bs)) := by
  cases hd : d.site <;>
    simp only [Wg0.next, nextSite, writeStep, waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hm
        exact (hd' : False).elim
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hm⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hm
      exact (hd' : False).elim
    · cases hn
  case pStore k =>
    by_cases h : k.val + 1 < 4
    · simp only [h, dite_true] at hn
      split at hn <;> try cases hn
      repeat' split at hn
      all_goals cases hn
      all_goals exact (hd' : False).elim
    · have hk : k = 3 := Fin.ext (by have := k.isLt; omega)
      simp only [h, dite_false] at hn
      split at hn <;> try cases hn
      rename_i a bs he
      split at hn <;> try cases hn
      split at hn
      · cases hn
        exact (hd' : False).elim
      · rename_i hs
        split at hn <;> cases hn
        all_goals
          exact ⟨rfl, .inr ⟨congrArg Site.pStore hk, by simpa [Site.elems] using hs, _, _, he⟩⟩
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp_all [afterProbability, Wg0.init, firstSite, afterSink, afterLen, afterScoreSite,
      epiAfterBar, loadOutput]
  all_goals split_ifs at hd' <;> exact hd'

private def priorWrite (P : Params) (L : Launch) (g : Nat) (es : List Event) (block : Nat) : Prop :=
  ∃ j < es.length, ∃ (d : Wg0.D) (e : Event),
    (Machine.machine P L g).after (Machine.machine P L g).init (es.take j) =
      some (some (.wg0 d)) ∧ d.block = block ∧ d.site = .pStore 3 ∧ 4 ≤ d.sub + 1 ∧
    es[j]? = some e ∧ ∃ a bs, e.kind = .wr a bs

private theorem priorWrite_snoc {P : Params} {L : Launch} {g block : Nat}
    {es : List Event} {e : Event} (h : priorWrite P L g es block) :
    priorWrite P L g (es ++ [e]) block := by
  obtain ⟨j, hj, d, ev, hstate, hblock, hsite, hsub, he, hwrite⟩ := h
  refine ⟨j, by simp; omega, d, ev, ?_, hblock, hsite, hsub, ?_, hwrite⟩
  · simpa only [List.take_append_of_le_length hj.le] using hstate
  · simpa only [List.getElem?_append_left hj] using he

private def history (P : Params) (L : Launch) (g : Nat) (d : Option Machine.ThreadD)
    (es : List Event) : Prop :=
  (Machine.machine P L g).after (Machine.machine P L g).init es = some d ∧
    match d with
    | some (.wg0 state) => afterProbability state.site → priorWrite P L g es state.block
    | _ => True

private theorem history_step {P : Params} {L : Launch} {g : Nat}
    {d d' : Option Machine.ThreadD} {es : List Event} {e : Event}
    (h : history P L g d es) (hn : (Machine.machine P L g).next d e = some d') :
    history P L g d' (es ++ [e]) := by
  have hafter := h.1
  refine ⟨?_, ?_⟩
  · rw [PTX.Flow.Machine.after_snoc, hafter]
    exact hn
  cases d' with
  | none => trivial
  | some role =>
    cases role <;> try trivial
    rename_i state
    intro hmark
    cases d with
    | none =>
      change (some none : Option (Option Machine.ThreadD)) = some (some (.wg0 state)) at hn
      cases hn
    | some old =>
      change Machine.next P L g old e = some (some (.wg0 state)) at hn
      cases old
      case wg0 before =>
        simp only [Machine.next] at hn
        split at hn
        · rename_i q hnext
          cases hn
          have hprev : afterProbability before.site → priorWrite P L g es before.block := h.2
          obtain ⟨hblock, hfrom | ⟨hsite, hsub, hwr⟩⟩ := step_afterProbability hnext hmark
          · exact hblock ▸ priorWrite_snoc (hprev hfrom)
          · refine ⟨es.length, ?_, before, e, ?_, hblock.symm, hsite, hsub, ?_, hwr⟩
            · simp
            · rw [List.take_left]
              exact h.1
            · simp
        · split at hn <;> cases hn
        · cases hn
      case prologue before =>
        simp only [Machine.next] at hn
        split at hn
        · cases hn
        · split at hn
          · rename_i w _
            split at hn
            · fin_cases w <;> cases hn
              exact (init_not_afterProbability P L g hmark).elim
            · cases hn
          · cases hn
        · cases hn
      case head =>
        simp only [Machine.next] at hn
        repeat' split at hn
        all_goals try contradiction
        all_goals rename_i heq
        all_goals cases hn
        all_goals unfold Machine.headStart at heq
        all_goals repeat' split at heq
        all_goals cases heq
      all_goals
        simp only [Machine.next] at hn
        repeat' split at hn
        all_goals cases hn

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {out : Wg0.D}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 out)))
include hX hg hs hstate

private theorem last_before_marked (hmark : afterProbability out.site) :
    ∃ j < i, ∃ (d : Wg0.D) (e : Event),
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧
      d.block = out.block ∧ d.site = .pStore 3 ∧ 4 ≤ d.sub + 1 ∧
      X.get (g, j) = some e ∧
      ∃ a bs, e.kind = .wr a bs := by
  have hrec := (hs.produces (hX.thr g hg)).prefix_induction (history P L g)
    ⟨rfl, trivial⟩ (fun _ _ _ _ _ h _ hn => history_step h hn) i _ hstate
  obtain ⟨j, hj, d, e, hs', hblock, hsite, hsub, he, hwrite⟩ := hrec.2 hmark
  have hji : j < i := by simp only [List.length_take] at hj; omega
  refine ⟨j, hji, d, e, ?_, hblock, hsite, hsub, ?_, hwrite⟩
  · change (Machine.machine P L g).after (Machine.machine P L g).init
      ((X.tr g).take j) = some (some (.wg0 d))
    simpa only [List.take_take, Nat.min_eq_left hji.le] using hs'
  · simpa only [List.getElem?_take, ite_eq_left hji, Execution.get, Prod.fst, Prod.snd] using he

private theorem before_marked (hmark : afterProbability out.site) :
    ∃ j < i, ∃ (d : Wg0.D) (k : Fin 4) (e : Event),
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧
      d.block = out.block ∧ d.site = .pStore k ∧ X.get (g, j) = some e ∧
      ∃ a bs, e.kind = .wr a bs := by
  obtain ⟨j, hj, d, e, hstate', hb, hsite, _, he, hw⟩ :=
    last_before_marked hX hg hs hstate hmark
  exact ⟨j, hj, d, 3, e, hstate', hb, hsite, he, hw⟩

/-- The probability fence has the last packed probability store of its block in its prefix. -/
theorem last_before_fence (hsite : out.site = .soFence) :
    ∃ j < i, ∃ (d : Wg0.D) (e : Event),
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧
      d.block = out.block ∧ d.site = .pStore 3 ∧ 4 ≤ d.sub + 1 ∧
      X.get (g, j) = some e ∧ ∃ a bs, e.kind = .wr a bs :=
  last_before_marked hX hg hs hstate (by rw [hsite]; trivial)

omit hX hg hs hstate in
/-- At every followed output TMA site, the same lane has issued a probability write of the
block carried by that output state. The output invariant identifies that block as the last one. -/
theorem before_output {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {out : Wg0.D} {tile : Fin 4}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 out)))
    (htile : out.site = .tmaStore tile) :
    ∃ j < i, ∃ (d : Wg0.D) (k : Fin 4) (e : Event),
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧
      d.block = out.block ∧ d.site = .pStore k ∧ X.get (g, j) = some e ∧
      ∃ a bs, e.kind = .wr a bs :=
  before_marked hX hg hs hstate (by rw [htile]; trivial)

omit hX hg hs hstate in
/-- Each staging write follows a probability write of the final block in its lane. -/
theorem before_stage {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {out : Wg0.D} {tile : Fin 4} {chunk : Fin 8}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 out)))
    (htile : out.site = .oStage tile chunk) :
    ∃ j < i, ∃ (d : Wg0.D) (k : Fin 4) (e : Event),
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧
      d.block = out.block ∧ d.site = .pStore k ∧ X.get (g, j) = some e ∧
      ∃ a bs, e.kind = .wr a bs :=
  before_marked hX hg hs hstate (by rw [htile]; trivial)

/-- The actual final PV wait follows a probability write of that same block in its lane. -/
theorem before_pv_wait (hwait : out.site = .svDone) :
    ∃ j < i, ∃ (d : Wg0.D) (k : Fin 4) (e : Event),
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)) ∧
      d.block = out.block ∧ d.site = .pStore k ∧ X.get (g, j) = some e ∧
      ∃ a bs, e.kind = .wr a bs :=
  before_marked hX hg hs hstate (by rw [hwait]; trivial)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ProbabilityHistory
