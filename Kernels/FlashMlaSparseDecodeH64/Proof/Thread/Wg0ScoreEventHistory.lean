-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents

@[expose] public section

/-! # The two actual waits surrounding the score loads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ScoreEventHistory

open PTX.Flow Wg0

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def phase : Wg0.Site → Option Nat
  | .qkDone => some 0
  | .fenceLoad => some 1
  | .scoreLoad _ k => some (2 + k.val)
  | .scoreWait => some 4
  | .fenceBefore => some 5
  | .maskRead => some 6
  | _ => none

set_option maxHeartbeats 1500000 in
private theorem role_predecessor {n : Nat} {q d : D} {e : Event}
    (hn : Wg0.next P L g q e = some (some d))
    (hd : phase d.site = some (n + 1)) : phase q.site = some n ∧ q.block = d.block := by
  cases hq : q.site <;> cases hk : e.kind <;>
    simp only [Wg0.next, nextSite, hq, hk, waitStep, writeStep, reduceCtorEq] at hn
  case qkDone.wait =>
    split at hn <;> cases hn <;> simp_all [phase]
  case fenceLoad.tc =>
    split at hn <;> cases hn
    simp_all [phase]
  case scoreLoad.tc a k tc =>
    have hkBound := k.isLt
    split at hn
    · split at hn
      · cases hn
        simp only [afterScoreSite] at hd
        have hb (ws : List Value) : (loadScores q (a.val == k.val) ws).block = q.block := by
          unfold loadScores
          split <;> rfl
        split at hd <;> simp only [phase, Option.some.injEq] at hd ⊢
        all_goals exact ⟨by omega, (hb _).symm⟩
      · cases hn
    · cases hn
  case scoreWait.tc =>
    split at hn <;> cases hn
    simp_all [phase]
  case fenceBefore.tc =>
    split at hn <;> cases hn
    simp_all [phase]
  case maxRead.rd =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      simp [phase] at hd
    · cases hn
  case rescaleVote.voteMode =>
    obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
    simp [phase] at hd
  all_goals repeat' split at hn
  all_goals try (simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals cases hn
  all_goals try (simp only [afterSink, afterLen, epiAfterBar] at hd)
  all_goals try split_ifs at hd
  all_goals simp [phase, hq] at hd

private theorem machine_predecessor {n : Nat} {q : Machine.ThreadD} {d : D} {e : Event}
    (hn : Machine.next P L g q e = some (some (.wg0 d)))
    (hd : phase d.site = some (n + 1)) :
    ∃ s, q = .wg0 s ∧ phase s.site = some n ∧ s.block = d.block := by
  cases q
  case wg0 s =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i s' hnext
      cases hn
      exact ⟨s, rfl, role_predecessor hnext hd⟩
    · split at hn <;> cases hn
    · cases hn
  case prologue st =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          change phase (firstSite P) = some (n + 1) at hd
          simp only [firstSite, afterSink, afterLen] at hd
          split_ifs at hd <;> simp [phase] at hd
        · cases hn
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

private theorem prior_phase {j n rank : Nat} {d : D}
    (hbound : j ≤ (X.tr g).length)
    (hs : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hphase : phase d.site = some (rank + n)) :
    ∃ i q, i + n = j ∧ phase q.site = some rank ∧ q.block = d.block ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 q)) := by
  induction n generalizing j d with
  | zero => exact ⟨j, d, rfl, hphase, rfl, hs⟩
  | succ n ih =>
    cases j with
    | zero => rw [Frame.stateAt_zero] at hs; cases hs
    | succ j =>
      have hj : j < (X.tr g).length := by omega
      have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
      rw [Frame.stateAt_succ (C := Machine.code P L) he] at hs
      cases hp : Frame.stateAt (Machine.code P L) X g j with
      | none => simp [hp] at hs
      | some s =>
        cases s with
        | none => simp [hp] at hs; cases hs
        | some s =>
          rw [hp, Option.bind_some] at hs
          obtain ⟨q, rfl, hq, hb⟩ := machine_predecessor hs hphase
          obtain ⟨i, t, hi, ht, hiBlock, hstate⟩ := ih hj.le hp hq
          exact ⟨i, t, by omega, ht, hiBlock.trans hb, hstate⟩

/-- An actual score load follows the successful QK acquire of its block. -/
theorem qk_wait_before_score_load {i : Nat} {d : D} {arm part : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .scoreLoad arm part) (hbound : i ≤ (X.tr g).length) :
    ∃ w q tag scope, w < i ∧
      Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)) ∧
      q.site = .qkDone ∧ q.block = d.block ∧
      X.get (g, w) = some ⟨tag, .wait
        ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff (q.block % 2)⟩
        (q.block / 2 % 2) true true scope⟩ := by
  have hp : phase d.site = some (2 + part.val) := by rw [hsite]; rfl
  obtain ⟨w, q, hw, hq, hb, hqState⟩ :=
    prior_phase (rank := 0) (n := 2 + part.val) hbound hstate (by simpa using hp)
  obtain ⟨f, entry, hf, hentry, _, heState⟩ :=
    prior_phase (rank := 1) (n := 1 + part.val) hbound hstate (by
      rw [hp, Option.some.injEq]
      omega)
  have hqSite : q.site = .qkDone := by
    cases hn : q.site <;> simp [phase, hn] at hq ⊢
  have heSite : entry.site = .fenceLoad := by
    cases hn : entry.site <;> simp [phase, hn] at hentry ⊢
    omega
  have hfEq : f = w + 1 := by omega
  subst f
  have hwl : w < (X.tr g).length := by omega
  obtain ⟨e, hget⟩ : ∃ e, X.get (g, w) = some e := ⟨_, List.getElem?_eq_getElem hwl⟩
  obtain ⟨_, hfire⟩ := (Frame.trace hs hX (Frame.lt_of_get hX hget)).fired_at hget hqState
  obtain ⟨ok, scope, hKind⟩ := RingEvents.gemmDone_wait_exact hpre (.inl hqSite) hfire
  simp only [hqSite, ↓reduceIte] at hKind
  have hok : ok = true := by
    have he' := heState
    rw [Frame.stateAt_succ hget, hqState, Option.bind_some] at he'
    change Machine.next P L g (.wg0 q) e = some (some (.wg0 entry)) at he'
    cases ok <;> simp only [Machine.next, Wg0.next, Wg0.nextSite, hqSite, hKind,
      waitStep, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Machine.ThreadD.wg0.injEq]
      at he' ⊢
    subst entry
    rw [hqSite] at heSite
    cases heSite
  subst ok
  exact ⟨w, q, e.pc, scope, by omega, hqState, hqSite, hb,
    hget.trans (congrArg some (congrArg (Event.mk e.pc) hKind))⟩

/-- A visit to the mask read exposes the actual successful QK wait before the two loads,
the actual wait for those loads, and the first post-acquire event of the same block. -/
theorem waits_of_mask {j : Nat} {d : D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hstate : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 d)))
    (hsite : d.site = .maskRead) (hbound : j ≤ (X.tr g).length) :
    ∃ w qall entry sw qtag ltag scope, w + 6 = j ∧
      Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 qall)) ∧
      qall.site = .qkDone ∧ qall.block = d.block ∧
      X.get (g, w) = some ⟨qtag, .wait
        ⟨.shared, ctaOf L g, L.sharedBase + Wg0.qkDoneOff (d.block % 2)⟩
        (d.block / 2 % 2) true true scope⟩ ∧
      Frame.stateAt (Machine.code P L) X g (w + 1) = some (some (.wg0 entry)) ∧
      entry.site = .fenceLoad ∧ entry.block = d.block ∧
      Frame.stateAt (Machine.code P L) X g (w + 4) = some (some (.wg0 sw)) ∧
      sw.site = .scoreWait ∧ sw.block = d.block ∧
      X.get (g, w + 4) = some ⟨ltag, .tc .waitLd⟩ := by
  have hp : phase d.site = some 6 := by rw [hsite]; rfl
  obtain ⟨w, qall, hw, hq, hbq, hqall⟩ := prior_phase (rank := 0) (n := 6) hbound hstate hp
  obtain ⟨f, entry, hf, hentry, hbe, he⟩ := prior_phase (rank := 1) (n := 5) hbound hstate hp
  obtain ⟨k, sw, hk, hsw, hbs, hwait⟩ := prior_phase (rank := 4) (n := 2) hbound hstate hp
  have hqSite : qall.site = .qkDone := by
    cases hn : qall.site <;> simp [phase, hn] at hq ⊢
  have heSite : entry.site = .fenceLoad := by
    cases hn : entry.site <;> simp [phase, hn] at hentry ⊢
    omega
  have hsSite : sw.site = .scoreWait := by
    cases hn : sw.site <;> simp [phase, hn] at hsw ⊢
    have := ‹Fin 2›.isLt
    omega
  have hfEq : f = w + 1 := by omega
  have hkEq : k = w + 4 := by omega
  subst f k
  have hwl : w < (X.tr g).length := by omega
  have hkl : w + 4 < (X.tr g).length := by omega
  obtain ⟨e, hget⟩ : ∃ e, X.get (g, w) = some e := ⟨_, List.getElem?_eq_getElem hwl⟩
  obtain ⟨v, hgetK⟩ : ∃ v, X.get (g, w + 4) = some v := ⟨_, List.getElem?_eq_getElem hkl⟩
  obtain ⟨_, hfire⟩ := (Frame.trace hs hX (Frame.lt_of_get hX hget)).fired_at hget hqall
  obtain ⟨ok, scope, hqKind⟩ := RingEvents.gemmDone_wait_exact hpre (.inl hqSite) hfire
  simp only [hqSite, ↓reduceIte] at hqKind
  have hok : ok = true := by
    have he' := he
    rw [Frame.stateAt_succ hget, hqall, Option.bind_some] at he'
    change Machine.next P L g (.wg0 qall) e = some (some (.wg0 entry)) at he'
    cases ok <;> simp only [Machine.next, Wg0.next, Wg0.nextSite, hqSite, hqKind,
      waitStep, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Machine.ThreadD.wg0.injEq]
      at he' ⊢
    subst entry
    rw [hqSite] at heSite
    cases heSite
  subst ok
  obtain ⟨t, ins, o, _, _, hc, hl⟩ := Frame.fired_site hs hX hgetK hwait
  change kernel.code[sw.site.pc]? = some ins at hc
  change Fires sw.site.pc (eventTmpl Assumptions.all L g t ins.op) v o at hl
  have hp : sw.site.pc = 286 := by rw [hsSite]; rfl
  rw [hp] at hc hl
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_286)
  have ht : eventTmpl Assumptions.all L g t .tcWaitLd = .tc .waitLd (PTX.next t) := by
    simp [eventTmpl, tcTmpl, hpre.block, ofExec, pure, Except.pure]
  rw [ht] at hl
  refine ⟨w, qall, entry, sw, e.pc, 286, scope, hw, hqall, hqSite, hbq,
    ?_, he, heSite, hbe, hwait, hsSite, hbs, ?_⟩
  · rw [hget, ← hbq]
    change some e = some ⟨e.pc, .wait ⟨.shared, g / L.block, _⟩ _ true true scope⟩
    exact congrArg some (congrArg (Event.mk e.pc) hqKind)
  · exact hgetK.trans (congrArg some hl.1)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ScoreEventHistory
