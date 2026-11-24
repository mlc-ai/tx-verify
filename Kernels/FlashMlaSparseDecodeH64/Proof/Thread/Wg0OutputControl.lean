-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierTrace
public import Lemmas.Flow.TraceInduction

@[expose] public section

/-! # Control flow of the output epilogue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0OutputControl

open PTX PTX.Flow Wg0

private def outputIssuer (L : Launch) (g : Nat) : Wg0.Site → Prop
  | .elect _ | .tmaStore _ => warpOf L g < 2
  | _ => True

private theorem outputIssuer_step {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hi : outputIssuer L g d.site) (hn : Wg0.next P L g d e = some (some d')) :
    outputIssuer L g d'.site := by
  cases hd : d.site <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        trivial
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      trivial
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [outputIssuer, Wg0.afterScoreSite, Wg0.afterLen, Wg0.afterSink,
    Wg0.epiAfterBar]
  all_goals split_ifs <;> simp_all

private def issuerRole (L : Launch) (g : Nat) : Option Machine.ThreadD → Prop
  | some (.wg0 d) => outputIssuer L g d.site
  | _ => True

variable {P : Params}

private theorem issuerRole_step {L : Launch} {g : Nat} {e : Event} {d d' : Option Machine.ThreadD}
    (hi : issuerRole L g d) (hn : (Machine.machine P L g).next d e = some d') :
    issuerRole L g d' := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn
            · simp only [issuerRole, Machine.roleStart, Wg0.init, Wg0.firstSite]
              split <;> simp [outputIssuer, Wg0.afterSink, Wg0.afterLen]
              all_goals split_ifs <;> trivial
            · trivial
            · trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> trivial
    case wg0 d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i _ hs
        cases hn
        exact outputIssuer_step hi hs
      · split_ifs at hn <;> cases hn <;> trivial
      · cases hn
    all_goals
      simp only [Machine.next] at hn
      repeat' split at hn
      all_goals cases hn
      all_goals trivial

/-- A thread at a TMA output state is in one of the two output warps. -/
theorem outputWarp {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {e : Event} {d : D}
    {j : Fin 4} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, k) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) (hj : d.site = .tmaStore j)
    : warpOf L g < 2 := by
  have h := (hs.produces (hX.thr g (Frame.lt_of_get hX he))).prefix_induction
    (fun q _ => issuerRole L g q) trivial (fun _ _ _ _ _ h _ => issuerRole_step h)
    k (some (.wg0 d)) hd
  simpa [issuerRole, outputIssuer, hj] using h

/-- A represented output election belongs to one of the two issuing warps. -/
theorem outputElectionWarp {L : Launch} {mem0 : Mem0} {X : Execution} {g k : Nat} {d : D}
    {j : Fin 4} (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d))) (hj : d.site = .elect j)
    : warpOf L g < 2 := by
  have h := (hs.produces (hX.thr g hg)).prefix_induction
    (fun q _ => issuerRole L g q) trivial (fun _ _ _ _ _ h _ => issuerRole_step h)
    k (some (.wg0 d)) hd
  simpa [issuerRole, outputIssuer, hj] using h

private def outputPredecessor : Wg0.Site → Option Wg0.Site
  | .epiBar j => some (.stageFence j)
  | .elect j => some (.epiBar j)
  | .tmaStore j => some (.elect j)
  | .everyone => some .commit
  | .exit => some .everyone
  | _ => none

private theorem prev_step {L : Launch} {g : Nat} {d d' : D} {e : Event} {s : Wg0.Site}
    (hn : Wg0.next P L g d e = some (some d')) (hp : outputPredecessor d'.site = some s)
    : d.site = s := by
  cases hd : d.site <;>
    simp only [Wg0.next, Wg0.nextSite, Wg0.writeStep, Wg0.waitStep, hd] at hn
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        cases hp
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
      cases hp
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp only [Wg0.afterScoreSite, Wg0.afterLen, Wg0.afterSink, Wg0.epiAfterBar,
      hd, outputPredecessor, Option.some.injEq] at hp
  all_goals try (split_ifs at hp)
  all_goals cases hp
  all_goals rfl

private theorem composed_prev {L : Launch} {g : Nat} {src : Machine.ThreadD} {d' : D} {e : Event}
    {s : Wg0.Site} (hn : Machine.next P L g src e = some (some (.wg0 d')))
    (hp : outputPredecessor d'.site = some s) :
    ∃ d, src = .wg0 d ∧ d.site = s := by
  cases src
  case prologue q =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          simp only [Wg0.init, Wg0.firstSite, Wg0.afterSink, Wg0.afterLen] at hp
          repeat' split at hp
          all_goals cases hp
        · cases hn
      · cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  case wg0 d =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i _ hs
      cases hn
      exact ⟨d, rfl, prev_step hs hp⟩
    · split_ifs at hn <;> cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

private theorem previous {L : Launch} {X : Execution} {g i : Nat} {d : D} {s : Wg0.Site}
    (hi : i ≤ (X.tr g).length)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hp : outputPredecessor d.site = some s) :
    ∃ k e d', k + 1 = i ∧ X.get (g, k) = some e ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d')) ∧ d'.site = s := by
  cases i with
  | zero =>
    rw [Frame.stateAt_zero] at hstate
    cases hstate
  | succ i =>
    have hik : i < (X.tr g).length := by omega
    have he : X.get (g, i) = some (X.tr g)[i] := List.getElem?_eq_getElem hik
    rw [Frame.stateAt_succ he] at hstate
    cases hprior : Frame.stateAt (Machine.code P L) X g i with
    | none =>
      rw [hprior] at hstate
      cases hstate
    | some q =>
      rw [hprior] at hstate
      cases q with
      | none => cases hstate
      | some q =>
        change Machine.next P L g q (X.tr g)[i] = some (some (.wg0 d)) at hstate
        obtain ⟨d', rfl, hd'⟩ := composed_prev hstate hp
        exact ⟨i, _, d', rfl, he, hprior, hd'⟩

/-- A lane at its output election has just arrived on the tile's staging barrier. -/
theorem barrierBeforeElection {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D}
    {j : Fin 4} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hi : i ≤ (X.tr g).length)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .elect j) :
    ∃ k e d', k + 1 = i ∧ X.get (g, k) = some e ∧ e.kind = .bar 9 (some 128) .sync ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d')) ∧ d'.site = .epiBar j := by
  obtain ⟨k, e, d', hk, he, hstate', hd'⟩ := previous hi hstate (by rw [hj]; rfl)
  obtain ⟨_, hf⟩ := (hs.produces (hX.thr g (Frame.lt_of_get hX he))).fired_at he hstate'
  refine ⟨k, e, d', hk, he, Wg0BarrierTrace.bar9_kind hpre hf ?_, hstate', hd'⟩
  rw [hd']
  trivial

/-- The issuer passes its tile's named barrier and elects before the issue. -/
theorem barrierBeforeIssue {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D}
    {j : Fin 4} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound) (hi : i < (X.tr g).length)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .tmaStore j) :
    ∃ k e d', k + 2 = i ∧ X.get (g, k) = some e ∧ e.kind = .bar 9 (some 128) .sync ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d')) ∧ d'.site = .epiBar j := by
  obtain ⟨m, _, md, hm, _, hmd, hme⟩ := previous hi.le hstate (by rw [hj]; rfl)
  obtain ⟨k, e, d', hk, he, hd', hdj⟩ := previous (by omega) hmd (by rw [hme]; rfl)
  obtain ⟨_, hf⟩ := (hs.produces (hX.thr g (Frame.lt_of_get hX he))).fired_at he hd'
  refine ⟨k, e, d', by omega, he, Wg0BarrierTrace.bar9_kind hpre hf ?_, hd', hdj⟩
  rw [hdj]
  trivial

/-- A writer arriving at a tile barrier has already fired that tile's staging proxy fence. -/
theorem fenceBeforeBarrier {L : Launch} {X : Execution} {g i : Nat} {d : D} {j : Fin 4}
    (hi : i < (X.tr g).length)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hj : d.site = .epiBar j) :
    ∃ k e d', k + 1 = i ∧ X.get (g, k) = some e ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.wg0 d')) ∧
      d'.site = .stageFence j :=
  previous hi.le hstate (by rw [hj]; rfl)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0OutputControl
