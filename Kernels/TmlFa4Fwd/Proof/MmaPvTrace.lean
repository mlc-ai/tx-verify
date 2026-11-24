-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaWaitCursor
public import Kernels.TmlFa4Fwd.Proof.MmaPvOperands
public import Kernels.TmlFa4Fwd.Proof.MmaPoll
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The four PV copies all wait for the tail publication between fragments 5 and 6. -/
def pvTailWait : Fin 4 → Fin 14
  | 0 => 5
  | 1 => 8
  | 2 => 11
  | 3 => 13

def pvTailAddress (l : Launch) (block : Fin 4) : Nat :=
  l.sharedBase + 112 + 8 * (pvSite block).stage.val

/-- Every non-elected lane skips this fragment without recording an event. -/
theorem pvSkip {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (block : Fin 4) (step : Fin 8) (ht : At t (pvPc block step) F)
    (hGuard : t.regs (pvSite block).guard = some (.pred false)) :
    Tau kernel Assumptions.all l g t (next t) := by
  have hRange := pvRange block step
  have hCode := pvCode block step
  rw [← ht.1] at hCode
  have hFalse : guardHolds t (some ((pvSite block).guard, false)) = .ok false := by
    simp [guardHolds, readReg, hGuard, bind, Except.bind, pure, Except.pure]
  unfold Tau
  rw [out_eq_core (by rw [ht.1]; exact hRange.1) (by rw [ht.1]; exact hRange.2)]
  simp only [out, ht.2.2.2.1, hCode, hFalse]
  have hSub := ht.2.1
  have hAcc := ht.2.2.1
  simp [skip, next, hSub, hAcc]

/-- A PV fragment consumes an issue event precisely when the decoded election selected the lane.
Both the issue edge and the skip edge retain the same register frame. -/
theorem pvFragmentCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos : Nat} (hg : g < l.threads) (block : Fin 4) (step : Fin 8)
    (use : Nat) (accumulated lead : Bool) {t : TState} {F : List (Nat × Value)}
    (ht : At t (pvPc block step) F)
    (hPred : t.regs (pvSite block).guard = some (.pred lead))
    (hFacts : lead = true → Holds t.regs (pvIssueFacts l block step use accumulated))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    (lead = true → X.get (g, pos) = some (pvIssueEvent l g block step use accumulated)) ∧
      At (next t) (pvPc block step + 1) F ∧
      Run kernel Assumptions.all l g (next t)
        ((X.tr g).drop (pos + if lead then 1 else 0)) none := by
  cases lead
  · exact ⟨fun h => Bool.noConfusion h, ht.next,
      hr.after_local (.single (pvSkip block step ht hPred))⟩
  · obtain ⟨he, hRun⟩ := pvIssueAt hp hg block step use accumulated (ht.mono (hFacts rfl)) hr
    exact ⟨fun _ => he, ht.next, hRun⟩

/-- Initial scalar state carried unchanged between the eight issue sites of one PV block. -/
def pvCarry (l : Launch) (block : Fin 4) (use phase : Nat) (accumulated lead : Bool) :
    List (Nat × Value) :=
  let s := pvSite block
  [(s.guard, .pred lead), (s.dst, b32 (outputColumn s.stage)),
    (s.a, b32 (probabilityColumn s.stage)),
    (s.id, b32 0x8210490), (s.enable, .pred accumulated),
    (s.b - 3, b32 (kvStart l use / 16 + 67108864)),
    (s.b - 1, b32 0x40004040),
    ((waitSite (pvTailWait block)).base, b32 (pvTailAddress l block)),
    ((waitSite (pvTailWait block)).phase, b32 phase)]

private theorem pvCarryFresh (l : Launch) (block : Fin 4) (use phase : Nat)
    (accumulated lead : Bool) :
    ∀ pair ∈ pvCarry l block use phase accumulated lead,
      pair.1 ≠ (pvSite block).b - 2 ∧ pair.1 ≠ (pvSite block).b ∧
        pair.1 ≠ (waitSite (pvTailWait block)).result := by
  intro pair hm
  simp only [pvCarry, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases block <;> exact of_decide_eq_true rfl

def pvLow (l : Launch) (use : Nat) (step : Fin 8) : Nat :=
  kvStart l use / 16 + 67108864 + 128 * step.val

private theorem pvWord {l : Launch} (use : Nat) (step : Fin 8) :
    sharedDescriptorWord (kvStart l use + pvFragment step) 16384 =
      pvLow l use step + 2 ^ 32 * 0x40004040 := by
  unfold sharedDescriptorWord pvFragment pvLow
  omega

/-- The packed B descriptor is joined with the unchanged scalar frame at an issue site. -/
def pvIssueFrame (l : Launch) (block : Fin 4) (use phase : Nat) (accumulated lead : Bool)
    (step : Fin 8) : List (Nat × Value) :=
  [((pvSite block).b, b64 (sharedDescriptorWord (kvStart l use + pvFragment step) 16384))] ++
    ((if step.val = 0 then [] else [((pvSite block).b - 2, b32 (pvLow l use step))]) ++
      pvCarry l block use phase accumulated lead)

/-- Recover the issue operands from the framed descriptor cursor. -/
theorem pvFrameOperands {l : Launch} {t : TState} (block : Fin 4) (use phase : Nat)
    (accumulated lead : Bool) (step : Fin 8)
    (h : Holds t.regs (pvIssueFrame l block use phase accumulated lead step)) :
    t.regs (pvSite block).guard = some (.pred lead) ∧
      (lead = true → Holds t.regs (pvIssueFacts l block step use accumulated)) := by
  have hB := ((holds_append ..).mp h).1.1
  have hF : Holds t.regs (pvCarry l block use phase accumulated lead) :=
    ((holds_append ..).mp ((holds_append ..).mp h).2).2
  refine ⟨hF.1, ?_⟩
  intro hTrue
  exact ⟨hTrue ▸ hF.1, hF.2.1, hF.2.2.1, hB, hF.2.2.2.1, hF.2.2.2.2.1, trivial⟩

/-- At an already assembled PV fragment, the exact issue event is observed on the leader. -/
theorem pvFramedCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos : Nat} (hg : g < l.threads) (block : Fin 4) (step : Fin 8)
    (use phase : Nat) (accumulated lead : Bool) {t : TState}
    (ht : At t (pvPc block step) (pvIssueFrame l block use phase accumulated lead step))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    (lead = true → X.get (g, pos) = some (pvIssueEvent l g block step use accumulated)) ∧
      At (next t) (pvPc block step + 1) (pvIssueFrame l block use phase accumulated lead step) ∧
      Run kernel Assumptions.all l g (next t)
        ((X.tr g).drop (pos + if lead then 1 else 0)) none := by
  obtain ⟨hPred, hFacts⟩ := pvFrameOperands block use phase accumulated lead step ht.2.2.2.2
  exact pvFragmentCursor hp hg block step use accumulated lead ht hPred hFacts hr

def pvPrev (j : Fin 7) : Fin 8 := ⟨j.val, by have := j.isLt; omega⟩
def pvNext (j : Fin 7) : Fin 8 := ⟨j.val + 1, by have := j.isLt; omega⟩

/-- The two descriptor operations follow each fragment, after the optional tail wait. -/
theorem pvGap (block : Fin 4) (j : Fin 7) :
    if j.val = 5 then
      pvPc block (pvPrev j) + 1 = (waitSite (pvTailWait block)).pc ∧
        (waitSite (pvTailWait block)).pc + 3 = pvAdvancePc block j - 2
    else pvPc block (pvPrev j) + 1 = pvAdvancePc block j - 2 := by
  fin_cases block <;> fin_cases j <;> decide

/-- The descriptor frame excludes the acquire predicate written by the tail wait. -/
theorem pvBlockFrameTail {l : Launch} (block : Fin 4) (use phase : Nat)
    (accumulated lead : Bool) (step : Fin 8) :
    ∀ pair ∈ pvIssueFrame l block use phase accumulated lead step,
      pair.1 ≠ (waitSite (pvTailWait block)).result := by
  intro pair hm
  simp only [pvIssueFrame, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hm
  rcases hm with rfl | hm | hm
  · fin_cases block <;> exact of_decide_eq_true rfl
  · by_cases h : step.val = 0
    · simp [h] at hm
    · simp only [ite_eq_right h, List.mem_singleton] at hm
      subst pair
      fin_cases block <;> exact of_decide_eq_true rfl
  · exact (pvCarryFresh l block use phase accumulated lead pair hm).2.2

/-- Assemble the next fragment after any intervening acquire has returned. -/
theorem pvAdvanceLocalFramed {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (block : Fin 4) (j : Fin 7) (use phase : Nat) (accumulated lead : Bool)
    {extra : List (Nat × Value)}
    (hExtra : ∀ pair ∈ extra, pair.1 ≠ (pvSite block).b-2 ∧ pair.1 ≠ (pvSite block).b)
    {v : TState} (hv : At v (pvAdvancePc block j - 2)
      (pvIssueFrame l block use phase accumulated lead (pvPrev j) ++ extra)) :
    ∃ u, At u (pvPc block (pvNext j))
        (pvIssueFrame l block use phase accumulated lead (pvNext j) ++ extra) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) v u := by
  let F := pvCarry l block use phase accumulated lead
  have hOuter := (holds_append ..).mp hv.2.2.2.2
  have hKeep := hv.mono hOuter.1
  let site := pvSite block
  let old := if j.val < 5 then kvStart l use / 16 + 67108864 else pvLow l use (pvPrev j)
  have hf : Holds v.regs F :=
    ((holds_append ..).mp ((holds_append ..).mp hKeep.2.2.2.2).2).2
  have hLo : v.regs (pvAdvanceLowSrc block j) = some (b32 old) := by
    by_cases h : j.val < 5
    · simp only [pvAdvanceLowSrc, old, ite_eq_left h]
      exact hf.2.2.2.2.2.1
    · simp only [pvAdvanceLowSrc, old, ite_eq_right h]
      have hn : (pvPrev j).val ≠ 0 := by change j.val ≠ 0; omega
      have hLow := ((holds_append ..).mp ((holds_append ..).mp hKeep.2.2.2.2).2).1
      exact (show Holds v.regs [(site.b - 2, b32 (pvLow l use (pvPrev j)))] from
        by simpa only [ite_eq_right hn] using hLow).1
  have hHigh : v.regs (site.b - 1) = some (b32 0x40004040) := hf.2.2.2.2.2.2.1
  have hBound := hp.shared.2.1
  have hSlot : kvSlot use < 3 := Nat.mod_lt _ (by decide)
  have hj := j.isLt
  have hLowEq : old + pvAdvanceLowOffset j = pvLow l use (pvNext j) := by
    by_cases h : j.val < 5 <;>
      (simp only [old, pvAdvanceLowOffset, pvLow, pvPrev, pvNext, h, ↓reduceIte]
       try omega)
  have hLowBound : old + pvAdvanceLowOffset j < 2 ^ 32 := by
    rw [hLowEq]
    unfold pvLow pvNext kvStart
    omega
  have hInput : At v (pvAdvancePc block j - 2)
      ((pvAdvanceLowSrc block j, b32 old) :: (site.b - 1, b32 0x40004040) :: (F ++ extra)) :=
    hv.mono ⟨hLo, hHigh, (holds_append ..).mpr ⟨hf,hOuter.2⟩⟩
  obtain ⟨u, hLocal, hu⟩ := pvNextDescriptorFramed l g block j hLowBound
    (fun pair hm => by
      rcases List.mem_append.mp hm with hf | he
      · exact ⟨(pvCarryFresh l block use phase accumulated lead _ hf).1,
          (pvCarryFresh l block use phase accumulated lead _ hf).2.1⟩
      · exact hExtra pair he) v hInput
  have hU : At u (pvPc block (pvNext j))
      (pvIssueFrame l block use phase accumulated lead (pvNext j) ++ extra) :=
    hu.mono (by
      have hNZ : (pvNext j).val ≠ 0 := Nat.succ_ne_zero _
      simp only [pvIssueFrame, hNZ, ↓reduceIte, List.cons_append, List.nil_append, pvWord]
      have hLowFact := hu.2.2.2.2.1
      have hWordFact := hu.2.2.2.2.2.1
      rw [hLowEq] at hLowFact hWordFact
      exact ⟨hWordFact, hLowFact, hu.2.2.2.2.2.2⟩)
  exact ⟨u,hU,run_rtg hLocal⟩

/-- Assemble the next fragment after any intervening acquire has returned. -/
theorem pvAdvanceLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (block : Fin 4) (j : Fin 7) (use phase : Nat) (accumulated lead : Bool)
    {v : TState} (hv : At v (pvAdvancePc block j - 2)
      (pvIssueFrame l block use phase accumulated lead (pvPrev j))) :
    ∃ u, At u (pvPc block (pvNext j)) (pvIssueFrame l block use phase accumulated lead (pvNext j)) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) v u := by
  simpa only [List.append_nil] using pvAdvanceLocalFramed hp (g := g) block j use phase
    accumulated lead (extra := []) (by simp) (by simpa only [List.append_nil] using hv)

/-- Between consecutive PV issues the V word advances, including after the actual tail wait.
The resulting trace position accounts for each attempt of the tail acquire. -/
theorem pvAdvanceCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos : Nat} (block : Fin 4) (j : Fin 7)
    (use phase : Nat) (accumulated lead : Bool) (hPhase : phase < 2) {t : TState}
    (ht : At t (pvPc block (pvPrev j) + 1)
      (pvIssueFrame l block use phase accumulated lead (pvPrev j)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ n u, (j.val ≠ 5 → n = 0) ∧
      (j.val = 5 → ∃ attempts, n = attempts + 1 ∧
        X.get (g, pos + attempts) = some ⟨(waitSite (pvTailWait block)).pc,
          .wait ⟨.shared, g / l.block, pvTailAddress l block⟩ phase true true .cta⟩) ∧
      At u (pvPc block (pvNext j)) (pvIssueFrame l block use phase accumulated lead (pvNext j)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + n)) none := by
  let F' := pvIssueFrame l block use phase accumulated lead (pvPrev j)
  let site := pvSite block
  have hGap := pvGap block j
  have hWait : ∃ n v, At v (pvAdvancePc block j - 2) F' ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop (pos + n)) none ∧
      (j.val ≠ 5 → n = 0) ∧
      (j.val = 5 → ∃ attempts, n = attempts + 1 ∧
        X.get (g, pos + attempts) = some ⟨(waitSite (pvTailWait block)).pc,
          .wait ⟨.shared, g / l.block, pvTailAddress l block⟩ phase true true .cta⟩) := by
    by_cases h : j.val = 5
    · rw [ite_eq_left h] at hGap
      have hRange := hp.shared.2.1
      have hAlign := hp.shared.1
      have hStage := site.stage.isLt
      have hb : pvTailAddress l block < 2 ^ 32 := by unfold pvTailAddress; omega
      have ha : pvTailAddress l block % 8 = 0 := by unfold pvTailAddress; omega
      have ht' : At t (waitSite (pvTailWait block)).pc F' := hGap.1 ▸ ht
      have hBase : ((waitSite (pvTailWait block)).base, b32 (pvTailAddress l block)) ∈ F' := by
        simp [F', pvIssueFrame, pvCarry]
      have hP : ((waitSite (pvTailWait block)).phase, b32 phase) ∈ F' := by
        simp [F', pvIssueFrame, pvCarry]
      obtain ⟨n, v, he, _, hv, hV⟩ := waitAt (pvTailWait block) hb ha hPhase
        (pvBlockFrameTail block use phase accumulated lead (pvPrev j)) hBase hP ht' hr
      exact ⟨n + 1, v, hGap.2 ▸ hv, by simpa only [Nat.add_assoc] using hV,
        fun h' => (h' h).elim, fun _ => ⟨n, rfl, he⟩⟩
    · rw [ite_eq_right h] at hGap
      exact ⟨0, t, hGap ▸ ht, hr, fun _ => rfl, fun h' => (h h').elim⟩
  obtain ⟨n, v, hv, hV, hZero, hTail⟩ := hWait
  obtain ⟨u,hU,hLocal⟩ := pvAdvanceLocal hp (g := g) block j use phase accumulated lead hv
  exact ⟨n,u,hZero,hTail,hU,hV.after_local hLocal⟩

/-- The trace location of a fragment includes the leader-only issues and the tail wait. -/
def pvTracePos (lead : Bool) (base gap i : Nat) : Nat :=
  base + (if lead then i else 0) + if 6 ≤ i then gap else 0

/-- A prefix of one actual PV block. The sixth issue precedes the single tail wait. -/
structure PvBlockPrefix (l : Launch) (X : Execution) (g base : Nat) (block : Fin 4)
    (use phase : Nat) (accumulated lead : Bool) (step : Fin 8) where
  gap : Nat
  state : TState
  noGap : step.val < 6 → gap = 0
  tail : 6 ≤ step.val → ∃ attempts, gap = attempts + 1 ∧
    X.get (g, base + (if lead then 6 else 0) + attempts) =
      some ⟨(waitSite (pvTailWait block)).pc,
        .wait ⟨.shared, g / l.block, pvTailAddress l block⟩ phase true true .cta⟩
  observed : lead = true → ∀ i : Fin 8, i.val < step.val →
    X.get (g, pvTracePos lead base gap i.val) = some (pvIssueEvent l g block i use accumulated)
  checkpoint : At state (pvPc block step) (pvIssueFrame l block use phase accumulated lead step)
  continuation : Run kernel Assumptions.all l g state
    ((X.tr g).drop (pvTracePos lead base gap step.val)) none

private theorem advancePosition (j p gap w : Nat) (lead : Bool)
    (hGap : j < 6 → gap = 0) (hW : j ≠ 5 → w = 0) :
    pvTracePos lead p gap j + (if lead then 1 else 0) + w =
      pvTracePos lead p (gap + w) (j + 1) := by
  by_cases h : j = 5
  · subst j
    cases lead <;> simp [pvTracePos, hGap (by decide), Nat.add_assoc]
  · rw [hW h]
    have hSame : 6 ≤ j ↔ 6 ≤ j + 1 := by omega
    cases lead <;> simp only [pvTracePos, hSame, Nat.add_zero, Bool.false_eq_true, ↓reduceIte]
    omega

private theorem oldPosition (j p gap w i : Nat) (lead : Bool)
    (hPrev : i ≤ j) (hW : j ≠ 5 → w = 0) :
    pvTracePos lead p (gap + w) i = pvTracePos lead p gap i := by
  by_cases h : j = 5
  · have hi : ¬ 6 ≤ i := by omega
    simp [pvTracePos, hi]
  · simp [hW h]

/-- Consume one PV issue, optionally consume the tail wait, and advance the physical V slice. -/
theorem PvBlockPrefix.advance {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g base : Nat} (hg : g < l.threads) (block : Fin 4) (j : Fin 7)
    {use phase : Nat} {accumulated lead : Bool} (hPhase : phase < 2)
    (cur : PvBlockPrefix l X g base block use phase accumulated lead (pvPrev j)) :
    Nonempty (PvBlockPrefix l X g base block use phase accumulated lead (pvNext j)) := by
  obtain ⟨hIssue, hAt, hRun⟩ := pvFramedCursor hp hg block (pvPrev j) use phase accumulated lead
    cur.checkpoint cur.continuation
  obtain ⟨n, u, hZero, hTail, hu, hU⟩ :=
    pvAdvanceCursor hp block j use phase accumulated lead hPhase hAt hRun
  have hNo : j.val + 1 < 6 → cur.gap + n = 0 := by
    intro h
    rw [cur.noGap (by change j.val < 6; omega), hZero (by omega)]
  have hNewTail : 6 ≤ j.val + 1 → ∃ attempts, cur.gap + n = attempts + 1 ∧
      X.get (g, base + (if lead then 6 else 0) + attempts) =
        some ⟨(waitSite (pvTailWait block)).pc,
          .wait ⟨.shared, g / l.block, pvTailAddress l block⟩ phase true true .cta⟩ := by
    intro h
    by_cases hJ : j.val = 5
    · obtain ⟨attempts, hN, he⟩ := hTail hJ
      have hG := cur.noGap (show j.val < 6 by omega)
      refine ⟨attempts, by rw [hG, Nat.zero_add, hN], ?_⟩
      cases lead <;> simpa [pvTracePos, pvPrev, hJ, Nat.add_assoc] using he
    · obtain ⟨attempts, hN, he⟩ := cur.tail (show 6 ≤ j.val by omega)
      exact ⟨attempts, by rw [hZero hJ, Nat.add_zero, hN], he⟩
  have hEvents : lead = true → ∀ i : Fin 8, i.val < (pvNext j).val →
      X.get (g, pvTracePos lead base (cur.gap + n) i.val) =
        some (pvIssueEvent l g block i use accumulated) := by
    intro h i hi
    change i.val < j.val + 1 at hi
    rw [oldPosition j.val base cur.gap n i.val lead (by omega) hZero]
    by_cases hI : i.val < j.val
    · exact cur.observed h i hI
    · have e : i = pvPrev j := Fin.ext (by change i.val = j.val; omega)
      rw [e]
      exact hIssue h
  have hPos : pvTracePos lead base cur.gap (pvPrev j).val + (if lead then 1 else 0) + n =
      pvTracePos lead base (cur.gap + n) (pvNext j).val :=
    advancePosition j.val base cur.gap n lead cur.noGap hZero
  exact ⟨⟨cur.gap + n, u, hNo, hNewTail, hEvents, hu, hPos ▸ hU⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
