-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixDemand
public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Kernels.TmlFa4Fwd.Proof.LoaderWalkCheckpoint
import Lemmas.Flow.Final
import Lemmas.Flow.NotShfl
public import Lemmas.Kernel.PlainStep
public import Lemmas.Flow.TraceReach

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue

noncomputable section

private theorem observedRun {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {s : TState} {events : List Event} {vs : List Visit} (hw : Walk K A l g s events vs) :
    ∃ ending, Run K A l g s events ending := by
  induction hw with
  | stop => exact ⟨_, .nil _⟩
  | tau ht _ ih =>
    obtain ⟨_, hr⟩ := ih
    cases hr with
    | nil => exact ⟨_, .nil _⟩
    | step hLocal he hRest => exact ⟨_, .step (.head ht hLocal) he hRest⟩
    | last hLocal he => exact ⟨_, .last (.head ht hLocal) he⟩
  | ev he _ ih =>
    obtain ⟨_, hr⟩ := ih
    exact ⟨_, .step .refl he hr⟩
  | last he => exact ⟨none, .last .refl he⟩

private theorem cleanUntilObserved {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s events vs)
    {e : Event} (he : e ∈ events) (hSafe : ∀ f, e.kind ≠ .ub f) : s.fault = none := by
  cases hFault : s.fault with
  | none => rfl
  | some fault =>
    cases hw with
    | stop => cases he
    | tau ht _ => simp [Tau, out, hFault] at ht
    | ev ht _ =>
      obtain ⟨_, hOut, hFire⟩ := ht
      simp only [out, hFault, Out.ev.injEq] at hOut
      subst_vars
      obtain ⟨rfl, h⟩ := hFire
      cases h
    | last ht =>
      obtain rfl := List.mem_singleton.mp he
      obtain ⟨_, hOut, hFire⟩ := ht
      simp only [out, hFault, Out.ev.injEq] at hOut
      subst_vars
      obtain ⟨rfl, _⟩ := hFire
      exact (hSafe fault rfl).elim

private theorem cutBeforeMarkedWitness {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    {P cut : TState → Prop} (remaining : TState → Nat)
    (mark : Event → Bool)
    (hZero : ∀ t, P t → cut t → remaining t = 0)
    (hStep : ∀ {t u event}, P t → ¬ cut t → WStep kernel Assumptions.all l g t event u →
      P u ∧ remaining t = event.toList.countP mark + remaining u)
    (hLast : ∀ {t e}, EStep kernel Assumptions.all l g t e none → mark e = false)
    (hs : P s) {target : Event} {index : Nat} (hFound : events[index]? = some target)
    (hLater : (∀ t, P t → ¬ cut t → t.pc ≠ target.pc) ∨
      (mark target = true ∧ remaining s ≤ (events.take index).countP mark)) :
    ∃ u before rest tail, events = before ++ rest ∧ before.length ≤ index ∧ P u ∧ cut u ∧
      before.countP mark = remaining s ∧ Walk kernel Assumptions.all l g u rest tail ∧
      TraceReach kernel Assumptions.all l g s before u := by
  classical
  induction hw generalizing index with
  | stop => simp at hFound
  | @tau t u es vs ht hw ih =>
    by_cases hc : cut t
    · exact ⟨t, [], es, _, rfl, Nat.zero_le _, hs, hc, (hZero t hs hc).symm, .tau ht hw, .refl _⟩
    obtain ⟨hu, hEq⟩ := hStep hs hc (.inl ⟨rfl, ht⟩)
    simp only [Option.toList_none, List.countP_nil, Nat.zero_add] at hEq
    rw [hEq]
    obtain ⟨v,before,rest,tail,he,hLen,hv,hCut,hRank,hWalk,hReach⟩ :=
      ih hu hFound (hLater.imp_right (fun h => ⟨h.1, hEq ▸ h.2⟩))
    exact ⟨v,before,rest,tail,he,hLen,hv,hCut,hRank,hWalk,.tau ht hReach⟩
  | @ev t u e es vs he hw ih =>
    by_cases hc : cut t
    · exact ⟨t, [], e :: es, _, rfl, Nat.zero_le _, hs, hc, (hZero t hs hc).symm,
        .ev he hw, .refl _⟩
    obtain ⟨hu, hEq⟩ := hStep hs hc (.inr ⟨e, rfl, he⟩)
    cases index with
    | zero =>
      have heq : e = target := Option.some.inj hFound
      subst target
      rcases hLater with hPc | ⟨hMark, hRank⟩
      · exact (hPc t hs hc (estep_source_pc he).symm).elim
      · simp only [List.take_zero, List.countP_nil] at hRank
        simp [hMark] at hEq
        omega
    | succ index =>
      have hLater' : (∀ t, P t → ¬ cut t → t.pc ≠ target.pc) ∨
          (mark target = true ∧ remaining u ≤ (es.take index).countP mark) :=
        hLater.imp_right (fun ⟨hMark, hRank⟩ => ⟨hMark, by
          simp only [List.take_succ_cons, List.countP_cons] at hRank
          simp only [Option.toList_some, List.countP_cons, List.countP_nil, Nat.zero_add] at hEq
          omega⟩)
      obtain ⟨v, before, rest, tail, hEs, hLen, hv, hcut, hCount, hWalk,hReach⟩ :=
        ih hu hFound hLater'
      refine ⟨v, e :: before, rest, tail, by rw [hEs]; rfl, by simp [hLen],
        hv, hcut, ?_, hWalk,.event he hReach⟩
      simpa [List.countP_cons, hCount, Nat.add_comm] using hEq.symm
  | @last t e he =>
    by_cases hc : cut t
    · exact ⟨t, [], [e], _, rfl, Nat.zero_le _, hs, hc, (hZero t hs hc).symm,
        .last he,.refl _⟩
    have hIndex : index = 0 := by
      have hi := (List.getElem?_eq_some_iff.mp hFound).1
      simp at hi
      omega
    subst index
    have heq : e = target := Option.some.inj hFound
    subst target
    rcases hLater with hPc | hRank
    · exact (hPc t hs hc (estep_source_pc he).symm).elim
    · exact (Bool.noConfusion ((hLast he).symm.trans hRank.1))

private theorem lastEventNotShuffle {l : Launch} {g : Nat} {t : TState} {e : Event}
    (he : EStep kernel Assumptions.all l g t e none) : Execution.isShfl e = false := by
  obtain ⟨_, _, hf⟩ := he
  obtain ⟨pc, kind⟩ := e
  rcases fires_none_ends hf with ⟨f, h⟩ | h <;> cases h <;> rfl

private theorem loaderSubstepAtNewPc {l : Launch} {g : Nat} {t u : TState}
    {event : Option Event} (hLo : 174 ≤ t.pc) (hHi : t.pc < 1901)
    (hShape : RingShape t) (hStep : WStep kernel Assumptions.all l g t event u)
    (hAdvance : u.pc ≠ t.pc) : u.sub = 0 := by
  rcases hStep with ⟨_, ht⟩ | ⟨_, _, he⟩
  · have ht' : Tau kernel [] l g t u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore hLo (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    have hZero : t.sub = 0 := by
      by_contra! hNZ
      obtain ⟨op, hCode, _, hLocal⟩ := hShape.1.2 (by have := hShape.1.1; omega)
      exact tau_core_not_event hCode hLocal ht'
    rcases tau_core_frame hc ht' with hSkip | hFrame
    · subst u
      rfl
    · exact hFrame.sub.trans hZero
  · rcases (loaderEventProgressWithSubstep hLo (by omega) hShape.1 he).2 with ⟨_, hSub⟩ |
      ⟨hSame, _⟩
    · exact hSub
    · exact (hAdvance hSame).elim

variable {l : Launch} {X : Execution} {g index start stop : Nat} {s : TState}
    {ending : Option TState} {F : List (Nat × Value)}
    (hRange : 174 ≤ start ∧ start ≤ stop ∧ stop ≤ 1901)
    (hAudit : ∀ branch, ((kernel.code.drop start).take (stop - start)).all
      (fun ins => loaderPipelineCutOp start stop branch (F.map Prod.fst) ins.op) = true)
include hRange hAudit

section
variable (hStart : start ≤ s.pc ∧ s.pc ≤ stop) (hs : At s s.pc F)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {target : Event}
    (he : X.get (g, j) = some target) (hBefore : index ≤ j) (hSafe : ∀ f, target.kind ≠ .ub f)
    (remaining : TState → Nat) (mark : Event → Bool)
    (hLater : stop ≤ target.pc ∨ (mark target = true ∧ remaining s ≤
      (((X.tr g).drop index).take (j - index)).countP mark))
    (hLast : ∀ {t e}, EStep kernel Assumptions.all l g t e none → mark e = false)
    (hZero : ∀ t, t.pc = stop → remaining t = 0)
    (hRank : ∀ {t u event}, start ≤ t.pc → t.pc < stop → RingShape t → Holds t.regs F →
      WStep kernel Assumptions.all l g t event u →
      remaining t = event.toList.countP mark + remaining u)
include hStart hs hr he hBefore hSafe remaining mark hLater hLast hZero hRank

/-- Follow the actual events to an audited nonvector cut before a later observed event.
The cut supplies actual continuation and the number of marked events consumed. -/
theorem prefixStableCutFromInteriorWithReach :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      passed.countP mark = remaining s ∧ nextIndex ≤ j ∧
      TraceReach kernel Assumptions.all l g s passed u := by
  have hGet : ((X.tr g).drop index)[j - index]? = some target := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hBefore]
    exact he
  obtain ⟨vs, hw⟩ := Mma.walkFromRun hr
  let P := fun (t : TState) => (start ≤ t.pc ∧ t.pc ≤ stop) ∧ RingShape t ∧ Holds t.regs F ∧
    (t.pc = stop → t.sub = 0)
  let cut := fun (t : TState) => t.pc = stop
  have hAdvance {t u : TState} {event : Option Event} (hP : P t) (hn : ¬ cut t)
      (hStep : WStep kernel Assumptions.all l g t event u) :
      P u ∧ remaining t = event.toList.countP mark + remaining u := by
    obtain ⟨hBounds, hShape, hF, _⟩ := hP
    have hPc : t.pc < stop := lt_of_le_of_ne hBounds.2 hn
    obtain ⟨hLo, hHi, huShape, huF⟩ :=
      pipelineCutStep hRange.1 hRange.2.2 ⟨hBounds.1, hPc⟩ (hAudit u.pc) hStep hShape hF
    have hSub (hc : u.pc = stop) : u.sub = 0 :=
      loaderSubstepAtNewPc (hRange.1.trans hBounds.1) (by omega) hShape hStep (by omega)
    exact ⟨⟨⟨hLo, hHi.resolve_right (Nat.lt_irrefl _)⟩, huShape, huF, hSub⟩,
      hRank hBounds.1 hPc hShape hF hStep⟩
  have hInitial : P s := ⟨hStart, ringShapeOfAt hs, hs.2.2.2.2, fun _ => hs.2.1⟩
  have hWitness : (∀ t, P t → ¬ cut t → t.pc ≠ target.pc) ∨
      (mark target = true ∧ remaining s ≤ (((X.tr g).drop index).take (j - index)).countP mark) :=
    hLater.imp_left (fun hPc t ht hn =>
      Nat.ne_of_lt ((lt_of_le_of_ne ht.1.2 hn).trans_le hPc))
  obtain ⟨u, front, tail, _, hTrace, hLength, hU, hCut, hCount, hWalk,hReach⟩ :=
    cutBeforeMarkedWitness hw remaining mark (P := P) (cut := cut)
      (fun t _ ht => hZero t ht) hAdvance hLast hInitial hGet hWitness
  have hPosition : index + front.length ≤ j := by omega
  have hIn : target ∈ tail := by
    apply List.mem_of_getElem? (i := j - (index + front.length))
    rw [hTrace, List.getElem?_append_right hLength] at hGet
    have heq : j - index - front.length = j - (index + front.length) := by omega
    simpa only [heq] using hGet
  have hFront : (X.tr g).drop (index + front.length) = tail := by
    rw [← List.drop_drop, hTrace, List.drop_left]
  have hPc : u.pc = stop := hCut
  have hSub : u.sub = 0 := hU.2.2.2 hPc
  have hFault := cleanUntilObserved hWalk hIn hSafe
  obtain ⟨end', hRun⟩ := observedRun hWalk
  refine ⟨u, front, end', hFront.symm ▸ hTrace,
    ⟨hPc, hSub, hU.2.1.2 hSub, hFault, hU.2.2.1⟩, hFront.symm ▸ hRun, hCount, hPosition,hReach⟩

/-- Replay an audited loader cut and count the marked events consumed. -/
theorem prefixStableCutFromInterior :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      passed.countP mark = remaining s ∧ nextIndex ≤ j := by
  obtain ⟨u,es,stop',hEs,hu,hTail,hCount,hIndex,_⟩ :=
    prefixStableCutFromInteriorWithReach hRange hAudit hStart hs hr he hBefore hSafe
      remaining mark hLater hLast hZero hRank
  exact ⟨u,es,stop',hEs,hu,hTail,hCount,hIndex⟩
end

/-- Follow the actual events to an audited nonvector cut before a later observed event.
The cut supplies actual continuation and the number of marked events consumed. -/
theorem prefixStableCut (hs : At s start F)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {target : Event}
    (he : X.get (g, j) = some target) (hBefore : index ≤ j) (hSafe : ∀ f, target.kind ≠ .ub f)
    (remaining : TState → Nat) (mark : Event → Bool)
    (hLater : stop ≤ target.pc ∨ (mark target = true ∧ remaining s ≤
      (((X.tr g).drop index).take (j - index)).countP mark))
    (hLast : ∀ {t e}, EStep kernel Assumptions.all l g t e none → mark e = false)
    (hZero : ∀ t, t.pc = stop → remaining t = 0)
    (hRank : ∀ {t u event}, start ≤ t.pc → t.pc < stop → RingShape t → Holds t.regs F →
      WStep kernel Assumptions.all l g t event u →
      remaining t = event.toList.countP mark + remaining u) :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      passed.countP mark = remaining s ∧ nextIndex ≤ j :=
  prefixStableCutFromInterior hRange hAudit
    (by rw [hs.1]; exact ⟨le_rfl, hRange.2.1⟩) (hs.1.symm ▸ hs)
    hr he hBefore hSafe remaining mark hLater hLast hZero hRank

/-- An audited loader slice containing no decoded shuffle keeps the lane ordinal. -/
theorem prefixQuietCutWithReach
    (hQuiet : ((kernel.code.drop start).take (stop - start)).all (fun ins => !ins.op.isShfl) = true)
    (_hTargetCode : ∃ ins, kernel.code[stop]? = some ins ∧ loaderVector ins.op = false)
    (hs : At s start F) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : stop ≤ target.pc) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      ((X.tr g).take nextIndex).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl ∧ nextIndex ≤ j ∧
      TraceReach kernel Assumptions.all l g s passed u := by
  have noShuffle {a b : TState} {ev : Option Event} (hLo : start ≤ a.pc) (hHi : a.pc < stop)
      (hw : WStep kernel Assumptions.all l g a ev b) :
      0 = ev.toList.countP Execution.isShfl + 0 := by
    rcases hw with ⟨rfl, _⟩ | ⟨e, rfl, ⟨tmpl, hOut, hFire⟩⟩
    · rfl
    rcases out_ev hOut with ⟨_, rfl⟩ | ⟨ins, hCode, rfl⟩
    · cases hFire.2
    have hGet : ((kernel.code.drop start).take (stop - start))[a.pc - start]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hCode
    have hNo := List.all_eq_true.mp hQuiet ins (List.mem_of_getElem? hGet)
    have hEv : Execution.isShfl e = false := by
      cases hShfl : Execution.isShfl e
      · rfl
      · rw [fires_shfl_op hFire hShfl] at hNo
        cases hNo
    simp [hEv]
  obtain ⟨u, front, stop', hTrace, hu, hRun, hCount, hIndex,hReach⟩ :=
    prefixStableCutFromInteriorWithReach hRange hAudit
      (by rw [hs.1]; exact ⟨le_rfl,hRange.2.1⟩) (hs.1.symm ▸ hs) hr he hBefore hSafe (fun _ => 0)
      Execution.isShfl (.inl hLater) lastEventNotShuffle (fun _ _ => rfl)
      (fun hLo hHi _ _ hStep => noShuffle hLo hHi hStep)
  refine ⟨u, front, stop', hTrace, hu, hRun, ?_, hIndex,hReach⟩
  rw [List.take_add, hTrace, List.take_append_length, List.countP_append, hCount, Nat.add_zero]

/-- An audited loader slice containing no decoded shuffle keeps the lane ordinal. -/
theorem prefixQuietCut
    (hQuiet : ((kernel.code.drop start).take (stop - start)).all (fun ins => !ins.op.isShfl) = true)
    (hTargetCode : ∃ ins, kernel.code[stop]? = some ins ∧ loaderVector ins.op = false)
    (hs : At s start F) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : stop ≤ target.pc) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      ((X.tr g).take nextIndex).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl ∧ nextIndex ≤ j := by
  obtain ⟨u,es,stop',hEs,hu,hTail,hCount,hIndex,_⟩ :=
    prefixQuietCutWithReach hRange hAudit hQuiet hTargetCode hs hr he hBefore hLater hSafe
  exact ⟨u,es,stop',hEs,hu,hTail,hCount,hIndex⟩

omit hRange hAudit in
/-- Fallthrough instructions whose decoded shuffles cannot be skipped. -/
def LoaderCountedInstr (ins : Instr) : Bool :=
  match ins.op with
  | .bra .. | .brx .. => false
  | _ => !ins.op.isShfl || ins.guard.isNone

omit hRange hAudit in
private theorem counted_shuffle_unguarded {i : Instr} (h : LoaderCountedInstr i = true)
    (hs : i.op.isShfl = true) : i.guard = none ∧ i.op.isLocal = false := by
  cases hi : i.op <;> simp_all [LoaderCountedInstr, Op.isShfl]
  case warp w =>
    rcases w with ⟨kind, ty, dsts, srcs, mask⟩
    cases kind <;> simp_all [Op.isLocal]

omit hRange hAudit in
/-- A returning shuffle event advances to the next decoded instruction. -/
theorem shuffle_fires_next {l : Launch} {g : Nat} {s u : TState} {op : Op}
    {e : Event} (hop : op.isShfl = true)
    (hf : Fires s.pc (eventTmpl [] l g s op) e (some u)) :
    Execution.isShfl e = true ∧ u.pc = s.pc + 1 := by
  cases hOp : op <;> simp_all only [Op.isShfl, Bool.false_eq_true]
  case warp w =>
    rcases w with ⟨kind, ty, dsts, srcs, mask⟩
    cases kind <;> try contradiction
    rename_i mode
    simp only [eventTmpl, warpTmpl] at hf
    split at hf
    · simp only [shflTmpl] at hf
      repeat' split at hf
      all_goals
        first
        | (obtain ⟨_, _, rfl, hResult⟩ := hf
           obtain rfl := Option.some.inj hResult
           exact ⟨rfl, rfl⟩)
        | simp [Fires] at hf
    all_goals first | contradiction | simp [Fires] at hf

omit hRange hAudit in
/-- Count the decoded shuffle instructions from a position up to a cut. -/
def loaderShuffleTail (stop pc : Nat) : Nat :=
  ((kernel.code.take stop).drop pc).countP (fun ins => ins.op.isShfl)

omit hRange hAudit in
private theorem loaderShuffleTail_succ {stop pc : Nat} {i : Instr} (hPc : pc < stop)
    (hCode : kernel.code[pc]? = some i) :
    loaderShuffleTail stop pc =
      (if i.op.isShfl then 1 else 0) + loaderShuffleTail stop (pc + 1) := by
  have hGet : (kernel.code.take stop)[pc]? = some i := by
    rw [List.getElem?_take_of_lt hPc, hCode]
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hGet
  unfold loaderShuffleTail
  rw [List.drop_eq_getElem_cons hi, he, List.countP_cons, Nat.add_comm]

omit hRange hAudit in
/-- Each control-flow edge must preserve the remaining shuffle count except when
it executes an unguarded shuffle. -/
def LoaderRankedInstr (stop pc : Nat) (i : Instr) : Bool :=
  match i.op with
  | .bra target _ => decide (loaderShuffleTail stop pc = loaderShuffleTail stop target)
  | .brx .. => false
  | _ => LoaderCountedInstr i

omit hRange hAudit in
private theorem rankedInstructionEdge {stop pc next : Nat} {i : Instr}
    (hRank : LoaderRankedInstr stop pc i = true)
    (hNext : next = nextPc i.op pc ∨ BrxTarget i.op next) :
    next = pc + 1 ∨ loaderShuffleTail stop pc = loaderShuffleTail stop next := by
  cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hNext
  case bra target uni =>
    subst next
    exact .inr (by simpa [LoaderRankedInstr, hop] using hRank)
  case brx =>
    simp [LoaderRankedInstr, hop] at hRank
  all_goals exact .inl hNext

omit hRange hAudit in
/-- One actual loader step conserves the remaining decoded shuffle rank. -/
theorem rankedLoaderStep {l : Launch} {g start stop : Nat} {t u : TState}
    {ev : Option Event} (hRange : 174 ≤ start ∧ start ≤ stop ∧ stop ≤ 1901)
    (hCounted : (((kernel.code.drop start).take (stop - start)).zipIdx start).all
      (fun (i, pc) => LoaderRankedInstr stop pc i) = true)
    (hLo : start ≤ t.pc) (hHi : t.pc < stop)
    (hw : WStep kernel Assumptions.all l g t ev u) :
    loaderShuffleTail stop t.pc =
      ev.toList.countP Execution.isShfl + loaderShuffleTail stop u.pc := by
  have counted {i : Instr} (hc : kernel.code[t.pc]? = some i) :
      LoaderRankedInstr stop t.pc i = true := by
    have hGet : ((kernel.code.drop start).take (stop - start))[t.pc - start]? = some i := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    have hAt : (((kernel.code.drop start).take (stop - start)).zipIdx start)[t.pc - start]? =
        some (i, t.pc) := by
      rw [List.getElem?_zipIdx, hGet]
      simp [Nat.add_sub_of_le hLo]
    exact List.all_eq_true.mp hCounted (i, t.pc) (List.mem_of_getElem? hAt)
  have hCodeEq := loaderOutCore (show 174 ≤ t.pc by omega) (show t.pc < 1906 by omega)
    (l := l) (g := g) (t := t)
  rcases hw with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have ht' : Tau kernel [] l g t u := by unfold Tau at ht ⊢; rwa [← hCodeEq]
    obtain ⟨i, hc⟩ := tau_core_has_code ht'
    have hi := counted hc
    have hShfl : i.op.isShfl = false := by
      by_contra! hShfl
      have hIs := Bool.eq_true_of_not_eq_false hShfl
      have hPlain : LoaderCountedInstr i = true := by
        cases hop : i.op <;> simp_all [LoaderRankedInstr, Op.isShfl]
      obtain ⟨hGuard, hEvent⟩ := counted_shuffle_unguarded hPlain hIs
      obtain ⟨guard, op⟩ := i
      change guard = none at hGuard
      subst guard
      exact tau_core_not_event hc hEvent ht'
    have hp : u.pc = t.pc + 1 ∨
        loaderShuffleTail stop t.pc = loaderShuffleTail stop u.pc := by
      rcases tau_core_frame hc ht' with rfl | hf
      · exact .inl rfl
      · exact rankedInstructionEdge hi hf.pc
    rcases hp with hp | hRemaining
    · rw [loaderShuffleTail_succ hHi hc, hp, hShfl]
      rfl
    · simpa only [Option.toList_none, List.countP_nil, Nat.zero_add] using hRemaining
  · have he' : EStep kernel [] l g t e (some u) := by
      obtain ⟨tmpl, hout, hf⟩ := he
      exact ⟨tmpl, hCodeEq.symm.trans hout, hf⟩
    obtain ⟨i, hc, _, hf⟩ := estep_event_source he'
    by_cases hShfl : i.op.isShfl = true
    · obtain ⟨hE, hPc⟩ := shuffle_fires_next hShfl hf
      rw [loaderShuffleTail_succ hHi hc, hPc, hShfl]
      simp [hE]
    · have hIs : Execution.isShfl e = false := by
        cases hE : Execution.isShfl e
        · rfl
        · exact (hShfl (fires_shfl_op hf hE)).elim
      rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with hp | hp
      · simp [hIs, hp]
      · rw [loaderShuffleTail_succ hHi hc, hp]
        simp [hShfl, hIs]

/-- Branches that jump over no shuffle instruction preserve the decoded shuffle count. -/
theorem prefixRankedShuffleCutWithReach
    (hCounted : (((kernel.code.drop start).take (stop - start)).zipIdx start).all
      (fun (i, pc) => LoaderRankedInstr stop pc i) = true) (hs : At s start F)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {target : Event}
    (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : stop ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ≤
      ((X.tr g).take j).countP Execution.isShfl)) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      ((X.tr g).take nextIndex).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ∧
      nextIndex ≤ j ∧ TraceReach kernel Assumptions.all l g s passed u := by
  have hDemand : stop ≤ target.pc ∨ (Execution.isShfl target = true ∧
      loaderShuffleTail stop s.pc ≤ (((X.tr g).drop index).take (j - index)).countP
        Execution.isShfl) :=
    hLater.imp_right (fun ⟨hMark, hRank⟩ => ⟨hMark, by
      rw [← Nat.add_sub_of_le hBefore, List.take_add, List.countP_append] at hRank
      rw [hs.1]
      omega⟩)
  obtain ⟨u, front, stop', hTrace, hu, hRun, hCount, hIndex,hReach⟩ :=
    prefixStableCutFromInteriorWithReach hRange hAudit
      (by rw [hs.1]; exact ⟨le_rfl,hRange.2.1⟩) (hs.1.symm ▸ hs) hr he hBefore hSafe
      (loaderShuffleTail stop ·.pc)
      Execution.isShfl hDemand lastEventNotShuffle (fun t ht => by simp [loaderShuffleTail, ht])
      (fun hLo hHi _ _ hStep => rankedLoaderStep hRange hCounted hLo hHi hStep)
  refine ⟨u, front, stop', hTrace, hu, hRun, ?_, hIndex,hReach⟩
  rw [List.take_add, hTrace, List.take_append_length, List.countP_append, hCount, hs.1]

/-- Branches that jump over no shuffle instruction preserve the decoded shuffle count. -/
theorem prefixRankedShuffleCut
    (hCounted : (((kernel.code.drop start).take (stop - start)).zipIdx start).all
      (fun (i, pc) => LoaderRankedInstr stop pc i) = true) (hs : At s start F)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {target : Event}
    (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : stop ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ≤
      ((X.tr g).take j).countP Execution.isShfl)) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      ((X.tr g).take nextIndex).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ∧
      nextIndex ≤ j := by
  obtain ⟨u,es,stop',hEs,hu,hTail,hCount,hIndex,_⟩ :=
    prefixRankedShuffleCutWithReach hRange hAudit hCounted hs hr he hBefore hLater hSafe
  exact ⟨u,es,stop',hEs,hu,hTail,hCount,hIndex⟩

omit hRange hAudit in
private theorem markedWalkProjectionsCutOrEvent {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits)
    {P cut : TState → Prop} {ι : Type} (remaining : ι → Nat → Nat) (mark : ι → Event → Bool)
    (hZero : ∀ t, P t → cut t → ∀ a, remaining a t.pc = 0)
    (hStep : ∀ {t u event}, P t → ¬ cut t → WStep kernel Assumptions.all l g t event u →
      P u ∧ ∀ a, remaining a t.pc = event.toList.countP (mark a) + remaining a u.pc)
    (hs : P s) {target : Event} {index : Nat} (hFound : events[index]? = some target) :
    (∃ t, P t ∧ ¬ cut t ∧ t.pc = target.pc ∧
      ∀ a, (events.take index).countP (mark a) + remaining a target.pc = remaining a s.pc) ∨
    (∃ u before rest tail, events = before ++ rest ∧ before.length ≤ index ∧ P u ∧ cut u ∧
      (∀ a, before.countP (mark a) = remaining a s.pc) ∧
      Walk kernel Assumptions.all l g u rest tail) := by
  classical
  induction hw generalizing index with
  | stop => simp at hFound
  | @tau t u es vs ht hw ih =>
    by_cases hc : cut t
    · exact .inr ⟨t, [], es, _, rfl, Nat.zero_le _, hs, hc,
        (fun a => (hZero t hs hc a).symm), .tau ht hw⟩
    obtain ⟨hu, hEq⟩ := hStep hs hc (.inl ⟨rfl, ht⟩)
    simp only [Option.toList_none, List.countP_nil, Nat.zero_add] at hEq
    rcases ih hu hFound with ⟨v,hv,hn,hpc,hCount⟩ |
      ⟨v,before,rest,tail,hEs,hLen,hv,hcut,hCount,hWalk⟩
    · exact .inl ⟨v,hv,hn,hpc,fun a => (hCount a).trans (hEq a).symm⟩
    · exact .inr ⟨v,before,rest,tail,hEs,hLen,hv,hcut,fun a =>
        (hCount a).trans (hEq a).symm,hWalk⟩
  | @ev t u e es vs he hw ih =>
    by_cases hc : cut t
    · exact .inr ⟨t, [], e :: es, _, rfl, Nat.zero_le _, hs, hc, (fun a => (hZero t hs hc a).symm),
        .ev he hw⟩
    cases index with
    | zero =>
      obtain rfl := Option.some.inj hFound
      exact .inl ⟨t, hs, hc, (estep_source_pc he).symm, by simp [estep_source_pc he]⟩
    | succ index =>
      obtain ⟨hu, hEq⟩ := hStep hs hc (.inr ⟨e, rfl, he⟩)
      rcases ih hu hFound with ⟨v, hv, hn, hp, hCount⟩ |
        ⟨v, before, rest, tail, hEs, hLen, hv, hcut, hCount, hWalk⟩
      · refine .inl ⟨v, hv, hn, hp, ?_⟩
        intro a
        have ha := hEq a
        have hCount := hCount a
        simp only [List.take_succ_cons, List.countP_cons] at ⊢
        simp only [Option.toList_some, List.countP_cons, List.countP_nil, Nat.zero_add] at ha
        omega
      · refine .inr ⟨v, e :: before, rest, tail, by rw [hEs]; rfl, by simp [hLen],
          hv, hcut, ?_, hWalk⟩
        intro a
        simpa [List.countP_cons, hCount a, Nat.add_comm] using (hEq a).symm
  | @last t e he =>
    by_cases hc : cut t
    · exact .inr ⟨t, [], [e], _, rfl, Nat.zero_le _, hs, hc,
        (fun a => (hZero t hs hc a).symm), .last he⟩
    have hIndex : index = 0 := by
      have hi := (List.getElem?_eq_some_iff.mp hFound).1
      simp at hi
      omega
    subst index
    obtain rfl := Option.some.inj hFound
    exact .inl ⟨t, hs, hc, (estep_source_pc he).symm, by simp [estep_source_pc he]⟩

omit hRange hAudit in
/-- Replay one actual loader cut, recording all selected event counts at the same boundary. -/
theorem prefixProjectionsCutOrEvent {l : Launch} {X : Execution} {g index start stop : Nat}
    {s : TState} {ending : Option TState} {F : List (Nat × Value)} {ι : Type}
    (hRange : 174 ≤ start ∧ start ≤ stop ∧ stop ≤ 1901)
    (hAudit : ∀ branch, ((kernel.code.drop start).take (stop - start)).all
      (fun ins => loaderPipelineCutOp start stop branch (F.map Prod.fst) ins.op) = true)
    (remaining : ι → Nat → Nat) (mark : ι → Event → Bool) (hZero : ∀ a, remaining a stop = 0)
    (hRank : ∀ {t u evt}, start ≤ t.pc → t.pc < stop →
      WStep kernel Assumptions.all l g t evt u →
      ∀ a, remaining a t.pc = evt.toList.countP (mark a) + remaining a u.pc)
    (hs : At s start F)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hSafe : ∀ f, target.kind ≠ .ub f) :
    (start ≤ target.pc ∧ target.pc < stop ∧
      ∀ a, ((X.tr g).take j).countP (mark a) + remaining a target.pc =
        ((X.tr g).take index).countP (mark a) + remaining a start) ∨
    (∃ pos ≤ j, ∃ u ending',
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop pos) ending' ∧
      ∀ a, ((X.tr g).take pos).countP (mark a) =
        ((X.tr g).take index).countP (mark a) + remaining a start) := by
  have hGet : ((X.tr g).drop index)[j - index]? = some target := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hBefore]
    exact he
  obtain ⟨visits, hWalk⟩ := Mma.walkFromRun hr
  let P := fun (t : TState) => (start ≤ t.pc ∧ t.pc ≤ stop) ∧ RingShape t ∧
    Holds t.regs F ∧ (t.pc = stop → t.sub = 0)
  let cut := fun (t : TState) => t.pc = stop
  have hAdvance {t u : TState} {event : Option Event} (hP : P t) (hn : ¬ cut t)
      (hStep : WStep kernel Assumptions.all l g t event u) :
      P u ∧ ∀ a, remaining a t.pc = event.toList.countP (mark a) + remaining a u.pc := by
    obtain ⟨hBounds, hShape, hF, _⟩ := hP
    have hPc : t.pc < stop := lt_of_le_of_ne hBounds.2 hn
    obtain ⟨hLo, hHi, hU, hRegs⟩ :=
      pipelineCutStep hRange.1 hRange.2.2 ⟨hBounds.1, hPc⟩ (hAudit u.pc) hStep hShape hF
    have hSub (hc : u.pc = stop) : u.sub = 0 :=
      loaderSubstepAtNewPc (hRange.1.trans hBounds.1) (by omega) hShape hStep (by omega)
    exact ⟨⟨⟨hLo, hHi.resolve_right (Nat.lt_irrefl _)⟩, hU, hRegs, hSub⟩,
      hRank hBounds.1 hPc hStep⟩
  have hInitial : P s :=
    ⟨⟨hs.1.symm ▸ le_rfl, hs.1.symm ▸ hRange.2.1⟩, ringShapeOfAt hs, hs.2.2.2.2,
      fun _ => hs.2.1⟩
  rcases markedWalkProjectionsCutOrEvent hWalk (remaining) mark
    (P := P) (cut := cut) (fun t _ ht a => by rw [show t.pc = stop from ht]; exact hZero a)
    hAdvance hInitial hGet with ⟨t, ht, hn, hp, hCount⟩ |
      ⟨u, front, tail, _, hTrace, hLength, hU, hCut, hCount, hTail⟩
  · refine .inl ⟨hp ▸ ht.1.1, hp ▸ lt_of_le_of_ne ht.1.2 hn, ?_⟩
    intro a
    conv => left; left; rw [← Nat.add_sub_of_le hBefore, List.take_add, List.countP_append]
    rw [Nat.add_assoc, hCount a, hs.1]
  · let pos := index + front.length
    have hPos : pos ≤ j := by unfold pos; omega
    have hIn : target ∈ tail := by
      apply List.mem_of_getElem? (i := j - pos)
      rw [hTrace, List.getElem?_append_right hLength] at hGet
      have same : j - index - front.length = j - pos := by unfold pos; omega
      rwa [same] at hGet
    have hFront : (X.tr g).drop pos = tail := by
      unfold pos
      rw [← List.drop_drop, hTrace, List.drop_left]
    have hPc : u.pc = stop := hCut
    have hSub : u.sub = 0 := hU.2.2.2 hPc
    have hFault := cleanUntilObserved hTail hIn hSafe
    obtain ⟨end', hRun⟩ := observedRun hTail
    refine .inr ⟨pos, hPos, u, end', ⟨hPc, hSub, hU.2.1.2 hSub, hFault, hU.2.2.1⟩,
      hFront.symm ▸ hRun, ?_⟩
    intro a
    unfold pos
    rw [List.take_add, hTrace, List.take_append_length, List.countP_append, hCount a, hs.1]

/-- A conserved projection survives an actual loader cut at the end of a
checked interval. The interior case retains the projection at the selected event. -/
theorem prefixProjectedCutOrEvent (remaining : Nat → Nat) (mark : Event → Bool)
    (hZero : remaining stop = 0)
    (hRank : ∀ {t u evt}, start ≤ t.pc → t.pc < stop →
      WStep kernel Assumptions.all l g t evt u →
      remaining t.pc = evt.toList.countP mark + remaining u.pc) (hs : At s start F)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {target : Event}
    (he : X.get (g, j) = some target) (hBefore : index ≤ j) (hSafe : ∀ f, target.kind ≠ .ub f) :
    (start ≤ target.pc ∧ target.pc < stop ∧
      ((X.tr g).take j).countP mark + remaining target.pc =
        ((X.tr g).take index).countP mark + remaining start) ∨
    (∃ pos ≤ j, ∃ u ending',
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop pos) ending' ∧
      ((X.tr g).take pos).countP mark =
        ((X.tr g).take index).countP mark + remaining start) := by
  have h := prefixProjectionsCutOrEvent hRange hAudit (fun (_ : Unit) => remaining)
    (fun _ => mark) (fun _ => hZero) (fun hLo hHi hStep _ => hRank hLo hHi hStep)
    hs hr he hBefore hSafe
  rcases h with ⟨hLo,hHi,hRank⟩ | ⟨pos,hPos,u,ending',hu,hRun,hRank⟩
  · exact .inl ⟨hLo,hHi,hRank ()⟩
  · exact .inr ⟨pos,hPos,u,ending',hu,hRun,hRank ()⟩

omit hRange hAudit in
/-- An observed event with too few preceding shuffles to cross a cut occurs
inside the current visit to its containing packet. -/
theorem loaderEventInRankedSlice {l : Launch} {g start cut stop : Nat}
    {s : TState} {events : List Event} {visits : List Visit}
    (hRange : 174 ≤ start ∧ start ≤ cut ∧ cut ≤ 1901) (hCut : cut ≤ stop)
    (hAudit : ∀ bound, ((kernel.code.drop start).take (cut - start)).all
      (fun i => loaderPipelineCutOp start cut bound [] i.op) = true)
    (hRanked : (((kernel.code.drop start).take (cut - start)).zipIdx start).all
      (fun (i, pc) => LoaderRankedInstr cut pc i) = true)
    (hWalk : Walk kernel Assumptions.all l g s events visits)
    (hPc : start ≤ s.pc ∧ s.pc ≤ cut) (hShape : RingShape s)
    {target : Event} {index : Nat} (hEvent : events[index]? = some target)
    (hRank : (events.take index).countP Execution.isShfl < loaderShuffleTail cut s.pc) :
    target ∈ loaderSliceEvents start stop visits := by
  have before {t : TState} (hHere : t.pc ≤ cut)
      {es : List Event} {n : Nat}
      (hFew : (es.take n).countP Execution.isShfl < loaderShuffleTail cut t.pc) :
      t.pc < cut := by
    by_contra! hAt
    obtain heq : t.pc = cut := by omega
    simp [loaderShuffleTail, heq] at hFew
  have advance {t u : TState} {ev : Option Event}
      (hHere : start ≤ t.pc) (hBefore : t.pc < cut) (ht : RingShape t)
      (hStep : WStep kernel Assumptions.all l g t ev u) :
      (start ≤ u.pc ∧ u.pc ≤ cut) ∧ RingShape u ∧
        loaderShuffleTail cut t.pc =
          ev.toList.countP Execution.isShfl + loaderShuffleTail cut u.pc := by
    obtain ⟨hLo, hHi, hu, _⟩ := pipelineCutStep (F := []) hRange.1 hRange.2.2
      ⟨hHere, hBefore⟩ (hAudit u.pc) hStep ht trivial
    exact ⟨⟨hLo, hHi.elim id (False.elim ∘ Nat.lt_irrefl _)⟩, hu,
      rankedLoaderStep hRange hRanked hHere hBefore hStep⟩
  induction hWalk generalizing index with
  | stop => simp at hEvent
  | @tau t u es vs ht hw ih =>
    have hBefore := before hPc.2 hRank
    obtain ⟨huPc, hu, hEq⟩ := advance hPc.1 hBefore hShape (.inl ⟨rfl, ht⟩)
    have hMem := ih huPc hu hEvent (by simpa [hEq] using hRank)
    simpa [loaderSliceEvents, visit, hPc.1, hBefore.trans_le hCut] using hMem
  | @ev t u e es vs he hw ih =>
    have hBefore := before hPc.2 hRank
    cases index with
    | zero =>
      obtain rfl := Option.some.inj hEvent
      simp [loaderSliceEvents, visit, hPc.1, hBefore.trans_le hCut]
    | succ index =>
      obtain ⟨huPc, hu, hEq⟩ := advance hPc.1 hBefore hShape (.inr ⟨e, rfl, he⟩)
      have hCount : (es.take index).countP Execution.isShfl < loaderShuffleTail cut u.pc := by
        simp only [List.take_succ_cons, List.countP_cons] at hRank
        simp only [Option.toList_some, List.countP_cons, List.countP_nil, Nat.zero_add] at hEq
        omega
      have hMem := ih huPc hu hEvent hCount
      simp [loaderSliceEvents, visit, hPc.1, hBefore.trans_le hCut, List.mem_filterMap] at hMem ⊢
      exact .inr hMem
  | @last t e he =>
    have hBefore := before hPc.2 hRank
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hEvent
    obtain rfl : index = 0 := by simp at hi; omega
    obtain rfl := Option.some.inj hEvent
    simp [loaderSliceEvents, visit, hPc.1, hBefore.trans_le hCut]

/-- A straight-line loader slice preserves the actual trace up to the cut and adds
exactly the shuffle count of the decoded instructions it advances over. -/
theorem prefixCountedShuffleCutAtEntryWithReach
    (hCounted : ((kernel.code.drop start).take (stop - start)).all LoaderCountedInstr = true)
    (hs : At s start F) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : stop ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ≤
      ((X.tr g).take j).countP Execution.isShfl)) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      ((X.tr g).take nextIndex).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ∧
      nextIndex ≤ j ∧ TraceReach kernel Assumptions.all l g s passed u := by
  apply prefixRankedShuffleCutWithReach hRange hAudit _ hs hr he hBefore hLater hSafe
  apply List.all_eq_true.mpr
  rintro ⟨i, pc⟩ hm
  have hGet := (List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mp hm).2
  have hi := List.all_eq_true.mp hCounted i (List.mem_of_getElem? hGet)
  have hOp : ∀ op, i.op = op → LoaderRankedInstr stop pc i = true := by
    intro op hop
    cases op <;> simp [LoaderRankedInstr, hop, LoaderCountedInstr] at hi ⊢ <;> assumption
  exact hOp i.op rfl

/-- Replay a straight-line loader slice with its decoded shuffle count. -/
theorem prefixCountedShuffleCutAtEntry
    (hCounted : ((kernel.code.drop start).take (stop - start)).all LoaderCountedInstr = true)
    (hs : At s start F) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : stop ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ≤
      ((X.tr g).take j).countP Execution.isShfl)) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      ((X.tr g).take nextIndex).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ∧
      nextIndex ≤ j := by
  obtain ⟨u,es,stop',hEs,hu,hTail,hCount,hIndex,_⟩ :=
    prefixCountedShuffleCutAtEntryWithReach hRange hAudit hCounted hs hr he hBefore hLater hSafe
  exact ⟨u,es,stop',hEs,hu,hTail,hCount,hIndex⟩

/-- The same cut interface for callers with an audited nonvector checkpoint. -/
theorem prefixCountedShuffleCutWithReach
    (hCounted : ((kernel.code.drop start).take (stop - start)).all LoaderCountedInstr = true)
    (_hTargetCode : ∃ ins, kernel.code[stop]? = some ins ∧ loaderVector ins.op = false)
    (hs : At s start F) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : stop ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ≤
      ((X.tr g).take j).countP Execution.isShfl)) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      ((X.tr g).take nextIndex).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ∧
      nextIndex ≤ j ∧ TraceReach kernel Assumptions.all l g s passed u :=
  prefixCountedShuffleCutAtEntryWithReach hRange hAudit hCounted hs hr he hBefore hLater hSafe

/-- The same cut interface for callers with an audited nonvector checkpoint. -/
theorem prefixCountedShuffleCut
    (hCounted : ((kernel.code.drop start).take (stop - start)).all LoaderCountedInstr = true)
    (_hTargetCode : ∃ ins, kernel.code[stop]? = some ins ∧ loaderVector ins.op = false)
    (hs : At s start F) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {target : Event} (he : X.get (g, j) = some target) (hBefore : index ≤ j)
    (hLater : stop ≤ target.pc ∨ (Execution.isShfl target = true ∧
      ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ≤
      ((X.tr g).take j).countP Execution.isShfl)) (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u passed ending',
      let nextIndex := index + passed.length
      (X.tr g).drop index = passed ++ (X.tr g).drop nextIndex ∧
      At u stop F ∧ Run kernel Assumptions.all l g u ((X.tr g).drop nextIndex) ending' ∧
      ((X.tr g).take nextIndex).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + loaderShuffleTail stop start ∧
      nextIndex ≤ j :=
  prefixCountedShuffleCutAtEntry hRange hAudit hCounted hs hr he hBefore hLater hSafe

end
end PTX.Kernels.TmlFa4Fwd.Loader
