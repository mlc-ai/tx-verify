-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorTrace
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyExactOrdinal
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.LoaderObservedCut
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part008
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part029

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
  (reuseArrival RingShape ringShapeOfAt pipelineAtCut walkWithArrivalClean loaderSegmentFrame
    loaderRingWrites loaderSliceEvents loaderEventAfterLocal loaderWaitTemplate
    pollBeforeSliceEvent loaderObservedCut loaderPipelineCutOp primingPacketSite copyCommitPc
    copyCommitCode loaderOutCore packetArrivalStep loaderTauBackEdge loaderBackEdges
    packetEventNext)

noncomputable section

private def dispatchFrame (l : Launch) (warp : Fin 2) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))]

private theorem keepDispatch {l : Launch} {warp : Fin 2} {t u : TState} {r : CursorRoute}
    (hf : Holds t.regs (dispatchFrame l warp)) (hRegs : [2535, 1062] ⊆ r.registers)
    (hKeep : ∀ reg ∈ r.registers, u.regs reg = t.regs reg) :
    Holds u.regs (dispatchFrame l warp) :=
  ⟨(hKeep 2535 (hRegs (by simp))).trans hf.1,
    (hKeep 1062 (hRegs (by simp))).trans hf.2.1, trivial⟩

private theorem publicationPc {e : Event} (h : recurringPublicationEvent e) :
    909 ≤ e.pc ∧ e.pc < 1744 := by
  obtain ⟨site, loc, rfl⟩ := h
  change 909 ≤ reuseArrival site ∧ reuseArrival site < 1744
  fin_cases site <;> decide

private theorem excludesExit {l : Launch} {g : Nat} {warp : Fin 2} {s : TState}
    {es : List Event} {vs : List Visit} {e : Event}
    (hPc : s.pc = 1901) (hShape : RingShape s) (hFrame : Holds s.regs (dispatchFrame l warp))
    (hw : Walk kernel Assumptions.all l g s es vs) (he : e ∈ es)
    (hPub : recurringPublicationEvent e) : False := by
  have hBounds := publicationPc hPub
  obtain ⟨site, loc, rfl⟩ := hPub
  have hAt := pipelineAtCut hPc hShape hFrame (walkWithArrivalClean hw he rfl)
    ⟨_, Flow.code_1901, rfl⟩
  have hPc := loaderTailEventPcs warp hAt hw _ he
  omega

private theorem excludesDrain {l : Launch} {g : Nat} {warp : Fin 2} {s : TState}
    {es : List Event} {vs : List Visit} {e : Event}
    (hIn : CursorRoute.drain.inside s.pc = true) (hShape : RingShape s)
    (hFrame : Holds s.regs (dispatchFrame l warp))
    (hw : Walk kernel Assumptions.all l g s es vs) (he : e ∈ es)
    (hPub : recurringPublicationEvent e) : False := by
  have hBounds := publicationPc hPub
  have hNo : CursorRoute.drain.inside e.pc = false := by
    simp [CursorRoute.inside, show ¬1744 ≤ e.pc by omega]
  rcases CursorRoute.drain.cutWalk hw hIn hShape with hAll |
    ⟨u, pre, tail, _, _, hEs, _, hBefore, hu, hShape', hKeep, hPre, hTail⟩
  · have := eventInside .drain hw hAll e he
    rw [hNo] at this
    contradiction
  have hEnds : u.pc = 1901 := by simpa [CursorRoute.stops] using hu
  rw [hEs] at he
  rcases List.mem_append.mp he with he | he
  · have := eventInside .drain hPre hBefore e he
    rw [hNo] at this
    contradiction
  exact excludesExit hEnds hShape' (keepDispatch hFrame (by decide) hKeep) hTail he hPub

private theorem getLastOfAppendRight {α : Type} {xs ys : List α} {e : α}
    (h : (xs ++ ys).getLast? = some e) (hne : ys ≠ []) : ys.getLast? = some e := by
  rw [List.getLast?_append] at h
  cases hs : ys.getLast? with
  | none => exact (hne (List.getLast?_eq_none_iff.mp hs)).elim
  | some => simpa [hs] using h

private theorem staysBeforeDrain {l : Launch} {g : Nat} {warp : Fin 2} {s : TState}
    {es : List Event} {vs : List Visit} {e : Event} (r : CursorRoute)
    (hStops : r.stops = [1744]) (hRegs : [2535, 1062] ⊆ r.registers)
    (hIn : r.inside s.pc = true) (hAt : At s s.pc (dispatchFrame l warp))
    (hw : Walk kernel Assumptions.all l g s es vs) (hLast : es.getLast? = some e)
    (hPub : recurringPublicationEvent e) :
    ∃ front, Walk kernel Assumptions.all l g s es front ∧ ∀ v ∈ front, r.inside v.pc = true := by
  rcases r.cutWalk hw hIn (ringShapeOfAt hAt) with hAll |
    ⟨u, pre, tail, front, _, hEs, _, hFront, hu, hShape, hKeep, hPre, hTail⟩
  · exact ⟨vs, hw, hAll⟩
  have hDest : u.pc = 1744 := by simpa [hStops] using hu
  cases tail with
  | nil => exact ⟨front, by simpa only [hEs, List.append_nil] using hPre, hFront⟩
  | cons first tail =>
    have hGet := getLastOfAppendRight (hEs ▸ hLast) (by simp)
    have hD : CursorRoute.drain.inside u.pc = true := by rw [hDest]; decide
    exact (excludesDrain hD hShape (keepDispatch hAt.2.2.2.2 hRegs hKeep) hTail
      (List.mem_of_getLast? hGet) hPub).elim

private theorem takeWhileAll {α : Type} (pred : α → Bool) {xs : List α}
    (h : ∀ x ∈ xs, pred x = true) : xs.takeWhile pred = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.takeWhile_cons_of_pos (h x (by simp)), ih (fun y hy => h y (by simp [hy]))]

private theorem primingArrivalBeforeRecurring {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {e : Event} (stage : Fin 2)
    (hs : At s ((primingEmptySite stage).pc + 3) [])
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hSeen : e ∈ loaderSliceEvents (if stage = 0 then 515 else 780) 1744 visits)
    (hPub : recurringPublicationEvent e) :
    ∃ target, ⟨copyCommitPc (primingPacketSite stage) + 1, .asyncArrive target true⟩ ∈ events := by
  let first := (primingEmptySite stage).pc + 3
  let cut := copyCommitPc (primingPacketSite stage) + 1
  let origin := if stage = 0 then 515 else 780
  have hb : 174 ≤ first ∧ origin ≤ first ∧ first < cut ∧ cut < 909 := by
    fin_cases stage <;> decide
  have hCode : ((kernel.code.drop first).take (cut - first)).all
      (fun i => loaderPipelineCutOp first cut (1744 - 1) [] i.op) = true := by
    fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hAfter := (publicationPc hPub).1
  have hStart : s.pc = first := hs.1
  have hReturn : ¬ Ends e := by obtain ⟨_, _, rfl⟩ := hPub; simp [Ends]
  obtain ⟨t, pre, tail, front, post, hEs, _, _, ht, _, _, _, hTail, hObserved⟩ :=
    loaderObservedCut (F := []) hb.2.1 hb.1 (by omega) (by omega) hCode hw
      ⟨hStart.ge, by omega⟩ (ringShapeOfAt hs) trivial hSeen (by omega) hReturn
  have hLater : e ∈ tail := by
    rw [hTail.events]
    obtain ⟨v, hv, he⟩ := List.mem_filterMap.mp hObserved
    exact List.mem_filterMap.mpr ⟨v, List.takeWhile_subset _ hv, he⟩
  cases hTail with
  | stop => cases hLater
  | @tau _ u _ _ hTau _ =>
    have hCore : Tau kernel [] l g t u := by
      unfold Tau at *
      rwa [← loaderOutCore (by omega) (by omega)]
    have hc := (copyCommitCode (primingPacketSite stage)).2
    change kernel.code[cut]? = _ at hc
    rw [← ht] at hc
    exact (tau_core_not_event hc rfl hCore).elim
  | last hStop =>
    obtain rfl := List.mem_singleton.mp hLater
    have hp := estep_source_pc hStop
    omega
  | ev hStep _ =>
    obtain ⟨target, hKind, _⟩ := packetArrivalStep (primingPacketSite stage) ht hStep
    have hPc := (estep_source_pc hStep).trans ht
    refine ⟨target, ?_⟩
    rw [hEs]
    apply List.mem_append_right
    have hSame := congrArg₂ Event.mk hPc hKind
    change _ = (⟨copyCommitPc (primingPacketSite stage) + 1, .asyncArrive target true⟩ : Event)
      at hSame
    rw [← hSame]
    exact List.mem_cons_self

private theorem primeFromCut {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {warp : Fin 2} {s : TState} {es : List Event} {vs : List Visit} {e : Event}
    (stage : Fin 2) (hs : At s (if stage = 0 then 515 else 780) (dispatchFrame l warp))
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hLast : es.getLast? = some e) (hPub : recurringPublicationEvent e) :
    let site := primingEmptySite stage
    let slot : Fin 3 := ⟨stage.val, by have := stage.isLt; omega⟩
    let poll := fun ok => (⟨site.pc, .wait (emptyObject l g slot) 1 ok true .cta⟩ : Event)
    ∃ n u tail visits, es = List.replicate n (poll false) ++ poll true :: tail ∧
      At u (site.pc + 3) (dispatchFrame l warp) ∧
      Walk kernel Assumptions.all l g u tail visits ∧ tail.getLast? = some e ∧
      (∃ target, ⟨copyCommitPc (primingPacketSite stage) + 1, .asyncArrive target true⟩ ∈ tail) :=
  by
  dsimp only
  let start := if stage = 0 then 515 else 780
  let site := primingEmptySite stage
  let addr := l.sharedBase + 8 * stage.val + 56
  have hBound : addr < 2 ^ 32 := by have := hp.shared.2.1; have := stage.isLt; dsimp [addr]; omega
  have hAlign : addr % 8 = 0 := by have := hp.shared.1; dsimp [addr]; omega
  let r := CursorRoute.throughPriming stage
  have hIn : r.inside s.pc = true := by rw [hs.1]; fin_cases stage <;> decide
  have hRegs : [2535, 1062] ⊆ r.registers := by
    simp [r, CursorRoute.registers]
  obtain ⟨front, hFront, hAll⟩ :=
    staysBeforeDrain r rfl hRegs hIn ⟨rfl, hs.2⟩ hw hLast hPub
  have hSlice : e ∈ loaderSliceEvents start 1744 front := by
    have hPred (v : Visit) (hv : v ∈ front) :
        (decide (start ≤ v.pc) && decide (v.pc < 1744)) = true := by
      have hP : (start ≤ v.pc ∧ v.pc < 1744) := of_decide_eq_true (hAll v hv)
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hP.1, decide_eq_true hP.2⟩
    rw [loaderSliceEvents, takeWhileAll _ hPred, ← hFront.events]
    exact List.mem_of_getLast? hLast
  obtain ⟨t, hr, ht⟩ := primingPollPrep stage hBound s (hs.mono ⟨hs.2.2.2.2.1, trivial⟩)
  have hLo : 174 ≤ start := by fin_cases stage <;> decide
  have hHi : start + 2 ≤ 1901 := by fin_cases stage <;> decide
  have hCode : ((kernel.code.drop start).take (start + 2 - start)).all
      (fun ins => schedulerFallsThrough ins.op &&
        [2535, 1062].all fun reg => !(loaderRingWrites ins.op).contains reg) = true := by
    fin_cases stage <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨_, hKeep⟩ := loaderSegmentFrame (regs := [2535, 1062]) hLo hHi hCode hr
    (Nat.le_of_eq hs.1.symm) (by rw [hs.1])
  let facts := [(site.base, b32 addr), (site.phase, b32 1)] ++ dispatchFrame l warp
  have hf : At t site.pc facts := ht.mono
    ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, (hKeep 2535 (by simp)).trans hs.2.2.2.2.1,
      (hKeep 1062 (by simp)).trans hs.2.2.2.2.2.1, trivial⟩
  obtain ⟨pre, hWalk, _, hSaw⟩ := loaderEventAfterLocal hr hFront hSlice
  have hRange : 174 ≤ site.pc ∧ site.pc + 3 < 1906 := by fin_cases stage <;> decide
  have hLower : start ≤ site.pc := by fin_cases stage <;> decide
  have hUpper : site.pc < 1744 := by fin_cases stage <;> decide
  have hBefore : site.pc < e.pc := by
    have hPc := (publicationPc hPub).1
    have hP : site.pc < 909 := by fin_cases stage <;> decide
    omega
  have hFresh : ∀ pair ∈ facts, pair.1 ≠ site.result := by
    intro pair hm
    fin_cases stage <;> simp [facts, site, primingEmptySite, dispatchFrame] at hm
    all_goals rcases hm with rfl | rfl | rfl | rfl <;> simp [site, primingEmptySite]
  obtain ⟨n, u, tail, visits, hEs, hu, hTail, hSeen⟩ :=
    pollBeforeSliceEvent site (primingEmptyCode stage) hRange hLower hUpper hFresh
      (fun _ ha => loaderWaitTemplate site (primingEmptyCode stage) hRange hBound hAlign
        (by decide) ha.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2.1) hf hWalk hBefore hSaw
  have hMem : e ∈ tail := by
    rw [hTail.events]
    obtain ⟨v, hv, he⟩ := List.mem_filterMap.mp hSeen
    exact List.mem_filterMap.mpr ⟨v, List.takeWhile_subset _ hv, he⟩
  have hLast' : tail.getLast? = some e := by
    apply getLastOfAppendRight (xs := List.replicate n _ ++ [_])
    · rw [List.append_assoc, List.singleton_append, ← hEs]
      exact hLast
    · exact List.ne_nil_of_mem hMem
  exact ⟨n, u, tail, visits, by
    simpa only [emptyObject, PTX.Kernels.TmlFa4Fwd.Loader.emptySlot_address] using hEs,
    hu.mono hu.2.2.2.2.2.2, hTail, hLast',
    primingArrivalBeforeRecurring stage (hu.mono trivial) hTail hSeen hPub⟩

private theorem primingArrivalCountBound {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (stage : Fin 2)
    (hw : Walk kernel Assumptions.all l g s events visits)
    (hRange : ∀ v ∈ visits, 174 ≤ v.pc ∧ v.pc < 1906) :
    let arrival := copyCommitPc (primingPacketSite stage) + 1
    events.countP (fun e => e.pc == arrival) ≤ if s.pc ≤ arrival then 1 else 0 := by
  dsimp only
  let arrival := copyCommitPc (primingPacketSite stage) + 1
  let mark := fun e : Event => e.pc == arrival
  have afterTau {t u : TState} (hBounds : 174 ≤ t.pc ∧ t.pc < 1906)
      (hAfter : arrival < t.pc) (hh : Tau kernel Assumptions.all l g t u) :
      arrival < u.pc := by
    by_contra! h
    have hEdge := loaderTauBackEdge hBounds.1 hBounds.2 (show u.pc ≤ t.pc by omega) hh
    have hCheck : loaderBackEdges.all
        (fun (src, dest) => !(arrival < src && dest ≤ arrival)) = true := by
      fin_cases stage <;> decide
    have hBad := List.all_eq_true.mp hCheck _ hEdge
    simp [h, hAfter] at hBad
  induction hw with
  | stop => simp
  | @tau t u es vs ht _ ih =>
    have hBounds : 174 ≤ t.pc ∧ t.pc < 1906 := hRange _ List.mem_cons_self
    have hTail := ih (fun v hv => hRange v (List.mem_cons_of_mem _ hv))
    change es.countP mark ≤ (if t.pc ≤ arrival then 1 else 0)
    change es.countP mark ≤ (if u.pc ≤ arrival then 1 else 0) at hTail
    by_cases hBefore : t.pc ≤ arrival
    · rw [ite_eq_left hBefore]
      split at hTail <;> omega
    · have hLater := afterTau hBounds (by omega) ht
      rw [ite_eq_right (Nat.not_le_of_lt hLater)] at hTail
      simpa only [ite_eq_right hBefore] using hTail
  | @ev t u en es vs he _ ih =>
    have hBounds : 174 ≤ t.pc ∧ t.pc < 1906 := hRange _ List.mem_cons_self
    have hTail := ih (fun v hv => hRange v (List.mem_cons_of_mem _ hv))
    change es.countP mark ≤ (if u.pc ≤ arrival then 1 else 0) at hTail
    have hPc := estep_source_pc he
    change (en :: es).countP mark ≤ if t.pc ≤ arrival then 1 else 0
    rw [List.countP_cons]
    by_cases hHere : t.pc = arrival
    · obtain ⟨_, _, hNext⟩ := packetArrivalStep (primingPacketSite stage) hHere he
      have hLater : ¬ u.pc ≤ arrival := by dsimp [arrival] at *; omega
      rw [ite_eq_right hLater] at hTail
      have hMarked : mark en = true := by simp [mark, hPc, hHere]
      rw [ite_eq_left (show t.pc ≤ arrival by omega), hMarked]
      simp only [ite_true]
      omega
    · have hNot : mark en = false := by simp [mark, hPc, hHere]
      simp only [hNot, Bool.false_eq_true, ite_false, Nat.add_zero]
      by_cases hBefore : t.pc ≤ arrival
      · rw [ite_eq_left hBefore]
        split at hTail <;> omega
      · have hNext := packetEventNext hBounds.1 hBounds.2 he
        have hLater : ¬ u.pc ≤ arrival := by omega
        rw [ite_eq_right hLater] at hTail
        simpa only [ite_eq_right hBefore] using hTail
  | @last t en he =>
    have hPc := estep_source_pc he
    change [en].countP mark ≤ if t.pc ≤ arrival then 1 else 0
    by_cases hBefore : t.pc ≤ arrival
    · cases h : mark en <;> simp [hBefore, h]
    · have hNot : mark en = false := by simp [mark, hPc, ne_of_gt (Nat.lt_of_not_ge hBefore)]
      simp [hNot, hBefore]

private theorem cutBeforePublication {l : Launch} {g stop start : Nat} {warp : Fin 2}
    {s : TState} {es : List Event} {vs : List Visit} {e : Event} (r : CursorRoute)
    (hs : At s start (dispatchFrame l warp)) (hIn : r.inside start = true)
    (hCodes : ∃ ins, kernel.code[stop]? = some ins ∧ ins.op.isLocal = true)
    (hRegs : [2535, 1062] ⊆ r.registers)
    (hStops : ∀ pc ∈ r.stops, pc = stop ∨ CursorRoute.drain.inside pc = true ∨ pc = 1901)
    (hBefore : ∀ pc, r.inside pc = true → 174 ≤ pc ∧ pc < 909)
    (hw : Walk kernel Assumptions.all l g s es vs) (hLast : es.getLast? = some e)
    (hPub : recurringPublicationEvent e) :
    ∃ u pre tail visits, es = pre ++ tail ∧ (∀ a ∈ pre, r.inside a.pc = true) ∧
      At u stop (dispatchFrame l warp) ∧ Walk kernel Assumptions.all l g u tail visits ∧
      tail.getLast? = some e ∧ ∀ stage : Fin 2,
        pre.countP (fun a => a.pc == copyCommitPc (primingPacketSite stage) + 1) ≤ 1 := by
  have hMem := List.mem_of_getLast? hLast
  have hBounds := publicationPc hPub
  rcases r.cutWalk hw (hs.1.symm ▸ hIn) (ringShapeOfAt hs) with hAll |
    ⟨u, pre, tail, _, visits, hEs, _, hFront, hStop, hShape, hKeep, hPre, hTail⟩
  · have h := (hBefore _ (eventInside r hw hAll e hMem)).2
    omega
  have hLeft := eventInside r hPre hFront
  have hSeen : e ∈ tail := by
    rw [hEs] at hMem
    refine (List.mem_append.mp hMem).resolve_left (fun he => ?_)
    have h := (hBefore _ (hLeft e he)).2
    omega
  have hLast' := getLastOfAppendRight (hEs ▸ hLast) (List.ne_nil_of_mem hSeen)
  have hFrame := keepDispatch hs.2.2.2.2 hRegs hKeep
  rcases hStops _ hStop with hPc | hDrain | hExit
  · obtain ⟨site, loc, rfl⟩ := hPub
    have hAt := pipelineAtCut hPc hShape hFrame (walkWithArrivalClean hTail hSeen rfl) hCodes
    refine ⟨u, pre, tail, visits, hEs, hLeft, hAt, hTail, hLast', ?_⟩
    intro stage
    have hBound := primingArrivalCountBound stage hPre fun v hv =>
      ⟨(hBefore _ (hFront v hv)).1, (hBefore _ (hFront v hv)).2.trans (by decide)⟩
    dsimp only at hBound
    split at hBound <;> omega
  · exact (excludesDrain hDrain hShape hFrame hTail hSeen hPub).elim
  · exact (excludesExit hExit hShape hFrame hTail hSeen hPub).elim

/-- The unsuccessful or successful poll in a priming packet. -/
def primingCursorPoll (l : Launch) (g : Nat) (stage : Fin 2) (ok : Bool) : Event :=
  ⟨(primingEmptySite stage).pc,
    .wait (emptyObject l g ⟨stage, by have := stage.isLt; omega⟩) 1 ok true .cta⟩

/-- The actual thread prefix through any recurring publication visits the two priming
empty waits in order. Its remaining successful empty waits follow the recurring cursor. -/
theorem actualLoaderCursorThrough {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (site : Fin 4) {g index : Nat} {target : Loc}
    (he : X.get (g, index) = some ⟨reuseArrival site, .asyncArrive target true⟩) :
    ∃ (pre0 pre1 pre2 rest : List Event) (nK nV : Nat),
      (X.tr g).take (index + 1) =
        (X.tr g).take 5 ++ pre0 ++
          (List.replicate nK (primingCursorPoll l g 0 false) ++ [primingCursorPoll l g 0 true]) ++
          pre1 ++
          (List.replicate nV (primingCursorPoll l g 1 false) ++ [primingCursorPoll l g 1 true]) ++
          pre2 ++ rest ∧
      (∀ e ∈ (X.tr g).take 5, e.pc ≤ 173) ∧
      (∀ e ∈ pre0, e.pc < 515) ∧ (∀ e ∈ pre1, 520 ≤ e.pc ∧ e.pc < 780) ∧
      (∀ e ∈ pre2, 785 ≤ e.pc ∧ e.pc < 909) ∧
      (∀ e ∈ rest, 909 ≤ e.pc ∧ e.pc < 1744) ∧
      (∃ target, (⟨674, .asyncArrive target true⟩ : Event) ∈ pre1) ∧
      (∃ target, (⟨904, .asyncArrive target true⟩ : Event) ∈ pre2) ∧
      pre1.countP (fun a => a.pc == 674) = 1 ∧ pre2.countP (fun a => a.pc == 904) = 1 ∧
      RecurringCursorTrace l g 2 rest := by
  let e : Event := ⟨reuseArrival site, .asyncArrive target true⟩
  have hPub : recurringPublicationEvent e := ⟨site, target, rfl⟩
  have hPc := publicationPc hPub
  dsimp only [e] at hPc
  have hHint : e.pc ∉ registerHintSites := by
    change reuseArrival site ∉ registerHintSites
    fin_cases site <;> decide
  have hLate : 173 < e.pc := by
    change 173 < reuseArrival site
    omega
  have hWarp : 14 ≤ warpIndex l g := by
    rcases roleBodyPcOfEvent hp hX he hLate hHint with h | h
    · change reuseArrival site = 9205 at h
      omega
    · dsimp only at h
      split_ifs at h <;> omega
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hNZ : 0 < warpIndex l g := by omega
  have hWord : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hWarp
  have hg := event_thread_lt hX he
  obtain ⟨s, o, hi, hs, hr⟩ :=
    nonzeroCommonPrefixOfLateEvent hp hX hg hNZ he hLate
  have hAt : At s 174 (dispatchFrame l warp) :=
    hs.mono ⟨hs.2.2.2.2.2.1, hWord.symm ▸ hs.2.2.2.2.1, trivial⟩
  have hEarly e' (hm : e' ∈ (X.tr g).take 5) : e'.pc ≤ 173 := by
    obtain ⟨i, hIn, rfl⟩ := List.getElem_of_mem hm
    have hIndex := hIn
    rw [List.length_take] at hIndex
    by_contra! hBad
    have hGet : X.get (g, i) = some ((X.tr g).take 5)[i] := by
      change (X.tr g)[i]? = _
      rw [List.getElem_take, List.getElem?_eq_getElem (by omega)]
    obtain ⟨_, _, hOld, _, _⟩ :=
      nonzeroCommonPrefixOfLateEvent hp hX hg hNZ hGet hBad
    omega
  obtain ⟨visits, hw⟩ := Mma.walkFromRun hr
  let body := ((X.tr g).drop 5).take (index - 5 + 1)
  obtain ⟨front, _, hFront⟩ := takeLoaderEvents hw (index - 5 + 1)
  have hGet : ((X.tr g).drop 5)[index - 5]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hi]
    exact he
  have hLast : body.getLast? = some e := by
    change (((X.tr g).drop 5).take (index - 5 + 1)).getLast? = _
    rw [List.take_add_one, hGet]
    simp
  obtain ⟨k, pre0, kTail, kVisits, hc0, hQuiet0, hk, hKWalk, hKLast, _⟩ :=
    cutBeforePublication .beforePriming hAt (by decide) ⟨_, Flow.code_515, rfl⟩ (by decide)
      (by
        intro pc hm
        simp [CursorRoute.stops] at hm
        rcases hm with rfl | rfl | rfl <;> decide)
      (by
        intro pc h
        have hr : 174 ≤ pc ∧ pc < 515 := of_decide_eq_true h
        exact ⟨hr.1, by omega⟩) hFront hLast hPub
  obtain ⟨nK, kEnd, preV, preVVisits, hcK, hkEnd, hPreV, hPreVLast, hPrimingK⟩ :=
    primeFromCut hp 0 hk hKWalk hKLast hPub
  obtain ⟨v, pre1, vTail, vVisits, hc1, hQuiet1, hv, hVWalk, hVLast, hKCount⟩ :=
    cutBeforePublication .betweenPriming hkEnd (by decide) ⟨_, Flow.code_780, rfl⟩ (by decide)
      (by simp [CursorRoute.stops])
      (by
        intro pc h
        have hr : 520 ≤ pc ∧ pc < 780 := of_decide_eq_true h
        exact ⟨by omega, by omega⟩) hPreV hPreVLast hPub
  obtain ⟨nV, vEnd, preSeed, preSeedVisits, hcV, hvEnd, hPreSeed, hPreSeedLast, hPrimingV⟩ :=
    primeFromCut hp 1 hv hVWalk hVLast hPub
  obtain ⟨seed, pre2, rest, restVisits, hc2, hQuiet2, hSeed, hRest, hRestLast, hVCount⟩ :=
    cutBeforePublication .beforeSeed hvEnd (by decide) ⟨_, Flow.code_909, rfl⟩ (by decide)
      (by simp [CursorRoute.stops])
      (by
        intro pc h
        have hr : 785 ≤ pc ∧ pc < 909 := of_decide_eq_true h
        exact ⟨by omega, hr.2⟩) hPreSeed hPreSeedLast hPub
  obtain ⟨finalVisits, hFinal, hAll⟩ := staysBeforeDrain .throughReuse rfl (by decide)
    (by rw [hSeed.1]; decide) ⟨rfl, hSeed.2⟩ hRest hRestLast hPub
  have hRange : ∀ x ∈ rest, 909 ≤ x.pc ∧ x.pc < 1744 := fun x hx =>
    of_decide_eq_true (eventInside .throughReuse hFinal hAll x hx)
  have hScope : ∀ visit ∈ finalVisits, visit.pc < 1744 := fun v hv =>
    (show 909 ≤ v.pc ∧ v.pc < 1744 from of_decide_eq_true (hAll v hv)).2
  obtain ⟨j, t, pre, tail, post, hCut, hSuf, ht, hPlane, hQuiet, hTail⟩ :=
    firstEmptyPacket (hSeed.mono ⟨hSeed.2.2.2.2.1, trivial⟩) hFinal hScope
      ⟨e, List.mem_of_getLast? hRestLast, hPub⟩
  have hMem : e ∈ tail := by
    have hm := List.mem_of_getLast? hRestLast
    rw [hCut] at hm
    exact (List.mem_append.mp hm).resolve_left (fun hm => (hQuiet e hm).1 hPub)
  have hTrace := recurringCursorPrefix hp j hPlane ht hTail
    (fun v hv => hScope v (hSuf.sublist.subset hv))
    (getLastOfAppendRight (hCut ▸ hRestLast) (List.ne_nil_of_mem hMem)) hPub
  have hK : ∃ target, (⟨674, .asyncArrive target true⟩ : Event) ∈ pre1 := by
    obtain ⟨target, hK⟩ := hPrimingK
    change (⟨674, .asyncArrive target true⟩ : Event) ∈ preV at hK
    rw [hc1, hcV, hc2] at hK
    refine ⟨target, (List.mem_append.mp hK).resolve_right ?_⟩
    intro h
    simp only [List.mem_append, List.mem_cons, List.mem_replicate] at h
    rcases h with ⟨_, h⟩ | h | h | h
    · cases congrArg Event.pc h
    · cases congrArg Event.pc h
    · have hPc := hQuiet2 _ h
      change (785 ≤ 674 && 674 < 909) = true at hPc
      cases hPc
    · have hLo := (hRange _ h).1
      change 909 ≤ 674 at hLo
      omega
  have hV : ∃ target, (⟨904, .asyncArrive target true⟩ : Event) ∈ pre2 := by
    obtain ⟨target, hV⟩ := hPrimingV
    change (⟨904, .asyncArrive target true⟩ : Event) ∈ preSeed at hV
    rw [hc2] at hV
    exact ⟨target, (List.mem_append.mp hV).resolve_right (fun h => by
      have hLo := (hRange _ h).1
      change 909 ≤ 904 at hLo
      omega)⟩
  have hKOnce : pre1.countP (fun a => a.pc == 674) = 1 := by
    obtain ⟨target, hm⟩ := hK
    have hLe : pre1.countP (fun a => a.pc == 674) ≤ 1 := hKCount 0
    have hPos : 0 < pre1.countP (fun a => a.pc == 674) :=
      List.countP_pos_iff.mpr ⟨_, hm, rfl⟩
    omega
  have hVOnce : pre2.countP (fun a => a.pc == 904) = 1 := by
    obtain ⟨target, hm⟩ := hV
    have hLe : pre2.countP (fun a => a.pc == 904) ≤ 1 := hVCount 1
    have hPos : 0 < pre2.countP (fun a => a.pc == 904) :=
      List.countP_pos_iff.mpr ⟨_, hm, rfl⟩
    omega
  refine ⟨pre0, pre1, pre2, rest, nK, nV, ?_, hEarly,
    fun x hx => (show 174 ≤ x.pc ∧ x.pc < 515 from of_decide_eq_true (hQuiet0 x hx)).2,
    fun x hx => of_decide_eq_true (hQuiet1 x hx), fun x hx => of_decide_eq_true (hQuiet2 x hx),
    hRange, hK, hV, hKOnce, hVOnce, hCut.symm ▸ RecurringCursorTrace.gap hQuiet hTrace⟩
  rw [show index + 1 = 5 + (index - 5 + 1) by omega, List.take_add]
  change (X.tr g).take 5 ++ body = _
  have hCut0 : body = pre0 ++ kTail := hc0
  rw [hCut0, hcK, hc1, hcV, hc2]
  simp only [primingCursorPoll, List.append_assoc, List.cons_append, List.nil_append]


end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
