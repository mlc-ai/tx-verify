-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionScanProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationTerminalExit
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputFree
import Kernels.TmlFa4Fwd.Proof.CorrectionLseFallback
import Kernels.TmlFa4Fwd.Proof.CorrectionPollPrefix
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Flow.Code.Part143
import Lemmas.Step.BarArrival
import Lemmas.Step.Released

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.MBarrier AsyncCopy Prologue Epilogue
open Thread.Output (freeObject)

noncomputable section

def terminalFreeFrame (l : Launch) (phase : Nat) : List (Nat × Value) :=
  [(7131,b32 (l.sharedBase + 232)),(7287,b32 phase)]

private theorem terminalFreeTemplate {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g phase : Nat} {t : TState} (hPhase : phase < 2)
    (ht : At t 9201 (terminalFreeFrame l phase)) :
    out kernel Assumptions.all l g t =
      .ev (.wait (freeObject l (g/l.block) 1) phase
        (fun ok => next (setReg t 9892 (.pred ok))) true .cta) := by
  have hSize : l.sharedBase + 232 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase + 232) % 8 = 0 := by have := hp.shared.1; omega
  have hLoc := mbarLoc_b32 (L := l) (g := g) ht.2.2.2.2.1 hSize hAlign
  have hBits : readBits l g t 32 (.reg 7287) = .ok (BitVec.ofNat 64 phase) := by
    have hSmall : phase < 2^32 := by omega
    simp only [readBits,readReg,ht.2.2.2.2.2.1,b32,truncBits_ofNat hSmall
      (by decide : 32 ≤ 64),bind,Except.bind,pure,Except.pure]
  have hNat : (BitVec.ofNat 64 phase).toNat = phase := toNat_ofNat_lt (by omega)
  rw [out_event ht.2.2.2.1 (ht.1.symm ▸ Flow.code_9201) rfl rfl]
  change Out.ev (eventTmpl Assumptions.all l g t (.mbarWait 9892 7131 0 (.reg 7287) true .cta)) =
    _
  have hScope : Assumptions.all.any (·.clusterScopeMbar t.pc) = false := rfl
  simp [eventTmpl, widenMbarScope, hScope, tmaTmpl, hLoc, hBits, hNat, bind, Except.bind, pure,
    Except.pure, ofExec, freeObject, show phase ≤ 1 by omega]

private theorem terminalFreeReleased {l : Launch} {X : Execution} {g j phase : Nat}
    {loc : Loc} {ok : Bool} (he : X.get (g,j) = some ⟨9201,.wait loc phase ok true .cta⟩)
    (hLast : j+1 = (X.tr g).length) : Step.Released l X g := by
  constructor
  intro site kind hGet _
  have hPos : (X.tr g).length-1 = j := by omega
  rw [hPos] at hGet ⊢
  rw [he] at hGet
  cases hGet
  exact Step.ready_of_wait he

private theorem terminalFreeRecorded {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g phase : Nat} (hg : g < l.threads) (hPhase : phase < 2) {current : State}
    (hObject : stateBefore (X.objects (freeObject l (g/l.block) 1))
        (X.objects (freeObject l (g/l.block) 1)).length = some current)
    (hReady : current.phase % 2 ≠ phase % 2) :
    ∀ (fuel pos : Nat) {t u : TState} {o : Option TState},
      (X.tr g).length-pos = fuel → 0 < pos → pos ≤ (X.tr g).length →
      (pos = (X.tr g).length → Step.Released l X g) →
      At u 9201 (terminalFreeFrame l phase) →
      Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) →
      Run kernel Assumptions.all l g t ((X.tr g).drop pos) o →
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u →
      ∃ j v w, X.get (g,j) = some ⟨9201,.wait (freeObject l (g/l.block) 1) phase true true .cta⟩ ∧
        At w 9204 (terminalFreeFrame l phase) ∧
        Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some v) ∧
        Run kernel Assumptions.all l g v ((X.tr g).drop (j+1)) o ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l g) v w := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro pos t u o hFuel hPos hBound hRelease hu hPrefix hTail hLocal
    let loc := freeObject l (g/l.block) 1
    let post := fun ok => next (setReg u 9892 (.pred ok))
    have hOut : out kernel Assumptions.all l g u =
        .ev (.wait loc phase post true .cta) := terminalFreeTemplate hp hPhase hu
    have hn : Next kernel Assumptions.all l g t u (.wait loc phase post true .cta) := ⟨hLocal,hOut⟩
    have hMore : pos < (X.tr g).length := by
      by_contra! hNo
      have hEq := Nat.le_antisymm hBound hNo
      have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEq; omega
      have hFull : Run kernel Assumptions.all l g {} (X.tr g) (some t) := by
        rw [← List.take_of_length_le hNo]
        exact hPrefix
      have hES : EStep kernel Assumptions.all l g u
          ⟨u.pc,.wait loc phase true true .cta⟩ (some (post true)) :=
        ⟨_,hOut,true,rfl,rfl⟩
      exact hMax.not_grows (Step.poll_counted_extension hMax.1 hg hStarted (hRelease hEq)
        (fun a ha _ _ => Assumptions.wfStep.quiet hMax.1
          (Execution.le_trans le_snoc (Execution.le_appendObject ..)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl)) a ha)
        hFull hLocal hES hObject hReady)
    obtain ⟨_, _, hGet, ⟨ok,rfl,hRet⟩, hRest⟩ := hn.continuing_at_nonempty
      (by rintro _ ⟨_,_,hBad⟩; cases hBad) hTail
      (fun h => (Nat.not_le_of_lt hMore) (List.drop_eq_nil_iff.mp h))
    obtain rfl := Option.some.inj hRet
    have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (post ok)) := by
      rw [List.take_succ_eq_append_getElem hMore, (List.getElem?_eq_some_iff.mp hGet).2]
      exact hPrefix.snoc hLocal ⟨_,hOut,ok,rfl,rfl⟩
    obtain ⟨w, hw, hPc, hSub, hFault, hRegs, hZero, hEmpty⟩ :=
      correctionPollLocals (4 : Fin 5) (l := l) (g := g) hu.1 hu.2.2.2.1 ok
    have hRegisters : Holds w.regs (terminalFreeFrame l phase) := by
      rw [hRegs]
      exact holds_update hu.2.2.2.2 (by simp [terminalFreeFrame, correctionPoll])
    have hAt : At w (if ok then 9204 else 9201) (terminalFreeFrame l phase) :=
      ⟨hPc, hZero hu.2.1, hEmpty hu.2.2.1, hFault, hRegisters⟩
    rw [hu.1] at hGet
    cases ok with
    | true => exact ⟨pos,_,w,hGet,hAt,hPast,hRest,run_rtg hw⟩
    | false =>
      exact ih ((X.tr g).length-(pos+1)) (by omega) (pos+1) rfl (by omega)
        (len_of_get hGet) (terminalFreeReleased hGet) hAt hPast hRest (run_rtg hw)

/-- A correction lane that reached its terminal free-slot wait records its
allocation arrival when the final staging generation has been released. -/
theorem finalArrivalOfTerminalFree {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g phase pos : Nat} (hg : g < l.threads) (hPhase : phase < 2)
    (hReady : let log := X.objects (freeObject l (g/l.block) 1)
      ∃ s, stateBefore log log.length = some s ∧ s.phase % 2 ≠ phase % 2)
    {t u : TState} {o : Option TState}
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Step.Released l X g)
    (hAt : At u 9201 (terminalFreeFrame l phase))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) :
    ∃ j t o, Thread.FinalAllocationArrival X (g,j) .arrive ∧ At t 9205 [] ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o := by
  obtain ⟨s,hs,hAvail⟩ := hReady
  obtain ⟨j,v,w,he,hW,hPast,hRun,hwLocal⟩ := terminalFreeRecorded hp hMax hg hPhase
    hs hAvail ((X.tr g).length-pos) pos rfl hPos hBound hRelease
    hAt hPrefix hTail hLocal
  have hOut : out kernel Assumptions.all l g w = .ev (.bar 2 (next w) (some 416) .arrive) := by
    rw [out_event hW.2.2.2.1 (by rw [hW.1]; exact Flow.code_9204) rfl rfl]
    simp [eventTmpl, barTmpl, readBits, pure, Except.pure, hp.block,
      show (truncBits 32 2#64).toNat = 2 by decide,
      show (truncBits 32 416#64).toNat = 416 by decide]
  have hj : j+1 < (X.tr g).length := by
    by_contra! hLe
    have hLen : j+1 = (X.tr g).length := Nat.le_antisymm (len_of_get he) hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hLen; omega
    rw [List.take_of_length_le hLe] at hPast
    exact hMax.not_grows (Step.barArrival_counted_extension hMax.1 hg (.inl hStarted)
      (terminalFreeReleased he hLen) (Assumptions.wfStep.quiet hMax.1 le_snoc rfl
        (Execution.noNewRead_snoc rfl))
      hPast hwLocal ⟨_,hOut,rfl,rfl⟩)
  have hn : Next kernel Assumptions.all l g v w (.bar 2 (next w) (some 416) .arrive) :=
    ⟨hwLocal,hOut⟩
  obtain ⟨_, _, hGet, ⟨rfl,hRet⟩, hRest⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) hRun
    (fun h => (Nat.not_le_of_lt hj) (List.drop_eq_nil_iff.mp h))
  obtain rfl := Option.some.inj hRet
  have hPre : Run kernel Assumptions.all l g {} ((X.tr g).take (j+1+1))
      (some (next w)) := by
    rw [List.take_succ_eq_append_getElem hj, (List.getElem?_eq_some_iff.mp hGet).2]
    exact hPast.snoc hwLocal ⟨_,hOut,rfl,rfl⟩
  have hAt' := hW.next.mono (show Holds (next w).regs [] from trivial)
  exact ⟨j+1,next w,o,Thread.FinalAllocationArrival.of_decoded (by decide) (hW.1 ▸ hGet),
    hAt',hPre,hRest⟩

private theorem idleFinalArrivalAtExhausted {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles : Nat} (hg : g < l.threads)
    (hReady : let log := X.objects (freeObject l (g/l.block) 1)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0)
    {ends : Nat → Option TState}
    (done : SchedulerWarpReached l X g 7864
      (fun lane => Fallback.exhaustedScheduleFacts p (Fallback.fallbackFrame p l g lane))
      shuffles 0 ends) :
    ∃ j t o, Thread.FinalAllocationArrival X (g,j) .arrive ∧ At t 9205 ([]) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨cur⟩ := done.advanceLocal (G := fun _ => terminalFreeFrame l 1) (pc' := 9201) (by
    intro lane hl
    exact exhaustedTileRun hp (done.checkpoint lane hl))
  let pos := cur.pos lane
  let t := cur.before lane
  let u := cur.state lane
  have hAt : At u 9201 (terminalFreeFrame l 1) := cur.checkpoint lane hl
  have hBound : pos ≤ (X.tr g).length := by simpa only [pos,hSelf] using cur.bounded lane hl
  have hRelease : pos = (X.tr g).length → Step.Released l X g := by
    simpa only [pos,hSelf] using cur.released lane hl
  have hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t) := by
    simpa only [pos,t,hSelf] using cur.recorded lane hl
  have hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) (ends lane) := by
    simpa only [pos,t,hSelf] using cur.continuation lane hl
  have hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
    simpa only [t,u,hSelf] using cur.localSteps lane hl
  exact finalArrivalOfTerminalFree hp hMax hg (by decide)
    (by obtain ⟨s,hs,hZero⟩ := hReady; exact ⟨s,hs,by rw [hZero]; decide⟩)
    (cur.positive lane hl) hBound hRelease hAt hPrefix hTail hLocal

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) (hProtected : DrainCuQProtected p X)
include hp hMax hg hLo hHi hProtected

/-- An idle correction lane reaches its final allocation arrival after searching any batch. -/
theorem idleFinalArrivalPrefixForBatches (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block)
    (hReady : let log := X.objects (freeObject l (g/l.block) 1)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    ∃ j t o, Thread.FinalAllocationArrival X (g,j) .arrive ∧ At t 9205 ([]) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (j+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) o := by
  have hRoute := firstGroupRouteOfMaximal hp hMax hg hLo hHi hProtected
  have hCut : tilePrefix p (min p.batch 31) * p.heads ≤ g / l.block :=
    (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left ..))).trans hIdle
  rw [ite_eq_right (Nat.not_lt_of_ge hCut)] at hRoute
  obtain ⟨_,⟨route⟩⟩ := hRoute
  obtain ⟨done⟩ := Fallback.idleSearchExhaustedOfMaximal hp hMax hg hIdle hProtected route
  exact idleFinalArrivalAtExhausted hp hMax hg hReady done

/-- An idle correction lane of any batch records its final allocation arrival once the
output-free object is initialized at phase zero. -/
theorem idleFinalArrivalForBatchesOfPhaseZero (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block)
    (hReady : let log := X.objects (freeObject l (g/l.block) 1)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    ∃ j, Thread.FinalAllocationArrival X (g,j) .arrive := by
  obtain ⟨j,_,_,hArrival,_,_,_⟩ :=
    idleFinalArrivalPrefixForBatches hp hMax hg hLo hHi hProtected hIdle hReady
  exact ⟨j,hArrival⟩

/-- An idle correction lane records its exit after the matching deallocation. -/
theorem idleExitForBatchesOfDeallocation (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block)
    (hReady : let log := X.objects (freeObject l (g / l.block) 1)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) {d : EvId}
    (hCta : g / l.block = d.1 / l.block) (hDealloc : Thread.Deallocation X d) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  obtain ⟨j,t,o,hArrival,ht,hPrefix,hTail⟩ :=
    idleFinalArrivalPrefixForBatches hp hMax hg hLo hHi hProtected hIdle hReady
  have hNext : Next kernel Assumptions.all l g t t .exit := by
    refine ⟨.refl,?_⟩
    rw [epilogue_out_all_eq_nil (by unfold EpiloguePc; rw [ht.1]; decide),
      out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_9205) rfl rfl]
    rfl
  obtain ⟨site,_,hGet⟩ := hArrival.decoded
  exact ⟨j+1,_,Thread.exitAtMaximalCursor hMax hg (by omega) (len_of_get hGet)
    hPrefix hTail hNext
    (fun h => hArrival.releasedOfDeallocation hp hMax.1 hCta h hDealloc),rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
