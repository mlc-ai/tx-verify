-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyCycle
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorTrace
import Kernels.TmlFa4Fwd.Flow.Code.Part029
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyOrdinal
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Lemmas.Step.ExitLast
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderTransitions
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
  (drainWaitSite loaderPhaseWord loaderLinear drainWaitTrace kvUseStage kvEmptyPhase
    loaderRingWordsOfUse emptySlot_address prefixStableCut loaderPipelineCutOp)

noncomputable section

private def drainStageReg : Fin 3 → Nat
  | 0 => 7179
  | 1 => 2296
  | 2 => 2301

private def drainWords (l : Launch) (i : Fin 3) (stage : Fin 3) (bit : Bool) :
    List (Nat × Value) :=
  let site := drainWaitSite ⟨i.val, by omega⟩
  [(2535, b32 l.sharedBase), (drainStageReg i, b32 stage.val),
    (site.phase, loaderPhaseWord bit), (site.base, b32 (l.sharedBase + 8 * stage.val + 56))]

/-- The semantic acquire at a chosen position of the final drain. -/
def drainPoll (l : Launch) (g : Nat) (i : Fin 3) (use : Nat) (ok : Bool) : Event :=
  ⟨(drainWaitSite ⟨i.val, by omega⟩).pc,
    .wait (emptyObject l g (kvUseStage use)) (if kvEmptyPhase use then 1 else 0) ok true .cta⟩

private theorem boundsFromStage {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (stage : Fin 3) : l.sharedBase + 8 * stage.val + 56 < 2 ^ 32 := by
  have := hp.shared.2.1
  have := stage.isLt
  omega

private theorem firstDrainWordsFramed {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (stage : Fin 3) (bit : Bool)
    {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop 1863).take 3).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true) :
    Seg kernel Assumptions.all l g 3 1863
      ([(2535, b32 l.sharedBase), (7179, b32 stage.val), (7180, loaderPhaseWord bit)] ++ F)
      1866 (drainWords l 0 stage bit ++ F) := by
  have hBase : l.sharedBase + 72 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hCore : Seg kernel [] l g 3 1863
      [(2535, b32 l.sharedBase), (7179, b32 stage.val), (7180, loaderPhaseWord bit)]
      1866 (drainWords l 0 stage bit) := by
    fin_cases stage <;> intro t ht
    all_goals
      simp only [drainWords, drainStageReg, drainWaitSite]
      seg_fp ht using norm_bits
  intro t ht
  have hRegs := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨u,hRun,hu⟩ := hCore t (ht.mono hRegs.1)
  obtain ⟨hPath,hFrame⟩ := loaderLinear (by decide) (by decide) ht.1 hKeep
    (by set_option maxRecDepth 100000 in kernel_rfl) hRun
  exact ⟨u,hPath,hu.mono ((holds_append ..).mpr ⟨hu.2.2.2.2,
    Epilogue.holdsSchedulerFrame hRegs.2 hFrame (fun _ hm => List.mem_map_of_mem hm)⟩)⟩

private theorem firstDrainWords {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (stage : Fin 3) (bit : Bool) :
    Seg kernel Assumptions.all l g 3 1863
      [(2535,b32 l.sharedBase),(7179,b32 stage.val),(7180,loaderPhaseWord bit)]
      1866 (drainWords l 0 stage bit) :=
  firstDrainWordsFramed hp stage bit (F := []) (by simp)

private theorem drainWordsAdvanceFramed {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (i : Fin 2) (stage : Fin 3) (bit : Bool)
    {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop ((drainWaitSite ⟨i.val,by omega⟩).pc + 3)).take 8).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true) :
    let prev : Fin 3 := ⟨i.val, by omega⟩
    let nextSite : Fin 3 := ⟨i.val + 1, by omega⟩
    Seg kernel Assumptions.all l g 8 ((drainWaitSite ⟨prev.val, by omega⟩).pc + 3)
      (drainWords l prev stage bit ++ F) (drainWaitSite ⟨nextSite.val, by omega⟩).pc
      (drainWords l nextSite ⟨(stage.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
        (Loader.loaderNextPhase stage bit) ++ F) := by
  have hBase : l.sharedBase + 72 < 2 ^ 32 := by have := hp.shared.2.1; omega
  dsimp only
  intro t hAt
  have hRegs := (holds_append ..).mp hAt.2.2.2.2
  have ht := hAt.mono hRegs.1
  have hCore : ∃ u, run kernel [] l g 8 t = some u ∧
      At u (drainWaitSite ⟨i.val + 1, by omega⟩).pc
        (drainWords l ⟨i.val + 1, by omega⟩
          ⟨(stage.val + 1) % 3, Nat.mod_lt _ (by decide)⟩ (Loader.loaderNextPhase stage bit)) := by
    fin_cases i <;> fin_cases stage <;> cases bit
    all_goals
      simp only [drainWords, drainStageReg, drainWaitSite, Loader.loaderNextPhase, loaderPhaseWord]
        at ht ⊢
      seg_fp ht using first | decide +kernel | norm_bits
  obtain ⟨u, hRun, hu⟩ := hCore
  let src := (drainWaitSite ⟨i.val, by omega⟩).pc + 3
  have hBounds : ∀ j : Fin 2, 174 ≤ (drainWaitSite ⟨j.val, by omega⟩).pc + 3 ∧
      (drainWaitSite ⟨j.val, by omega⟩).pc + 3 + 8 ≤ 1906 := by
    intro j
    fin_cases j
    · change 174 ≤ 1869 ∧ 1877 ≤ 1906
      decide
    · change 174 ≤ 1880 ∧ 1888 ≤ 1906
      decide
  obtain ⟨hLo, hHi⟩ := hBounds i
  have hSeq : ((kernel.code.drop src).take 7).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases i <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hPath,hFrame⟩ := loaderLinear hLo hHi ht.1 hKeep hSeq hRun
  exact ⟨u,hPath,hu.mono ((holds_append ..).mpr ⟨hu.2.2.2.2,
    Epilogue.holdsSchedulerFrame hRegs.2 hFrame (fun _ hm => List.mem_map_of_mem hm)⟩)⟩

private theorem drainWordsAdvance {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (i : Fin 2) (stage : Fin 3) (bit : Bool) :
    let prev : Fin 3 := ⟨i.val,by omega⟩
    let nextSite : Fin 3 := ⟨i.val+1,by omega⟩
    Seg kernel Assumptions.all l g 8 ((drainWaitSite ⟨prev.val,by omega⟩).pc+3)
      (drainWords l prev stage bit) (drainWaitSite ⟨nextSite.val,by omega⟩).pc
      (drainWords l nextSite ⟨(stage.val+1)%3,Nat.mod_lt _ (by decide)⟩
        (Loader.loaderNextPhase stage bit)) :=
  drainWordsAdvanceFramed hp i stage bit (F := []) (by simp)

private theorem drainSlotTrace {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g use : Nat} (i : Fin 3) {s : TState} {events : List Event}
    (hs : At s (drainWaitSite ⟨i.val, by omega⟩).pc
      (drainWords l i (kvUseStage use) (kvEmptyPhase use)))
    (hr : Run kernel Assumptions.all l g s events none) :
    ∃ n u rest, events = List.replicate n (drainPoll l g i use false) ++
        drainPoll l g i use true :: rest ∧
      At u ((drainWaitSite ⟨i.val, by omega⟩).pc + 3)
        (drainWords l i (kvUseStage use) (kvEmptyPhase use)) ∧
      Run kernel Assumptions.all l g u rest none := by
  have hPhase : (if kvEmptyPhase use then 1 else 0) < 2 := by split <;> decide
  have hAlign : (l.sharedBase + 8 * (kvUseStage use).val + 56) % 8 = 0 := by
    have := hp.shared.1
    omega
  have hFresh : ∀ pair ∈ drainWords l i (kvUseStage use) (kvEmptyPhase use),
      pair.1 ≠ (drainWaitSite ⟨i.val, by omega⟩).result := by
    fin_cases i <;> simp [drainWords, drainStageReg, drainWaitSite]
  obtain ⟨n, u, rest, hEvents, hu, hRun⟩ :=
    drainWaitTrace ⟨i.val, by omega⟩ (boundsFromStage hp (kvUseStage use)) hAlign hPhase
      hFresh (by simp [drainWords]) (by simp [drainWords, loaderPhaseWord]) hs hr
  exact ⟨n, u, rest, by simpa only [drainPoll, emptyObject, emptySlot_address] using hEvents,
    hu, hRun⟩

private theorem drainWordsNext (l : Launch) (i : Fin 3) (use : Nat) :
    drainWords l i ⟨((kvUseStage use).val + 1) % 3, Nat.mod_lt _ (by decide)⟩
        (Loader.loaderNextPhase (kvUseStage use) (kvEmptyPhase use)) =
      drainWords l i (kvUseStage (use + 1)) (kvEmptyPhase (use + 1)) := by
  have hStage : (⟨((kvUseStage use).val + 1) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) =
      kvUseStage (use + 1) := by
    apply Fin.ext
    change (use % 3 + 1) % 3 = (use + 1) % 3
    omega
  have hWord := congrArg (fun words : List (Nat × Value) => words[1]?.map Prod.snd)
    (loaderRingWordsOfUse use)
  change some (loaderPhaseWord (Loader.loaderNextPhase (kvUseStage use) (kvEmptyPhase use))) =
    some (loaderPhaseWord (kvEmptyPhase (use + 1))) at hWord
  rw [hStage]
  unfold drainWords
  rw [Option.some.inj hWord]

/-- The drain waits once on each of the three consecutive cursor positions. The
cursor is the next unused ring position after the last ordinary publication. -/
theorem ringDrainTrace {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use : Nat} {s : TState} {events : List Event}
    (hs : At s 1863 [(2535, b32 l.sharedBase), (7179, b32 (kvUseStage use).val),
      (7180, loaderPhaseWord (kvEmptyPhase use))])
    (hr : Run kernel Assumptions.all l g s events none) :
    ∃ n0 n1 n2 u rest,
      events =
        (List.replicate n0 (drainPoll l g 0 use false) ++ [drainPoll l g 0 use true]) ++
        (List.replicate n1 (drainPoll l g 1 (use + 1) false) ++ [drainPoll l g 1 (use + 1) true]) ++
        (List.replicate n2 (drainPoll l g 2 (use + 2) false) ++ [drainPoll l g 2 (use + 2) true]) ++
        rest ∧ u.pc = 1891 ∧ u.regs 2535 = some (b32 l.sharedBase) ∧
      Run kernel Assumptions.all l g u rest none := by
  obtain ⟨s0, h0, hs0⟩ := firstDrainWords hp (kvUseStage use) (kvEmptyPhase use) s hs
  obtain ⟨n0, u0, tail0, he0, hu0, hTail0⟩ := drainSlotTrace hp 0 hs0 (hr.after_local (run_rtg h0))
  obtain ⟨s1, h1, hs1⟩ := drainWordsAdvance hp (g := g) 0 (kvUseStage use) (kvEmptyPhase use) u0 hu0
  change At s1 1877 (drainWords l 1 ⟨((kvUseStage use).val + 1) % 3, _⟩
    (Loader.loaderNextPhase (kvUseStage use) (kvEmptyPhase use))) at hs1
  rw [drainWordsNext l 1 use] at hs1
  obtain ⟨n1, u1, tail1, he1, hu1, hTail1⟩ := drainSlotTrace hp 1 hs1
    (hTail0.after_local (run_rtg h1))
  obtain ⟨s2, h2, hs2⟩ :=
    drainWordsAdvance hp (g := g) 1 (kvUseStage (use + 1)) (kvEmptyPhase (use + 1)) u1 hu1
  change At s2 1888 (drainWords l 2 ⟨((kvUseStage (use + 1)).val + 1) % 3, _⟩
    (Loader.loaderNextPhase (kvUseStage (use + 1)) (kvEmptyPhase (use + 1)))) at hs2
  rw [drainWordsNext l 2 (use + 1)] at hs2
  obtain ⟨n2, u, rest, he2, hu, hTail⟩ := drainSlotTrace hp 2 hs2
    (hTail1.after_local (run_rtg h2))
  refine ⟨n0, n1, n2, u, rest, ?_, hu.1, hu.2.2.2.2.1, hTail⟩
  simp only [he0, he1, he2, List.append_assoc, List.cons_append, List.nil_append, Nat.add_assoc]

/-- The three physical registers that encode the next K/V use. -/
def drainCarry (l : Launch) (use : Nat) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (7179, b32 (kvUseStage use).val),
    (7180, loaderPhaseWord (kvEmptyPhase use))]

/-- At the drain, all three ring positions have reached their next empty generation. -/
def CacheDrainReady (l : Launch) (X : Execution) (g use : Nat) : Prop :=
  ∀ i : Fin 3,
    let n := use+i.val
    let log := X.objects (emptyObject l g (kvUseStage n))
    ∃ s, MBarrier.stateBefore log log.length = some s ∧
      s.phase%2 ≠ (if kvEmptyPhase n then 1 else 0)

private theorem acquireDrainSlotOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use shuffles votes : Nat} (hg : g < l.threads) (hReady : CacheDrainReady l X g use)
    (i : Fin 3) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (drainWaitSite ⟨i.val,by omega⟩).pc
      (fun lane => drainWords l i (kvUseStage (use+i.val)) (kvEmptyPhase (use+i.val)) ++ F lane)
      shuffles votes ends)
    (hFresh : ∀ lane < 32, (drainWaitSite ⟨i.val,by omega⟩).result ∉ (F lane).map Prod.fst) :
    Nonempty (SchedulerWarpReached l X g ((drainWaitSite ⟨i.val,by omega⟩).pc+3)
      (fun lane => drainWords l i (kvUseStage (use+i.val)) (kvEmptyPhase (use+i.val)) ++ F lane)
      shuffles votes ends) := by
  let site : Fin 4 := ⟨i.val,by omega⟩
  let n := use+i.val
  let addr := l.sharedBase + 8*(kvUseStage n).val + 56
  let phase := if kvEmptyPhase n then 1 else 0
  have hPhase : phase < 2 := by dsimp only [phase]; split <;> decide
  have hAlign : addr % 8 = 0 := by have := hp.shared.1; dsimp [addr]; omega
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hAddress : emptyObject l g (kvUseStage n) = ⟨.shared,g/l.block,addr⟩ := by
    simp only [emptyObject,emptySlot_address,addr]
  obtain ⟨current,hObject,hReady⟩ := hReady i
  rw [hAddress] at hObject
  obtain ⟨done,_⟩ := PTX.Kernels.TmlFa4Fwd.Loader.loaderWarpWaitOfOppositePhaseTrace
    hMax hg hBlock (Loader.drainWaitCode site) (by have h := Loader.drainWaitRange site; omega)
    (boundsFromStage hp (kvUseStage n)) hAlign hPhase cur
    (by
      intro lane hl pair hm hEq
      rcases List.mem_append.mp hm with hm | hm
      · have hNo : (drainWaitSite site).result ∉
            (drainWords l i (kvUseStage n) (kvEmptyPhase n)).map Prod.fst := by
          fin_cases i <;> exact of_decide_eq_true rfl
        exact hNo (hEq ▸ List.mem_map_of_mem hm)
      · exact hFresh lane hl (hEq ▸ List.mem_map_of_mem hm))
    (fun _ _ => List.mem_append_left _ (by simp [drainWords,site,n]))
    (fun _ _ => List.mem_append_left _ (by simp [drainWords,site,phase,n,loaderPhaseWord]))
    (fun _ _ {_ _} _ _ _ => ⟨current,hObject,by
      have hMod : phase%2 = phase := Nat.mod_eq_of_lt hPhase
      rw [hMod]
      exact hReady⟩)
  exact ⟨done⟩

/-- A warp at the final ring cursor receives each of the three actual empty releases.
The caller's frame survives the local setup and all recorded poll attempts. -/
theorem cacheDrainOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use shuffles votes : Nat} (hg : g < l.threads) (hReady : CacheDrainReady l X g use)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1863 (fun lane => drainCarry l use ++ F lane)
      shuffles votes ends)
    (hKeep : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ [258,7192,1062]) :
    Nonempty (SchedulerWarpReached l X g 1891 (fun lane => (2535,b32 l.sharedBase)::F lane)
      shuffles votes ends) := by
  have hFresh (i : Fin 3) (lane : Nat) (hl : lane < 32) :
      (drainWaitSite ⟨i.val,by omega⟩).result ∉ (F lane).map Prod.fst := by
    intro hm
    obtain ⟨pair,hp,hEq⟩ := List.mem_map.mp hm
    have hMem := hKeep lane hl pair hp
    rw [hEq] at hMem
    fin_cases i <;> simp [drainWaitSite] at hMem
  have hFrame {lo count : Nat}
      (hCode : ((kernel.code.drop lo).take count).all
        (fun i => ([258,7192,1062] : List Nat).all
          (fun r => !(writesRegs i.op).contains r)) = true)
      (lane : Nat) (hl : lane < 32) :
      ((kernel.code.drop lo).take count).all
        (fun i => ((F lane).map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) =
        true := by
    apply List.all_eq_true.mpr
    intro i hi
    apply List.all_eq_true.mpr
    intro r hr
    obtain ⟨pair,hPair,rfl⟩ := List.mem_map.mp hr
    exact List.all_eq_true.mp (List.all_eq_true.mp hCode i hi) _ (hKeep lane hl _ hPair)
  obtain ⟨start0⟩ := cur.advanceLocal (pc' := 1866)
    (G := fun lane => drainWords l 0 (kvUseStage use) (kvEmptyPhase use) ++ F lane) (by
      intro lane hl
      obtain ⟨u,hRun,hU⟩ := firstDrainWordsFramed hp (kvUseStage use) (kvEmptyPhase use)
        (hFrame (by set_option maxRecDepth 100000 in kernel_rfl) lane hl) _ (cur.checkpoint lane hl)
      exact ⟨u,run_rtg hRun,hU⟩)
  obtain ⟨done0⟩ := acquireDrainSlotOfMaximal hp hMax hg hReady 0 (by
    change SchedulerWarpReached l X g 1866
      (fun lane => drainWords l 0 (kvUseStage use) (kvEmptyPhase use) ++ F lane)
      shuffles votes ends
    exact start0) (hFresh 0)
  have hAdvance (i : Fin 2) (atUse : Nat)
      (before : SchedulerWarpReached l X g ((drainWaitSite ⟨i.val,by omega⟩).pc+3)
        (fun lane => drainWords l ⟨i.val,by omega⟩ (kvUseStage atUse) (kvEmptyPhase atUse) ++
          F lane) shuffles votes ends) :
      Nonempty (SchedulerWarpReached l X g (drainWaitSite ⟨i.val+1,by omega⟩).pc
        (fun lane => drainWords l ⟨i.val+1,by omega⟩ (kvUseStage (atUse+1))
          (kvEmptyPhase (atUse+1)) ++ F lane) shuffles votes ends) := by
    apply before.advanceLocal
    intro lane hl
    obtain ⟨u,hRun,hU⟩ := drainWordsAdvanceFramed hp i (kvUseStage atUse) (kvEmptyPhase atUse)
      (hFrame (by fin_cases i <;> decide +kernel) lane hl) _ (before.checkpoint lane hl)
    rw [drainWordsNext l ⟨i.val+1,by omega⟩ atUse] at hU
    exact ⟨u,run_rtg hRun,hU⟩
  obtain ⟨start1⟩ := hAdvance 0 use done0
  obtain ⟨done1⟩ := acquireDrainSlotOfMaximal hp hMax hg hReady 1 start1 (hFresh 1)
  obtain ⟨start2⟩ := hAdvance 1 (use+1) done1
  obtain ⟨done2⟩ := acquireDrainSlotOfMaximal hp hMax hg hReady 2 start2 (hFresh 2)
  exact done2.advanceLocal (fun lane hl => by
    have hAt := done2.checkpoint lane hl
    have hReg := (holds_append ..).mp hAt.2.2.2.2
    exact ⟨_,.refl,hAt.mono ⟨hReg.1.1,hReg.2⟩⟩)

/-- The scheduler in the drain keeps the K/V cursor until its final wait setup. -/
theorem drainEntryBeforeExit {l : Launch} {X : Execution} {g start finish use : Nat}
    {s : TState} {ending : Option TState}
    (hs : At s 1744 (drainCarry l use))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop start) ending)
    (he : X.get (g, finish) = some ⟨9205, .exit⟩) (hStart : start ≤ finish)
    (cut : Fin 2) :
    ∃ u pos, start ≤ pos ∧ pos ≤ finish ∧ At u (1862 + cut.val) (drainCarry l use) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) none := by
  have hLimit : 1862 + cut.val ≤ 1901 := by have := cut.isLt; omega
  have hAudit : ∀ branch, ((kernel.code.drop 1744).take (1862 + cut.val - 1744)).all
      (fun ins => loaderPipelineCutOp 1744 (1862 + cut.val) branch
        ((drainCarry l use).map Prod.fst) ins.op) = true := by
    intro branch
    fin_cases cut <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨u, pre, result, _, hu, hRun, _, hPos⟩ :=
    prefixStableCut ⟨by decide, by omega, hLimit⟩ hAudit hs hr he hStart (by intro f h; cases h)
      (fun _ => 0) (fun _ => false) (.inl (by change 1862 + cut.val ≤ 9205; omega))
      (by intros; rfl) (by intros; rfl) (by intros; simp)
  let pos := start + pre.length
  have hGet : ((X.tr g).drop pos)[finish - pos]? = some ⟨9205, .exit⟩ := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hPos]
    exact he
  have hResult : result = none := by
    cases result with
    | none => rfl
    | some => exact (hRun.no_exit hGet).elim
  exact ⟨u, pos, by dsimp [pos]; omega, hPos, hu, hResult ▸ hRun⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
