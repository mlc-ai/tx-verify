-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasCursor
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
import Kernels.TmlFa4Fwd.Proof.LoaderBiasTensorActor
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import Lemmas.Flow.TensorLoadFacts
import Kernels.TmlFa4Fwd.Proof.LoaderBiasIssueOrigin
import Kernels.TmlFa4Fwd.Proof.LoaderObservedCut
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingBiasWarp
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Prologue

private theorem warmIssueStepPast {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (stage half : Fin 2) (hPast : warmBiasIssueSite stage half < s.pc) (hHi : s.pc < 1348)
    (h : WStep kernel Assumptions.all l g s e u) :
    warmBiasIssueSite stage half < u.pc := by
  have hMin : 917 ≤ warmBiasIssueSite stage half := by fin_cases stage <;> fin_cases half <;> decide
  rcases h with ⟨rfl,ht⟩ | ⟨ev,rfl,he⟩
  · by_contra! hn
    have hEdge := loaderTauBackEdge (by omega) (by omega) (by omega) ht
    have audit : ∀ edge ∈ loaderBackEdges, 917 ≤ edge.1 → edge.1 < 1348 →
        warmBiasIssueSite stage half < edge.1 → warmBiasIssueSite stage half < edge.2 := by
      fin_cases stage <;> fin_cases half <;> decide
    exact (Nat.not_lt_of_ge hn) (audit _ hEdge (by omega) hHi hPast)
  · have he' : EStep kernel [] l g s ev (some u) := by
      obtain ⟨tm,ho,hf⟩ := he
      exact ⟨tm,by rwa [← loaderOutCore (by omega) (by omega)],hf⟩
    rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with h | h <;> omega

section
variable {l : Launch}

private theorem warmIssueAbsentPast {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (stage half : Fin 2) {target : Event} (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hPc : target.pc = warmBiasIssueSite stage half) (hPast : target.pc < s.pc) :
    target ∉ loaderSliceEvents 917 1348 vs := by
  have hMin : 917 ≤ warmBiasIssueSite stage half := by fin_cases stage <;> fin_cases half <;> decide
  induction hWalk with
  | stop => simp [loaderSliceEvents]
  | @tau t u es vs ht hw ih =>
    by_cases hh : t.pc < 1348
    · have hNext := warmIssueStepPast stage half (hPc ▸ hPast) hh (.inl ⟨rfl,ht⟩)
      simpa [loaderSliceEvents,visit,show 917 ≤ t.pc by omega,hh] using ih (hPc.symm ▸ hNext)
    · simp [loaderSliceEvents,visit,hh]
  | @ev t u ev es vs he hw ih =>
    by_cases hh : t.pc < 1348
    · have hNext := warmIssueStepPast stage half (hPc ▸ hPast) hh (.inr ⟨ev,rfl,he⟩)
      have hNe : target ≠ ev := by
        intro heq
        have hHere := (congrArg Event.pc heq).trans (estep_source_pc he)
        omega
      simp only [loaderSliceEvents,visit,show 917 ≤ t.pc by omega,hh,decide_true,
        Bool.and_self,List.takeWhile_cons_of_pos,List.filterMap_cons,
        List.mem_cons]
      exact fun h => h.elim hNe (ih (hPc.symm ▸ hNext))
    · simp [loaderSliceEvents,visit,hh]
  | @last t ev he =>
    have hNe : target ≠ ev := by
      intro heq
      have hHere := (congrArg Event.pc heq).trans (estep_source_pc he)
      omega
    by_cases hh : t.pc < 1348
    · simpa [loaderSliceEvents,visit,show 917 ≤ t.pc by omega,hh] using hNe
    · simp [loaderSliceEvents,visit,hh]

private theorem warmIssueInSlice {g : Nat} {s : TState} {es : List Event} {vs : List Visit}
    (stage half : Fin 2) {target : Event} (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hPc : target.pc = warmBiasIssueSite stage half)
    (hSeen : target ∈ loaderSliceEvents 917 1348 vs) :
    target ∈ loaderSliceEvents 917 (target.pc+1) vs := by
  have hWarm : target.pc < 1348 := by
    rw [hPc]
    fin_cases stage <;> fin_cases half <;> decide
  induction hWalk with
  | stop => simp [loaderSliceEvents] at hSeen
  | @tau t u es vs ht hw ih =>
    by_cases hl : 917 ≤ t.pc
    · by_cases hb : t.pc < target.pc+1
      · have hh : t.pc < 1348 := by omega
        simp only [Nat.lt_succ_iff] at hb
        have hTail : target ∈ loaderSliceEvents 917 1348 vs := by
          simpa [loaderSliceEvents,visit,hl,hh] using hSeen
        simpa [loaderSliceEvents,visit,hl,hb] using ih hTail
      · exact (warmIssueAbsentPast stage half (.tau ht hw) hPc (by omega) hSeen).elim
    · simp [loaderSliceEvents,visit,hl] at hSeen
  | @ev t u ev es vs he hw ih =>
    by_cases hl : 917 ≤ t.pc
    · by_cases hb : t.pc < target.pc+1
      · have hh : t.pc < 1348 := by omega
        simp only [Nat.lt_succ_iff] at hb
        have hTail : target = ev ∨ target ∈ loaderSliceEvents 917 1348 vs := by
          simpa [loaderSliceEvents,visit,hl,hh] using hSeen
        rcases hTail with rfl | hTail
        · simp [loaderSliceEvents,visit,hl,hb]
        · exact (show target = ev ∨ target ∈ loaderSliceEvents 917 (target.pc+1) vs from
            .inr (ih hTail)) |> fun h => by
              simpa [loaderSliceEvents,visit,hl,hb] using h
      · exact (warmIssueAbsentPast stage half (.ev he hw) hPc (by omega) hSeen).elim
    · simp [loaderSliceEvents,visit,hl] at hSeen
  | @last t ev he =>
    have hEq : target = ev := by
      by_cases hh : 917 ≤ t.pc ∧ t.pc < 1348
      · simpa [loaderSliceEvents,visit,hh.1,hh.2] using hSeen
      · simp [loaderSliceEvents,visit,hh] at hSeen
    subst ev
    have hHere := estep_source_pc he
    have hLo : 917 ≤ target.pc := by
      rw [hPc]
      fin_cases stage <;> fin_cases half <;> decide
    simp [loaderSliceEvents,visit,← hHere,hLo]

/-- Local steps preserve an event in the remainder of the same loader slice. -/
theorem biasSeenAfterLocal {g lower stop : Nat} {s u : TState} {es : List Event} {vs : List Visit}
    {target : Event} (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hSeen : target ∈ loaderSliceEvents lower stop vs)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) :
    ∃ post, Walk kernel Assumptions.all l g u es post ∧
      target ∈ loaderSliceEvents lower stop post := by
  have step {a b : TState} {visits : List Visit}
      (hw : Walk kernel Assumptions.all l g a es visits)
      (hMem : target ∈ loaderSliceEvents lower stop visits)
      (ht : Tau kernel Assumptions.all l g a b) :
      ∃ post, Walk kernel Assumptions.all l g b es post ∧
        target ∈ loaderSliceEvents lower stop post := by
    cases hw with
    | stop => simp [loaderSliceEvents] at hMem
    | tau hTau hTail =>
      obtain rfl := tau_det hTau ht
      have hHead : lower ≤ a.pc ∧ a.pc < stop := by
        by_contra h
        simp [loaderSliceEvents,visit,h] at hMem
      exact ⟨_,hTail,by simpa [loaderSliceEvents,visit,hHead.1,hHead.2] using hMem⟩
    | ev hActual _ => exact (not_tau_of_stops (stops_of_estep hActual) ht).elim
    | last hActual => exact (not_tau_of_stops (stops_of_estep hActual) ht).elim
  induction hLocal with
  | refl => exact ⟨vs,hWalk,hSeen⟩
  | tail _ ht ih =>
    obtain ⟨post,hPost,hMem⟩ := ih
    exact step hPost hMem ht

/-- Replay the actual silent setup cut in a Bias loader slice. -/
theorem biasLocalCut {g scope start cut stop : Nat} {t : TState} {es : List Event} {vs : List Visit}
    {F : List (Nat × Value)} {event : Event} (hAt : At t start F) (hScope : scope ≤ start)
    (hStart : 174 ≤ start ∧ start ≤ cut) (hLimit : cut ≤ 1901) (hCut : cut < stop)
    (hCode : ((kernel.code.drop start).take (cut - start)).all
      (fun i => loaderPipelineCutOp start cut (stop - 1) (F.map Prod.fst) i.op) = true)
    (hInsn : ∃ ins, kernel.code[cut]? = some ins ∧ ins.op.isLocal = true)
    (hw : Walk kernel Assumptions.all l g t es vs) (he : event ∈ loaderSliceEvents scope stop vs)
    (hLo : cut ≤ event.pc) (hCont : ¬ Ends event) :
    ∃ u tail visits, At u cut F ∧ Walk kernel Assumptions.all l g u tail visits ∧
      event ∈ loaderSliceEvents scope stop visits := by
  obtain ⟨u,_,tail,_,visits,_,_,_,hu,hShape,hFrame,_,hTail,hSaw⟩ :=
    loaderObservedCut hScope hStart.1 hLimit hCut hCode hw
      ⟨hAt.1.symm ▸ le_rfl,hAt.1.symm ▸ hStart.2⟩
      (ringShapeOfAt hAt) hAt.2.2.2.2 he hLo hCont
  exact ⟨u,tail,visits,pipelineAtCut hu hShape hFrame
    (walkWithContinuingEventClean hTail (Thread.Loader.memEventsOfLoaderSlice hTail hSaw) hCont)
      hInsn,hTail,hSaw⟩

private def warmRowStart (half : Fin 2) : Nat := if half = 0 then 1189 else 1198

private theorem warmUpperRow {g row : Nat} (half : Fin 2) (hRow : row+128 < 2^32) :
    Seg kernel [] l g 1 (warmRowStart half) [(1087,b32 row)] (warmRowStart half+1)
      [((inputSite (warmBiasInputSite 1 half)).rowReg,b32 (row+128))] := by
  fin_cases half <;> intro t ht
  all_goals
    dsimp [warmBiasInputSite,warmRowStart,inputSite] at ht ⊢
    seg_fp ht using
      (nf_simp
       all_goals omega)

private theorem warmIssueRegisters {g row head iteration residual address : Nat}
    (stage half : Fin 2) (hIter : iteration < 9) (hBit : residual ≤ 1) (hRow : row+128 < 2^32)
    {s : TState} {es : List Event} {vs : List Visit} {spec : TensorCopy.Spec}
    (hs : At s 917 [(7174,b32 iteration),(1090,b32 0),(1117,b32 residual),
      (1087,b32 row),(7169,b32 head)]) (hw : Walk kernel Assumptions.all l g s es vs)
    (hSeen : (⟨warmBiasIssueSite stage half,.tensorIssue address spec⟩ : Event) ∈
      loaderSliceEvents 917 (warmBiasIssueSite stage half+1) vs) :
    let site := inputSite (warmBiasInputSite stage half)
    ∃ t u, EStep kernel Assumptions.all l g t ⟨site.pc,.tensorIssue address spec⟩ (some u) ∧
      t.regs site.colReg = some (b32 (warmBiasColumn stage half iteration residual)) ∧
      t.regs site.rowReg = some (b32 (row+128*stage.val)) ∧
      t.regs 7169 = some (b32 head) := by
  dsimp only
  let site := inputSite (warmBiasInputSite stage half)
  let event : Event := ⟨warmBiasIssueSite stage half,.tensorIssue address spec⟩
  let cut := warmColumnStart stage half
  let n := warmColumnLength stage
  let stop := warmBiasIssueSite stage half+1
  let F := [(7174,b32 iteration),(1090,b32 0),(1117,b32 residual),
    (1087,b32 row),(7169,b32 head)]
  let col := warmBiasColumn stage half iteration residual
  let G := (site.colReg,b32 col)::F
  have hCont : ¬ Ends event := by simp [event,Ends]
  have hStart : 917 ≤ cut := by
    change 917 ≤ warmColumnStart stage half
    fin_cases stage <;> fin_cases half <;> decide
  have hAfter : cut+n ≤ site.pc ∧ site.pc+1 ≤ 1901 := by
    change warmColumnStart stage half+warmColumnLength stage ≤
      (inputSite (warmBiasInputSite stage half)).pc ∧
      (inputSite (warmBiasInputSite stage half)).pc+1 ≤ 1901
    fin_cases stage <;> fin_cases half <;> decide
  have hPc : site.pc = event.pc := warmBiasInputSite_pc stage half
  have hAudit : ((kernel.code.drop 917).take (cut-917)).all
      (fun i => loaderPipelineCutOp 917 cut (stop-1) (F.map Prod.fst) i.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hInsn : ∃ i, kernel.code[cut]? = some i ∧ i.op.isLocal = true := by
    fin_cases stage <;> fin_cases half
    · exact ⟨_,Flow.code_1157,rfl⟩
    · exact ⟨_,Flow.code_1167,rfl⟩
    · exact ⟨_,Flow.code_1186,rfl⟩
    · exact ⟨_,Flow.code_1195,rfl⟩
  obtain ⟨a,tail,visits,ha,hWalk,hSaw⟩ := biasLocalCut hs le_rfl ⟨by decide,hStart⟩
    (by omega) (by change cut < event.pc+1; omega) hAudit hInsn hw hSeen
    (by change cut ≤ event.pc; omega) hCont
  obtain ⟨b,hb,hB⟩ := (warmBiasColumnSegment (l := l) (g := g) stage half hIter hBit).apply
    (ha.mono ⟨ha.2.2.2.2.2.1,ha.2.2.2.2.1,ha.2.2.2.2.2.2.1,trivial⟩)
  have hKeep : ((kernel.code.drop cut).take n).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hSilent : ((kernel.code.drop cut).take (n-1)).all
      (fun i => schedulerFallsThrough i.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hbA,hbKeep⟩ := loaderLinear (regs := F.map Prod.fst) (by omega) (by omega) ha.1
    hKeep hSilent hb
  have hbG : At b (cut+n) G := hB.mono
    ⟨hB.2.2.2.2.1,holdsSchedulerFrame ha.2.2.2.2 hbKeep (fun _ hm => List.mem_map_of_mem hm)⟩
  obtain ⟨post,hPost,hPostMem⟩ := biasSeenAfterLocal hWalk hSaw (run_rtg hbA)
  have finish {q : TState} {es' : List Event} {vs' : List Visit} {r : Nat}
      (hLo : 917 ≤ r) {J : List (Nat × Value)}
      (hAt : At q r J) (hStageCol : (site.colReg,b32 col) ∈ J)
      (hStageRow : (site.rowReg,b32 (row+128*stage.val)) ∈ J)
      (hStageHead : (7169,b32 head) ∈ J)
      (hCode : ((kernel.code.drop r).take (stop-r)).all
        (fun i => loaderPipelineCutOp r stop (stop-1) (J.map Prod.fst) i.op) = true)
      (hRun : Walk kernel Assumptions.all l g q es' vs')
      (hMem : event ∈ loaderSliceEvents 917 stop vs') :
      ∃ t u, EStep kernel Assumptions.all l g t ⟨site.pc,.tensorIssue address spec⟩ (some u) ∧
        t.regs site.colReg = some (b32 col) ∧
        t.regs site.rowReg = some (b32 (row+128*stage.val)) ∧ t.regs 7169 = some (b32 head) := by
    obtain ⟨t,u,_,hRegs,hStep⟩ := loaderEventWithRegisters hLo (by omega)
      (by change event.pc+1 ≤ 1901; omega) hCode hRun (hAt.1.symm ▸ le_rfl)
      (ringShapeOfAt hAt) hAt.2.2.2.2 hMem hCont
    have he : event = ⟨site.pc,.tensorIssue address spec⟩ := by
      change (⟨event.pc,.tensorIssue address spec⟩ : Event) = _
      rw [hPc]
    exact ⟨t,u,he ▸ hStep,holds_mem hRegs hStageCol,holds_mem hRegs hStageRow,
      holds_mem hRegs hStageHead⟩
  fin_cases stage
  · apply finish (r := cut+n) (J := G) (by omega) hbG _ _ _ _ hPost hPostMem
    · exact List.mem_cons_self
    · fin_cases half <;> simp [G,F,site,warmBiasInputSite,inputSite]
    · simp [G,F]
    · fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  · let r := warmRowStart half
    have hRowStart : cut+n ≤ r ∧ r < stop ∧ r ≤ site.pc := by
      change warmColumnStart (1 : Fin 2) half + warmColumnLength 1 ≤ warmRowStart half ∧
        warmRowStart half < warmBiasIssueSite 1 half + 1 ∧
        warmRowStart half ≤ (inputSite (warmBiasInputSite 1 half)).pc
      fin_cases half <;> decide
    have hAuditRow : ((kernel.code.drop (cut+n)).take (r-(cut+n))).all
        (fun i => loaderPipelineCutOp (cut+n) r (stop-1) (G.map Prod.fst) i.op) = true := by
      fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
    have hRowCode : ∃ i,kernel.code[r]? = some i ∧ i.op.isLocal = true := by
      fin_cases half
      · exact ⟨_,Flow.code_1189,rfl⟩
      · exact ⟨_,Flow.code_1198,rfl⟩
    obtain ⟨c,rest,last,hC,hNext,hMem⟩ := biasLocalCut hbG (by omega) ⟨by omega,hRowStart.1⟩
      (by omega) hRowStart.2.1 hAuditRow hRowCode hPost hPostMem
      (by change r ≤ event.pc; omega) hCont
    have hReg : (1087,b32 row) ∈ G := by simp [G,F]
    obtain ⟨d,hd,hD⟩ := (warmUpperRow (l := l) (g := g) half hRow).apply
      (hC.mono ⟨holds_mem hC.2.2.2.2 hReg,trivial⟩)
    have hKeepRow : ((kernel.code.drop r).take 1).all
        (fun i => (G.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
      fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
    obtain ⟨hdA,hdKeep⟩ := loaderLinear (regs := G.map Prod.fst) (by omega) (by omega) hC.1
      hKeepRow (by simp) hd
    let J := (site.rowReg,b32 (row+128)) :: G
    have hD' : At d (r+1) J := hD.mono
      ⟨hD.2.2.2.2.1,holdsSchedulerFrame hC.2.2.2.2 hdKeep (fun _ hm => List.mem_map_of_mem hm)⟩
    obtain ⟨after,hAfterWalk,hEndMem⟩ := biasSeenAfterLocal hNext hMem (run_rtg hdA)
    apply finish (r := r+1) (J := J) (by omega) hD' _ _ _ _ hAfterWalk hEndMem
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_self
    · simp [J,G,F]
    · fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)

/-- A rank-three input issues the signed coordinates in its actual input registers. -/
theorem inputOriginOfRegisters {g address col row head : Nat} (site : Fin 14)
    {spec : TensorCopy.Spec} {t u : TState}
    (hStep : EStep kernel Assumptions.all l g t
      ⟨(inputSite site).pc,.tensorIssue address spec⟩ (some u)) (hRank : spec.outer = 2)
    (hCol : t.regs (inputSite site).colReg = some (b32 col))
    (hRow : t.regs (inputSite site).rowReg = some (b32 row)) (hHead : t.regs 7169 = some (b32 head))
    (hc : col < 2^31) (hr : row < 2^31) (hh : head < 2^31) :
    (⟨spec.outer,spec.origin⟩ : (n : Nat) × (Fin (n+1) → Int)) =
      ⟨2,inputCoordinate col row head⟩ := by
  have hPc : t.pc = (inputSite site).pc := (estep_source_pc hStep).symm
  obtain ⟨ins,hCode,_,hFires⟩ := estep_event_source hStep
  rw [hPc,inputSiteCode] at hCode
  obtain rfl := Option.some.inj hCode
  have hCopy := fires_cpTensor_copy hFires rfl
  have hRead : [.reg (inputSite site).colReg,.reg (inputSite site).rowReg,.reg 7169].mapM
      (readBits l g t 32) = .ok [BitVec.ofNat 64 col,BitVec.ofNat 64 row,BitVec.ofNat 64 head] := by
    simp only [List.mapM_cons,List.mapM_nil,readBits_b32 hCol (by omega),
      readBits_b32 hRow (by omega),readBits_b32 hHead (by omega),bind,Except.bind,pure,Except.pure]
  have hDecode := tensorLoadCopy_origin_all hCopy hRead
  have hBit {n : Nat} (hn : n < 2^31) :
      (BitVec.ofNat 32 (BitVec.ofNat 64 n).toNat).toInt = (n : Int) := by
    rw [toNat_ofNat_lt (by omega : n < 2^64)]
    exact toInt_ofNat_lt32 hn
  rcases spec with ⟨⟨outer,descriptor,origin,base,rows⟩,barrier,cluster,group⟩
  change outer = 2 at hRank
  subst outer
  congr 1
  funext axis
  rw [hDecode axis]
  fin_cases axis
  · exact hBit hc
  · exact hBit hr
  · exact hBit hh

private theorem warmIssueInCurrentSlice {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (stage half : Fin 2)
    (hWalk : Walk kernel Assumptions.all l g s events visits) (hs : s.pc = 917)
    (hShape : RingShape s) {target : Event} {j : Nat} (hAt : events[j]? = some target)
    (hPc : target.pc = warmBiasIssueSite stage half)
    (hRank : (events.take j).countP Execution.isShfl < 64) :
    target ∈ loaderSliceEvents 917 (warmBiasIssueSite stage half+1) visits := by
  have hAudit (bound : Nat) : ((kernel.code.drop 917).take (1348 - 917)).all
      (fun i => loaderPipelineCutOp 917 1348 bound [] i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hRanked : (((kernel.code.drop 917).take (1348 - 917)).zipIdx 917).all
      (fun (i,pc) => LoaderRankedInstr 1348 pc i) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hCount : loaderShuffleTail 1348 917 = 64 := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hRank' : (events.take j).countP Execution.isShfl < loaderShuffleTail 1348 s.pc := by
    rwa [hs,hCount]
  have hm := loaderEventInRankedSlice (stop := 1348) (by decide) le_rfl hAudit hRanked hWalk
    (by rw [hs]; decide) hShape hAt hRank'
  rw [← hPc]
  exact warmIssueInSlice stage half hWalk hPc hm
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (hCuQ : DrainCuQProtected p X) (stage half : Fin 2) {g j : Nat} {spec : TensorCopy.Spec}
include hp hX hFrame hCuQ stage half

/-- A realized warm Bias issue reads its exact launch row and head and computes
its column from the actual warm iteration and the lower-stage residual. -/
theorem warmBiasInputOriginRanked (hBox : Thread.Loader.BiasSubbox p l X (g,j) stage half spec)
    (he : X.get (g,j) = some ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress spec⟩) :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let co := assignedCoordinates p batch (g/l.block)
      ∃ iteration < min (Mma.trips p batch co.1-1) 9,
        (⟨spec.outer,spec.origin⟩ : (n : Nat) × (Fin (n+1) → Int)) =
          ⟨2,inputCoordinate (warmBiasColumn stage half iteration
            (warmBiasResidualBit p batch co.1))
            (p.qOffset batch+256*co.1+128*stage.val) co.2⟩ ∧
        ((X.tr g).take j).countP Execution.isShfl = primingSearchShuffleCount batch+64+
          64*iteration+32 := by
  have hw := biasTensorActorWarp hp hX hBox
  let target : Event := ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress spec⟩
  have hSite : 297 < target.pc ∧ target.pc < 1862 := by
    change 297 < warmBiasIssueSite stage half ∧ warmBiasIssueSite stage half < 1862
    fin_cases stage <;> fin_cases half <;> decide
  have hGet : X.get (g,j) = some target := he
  have hActive := loaderOwnPrefixEventRequiresActiveTile hp hX hw.ge hCuQ hGet hSite.1 hSite.2
  obtain ⟨batch,hb,hLo,hHi,iteration,hIter,pos,hPos,s,ending,hs,hRun,hRank,hOrdinal⟩ :=
    warmBiasEntryOfIssueWithRank hp hX stage half hw
      (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hActive he
  let co := assignedCoordinates p batch (g/l.block)
  let row := p.qOffset batch+256*co.1
  let residual := warmBiasResidualBit p batch co.1
  have hBound : iteration < 9 := hIter.trans_le (Nat.min_le_right _ _)
  have hResid := warmBiasResidualBit_le p batch co.1
  obtain ⟨hTile,hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have hPacked : row < p.totalQ := hp.packedRow_lt hb hTile
  have hFit := hp.shape.2.2.2.2.2
  obtain ⟨visits,hWalk⟩ := Mma.walkFromRun hRun
  have hIndex : ((X.tr g).drop pos)[j-pos]? = some target := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact hGet
  have hInside := warmIssueInCurrentSlice stage half hWalk hs.1 (ringShapeOfAt hs)
    hIndex rfl hRank
  obtain ⟨t,u,hStep,hCol,hRow,hHeadReg⟩ := warmIssueRegisters (row := row) stage half hBound hResid
    (by omega) hs hWalk hInside
  have hOuter : spec.outer = 2 := congrArg Sigma.fst hBox.2.2.2.1
  have hColBound : warmBiasColumn stage half iteration residual < 2^31 := by
    have hHalf := half.isLt
    unfold warmBiasColumn
    split <;> omega
  have hRowBound : row+128*stage.val < 2^31 := by have := stage.isLt; omega
  refine ⟨batch,hb,hLo,hHi,iteration,hIter,?_,hOrdinal⟩
  exact inputOriginOfRegisters (warmBiasInputSite stage half) hStep hOuter hCol hRow hHeadReg
    hColBound hRowBound (hHead.trans hp.heads_signed)

end PTX.Kernels.TmlFa4Fwd.Loader
