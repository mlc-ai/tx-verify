-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderInputSites
public import Kernels.TmlFa4Fwd.Proof.LoaderExit
public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
public import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
public import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Prologue Mma

noncomputable section

private def mapCvtaPc (i : Fin 14) : Nat :=
  ![690, 697, 717, 725, 741, 749, 768, 776, 1161, 1171, 1188, 1197, 1374, 1381] i

private def mapSource (i : Fin 14) : Nat := if (inputSite i).bias then 7289 else 7291

private def mapCvtaOp (i : Fin 14) : Op :=
  .addr (.cvta false .param 64 (inputSite i).mapReg (.reg (mapSource i)))

private theorem mapCvtaCode (i : Fin 14) :
    kernel.code[mapCvtaPc i]? = some ⟨none, mapCvtaOp i⟩ := by
  fin_cases i
  · exact Flow.code_690
  · exact Flow.code_697
  · exact Flow.code_717
  · exact Flow.code_725
  · exact Flow.code_741
  · exact Flow.code_749
  · exact Flow.code_768
  · exact Flow.code_776
  · exact Flow.code_1161
  · exact Flow.code_1171
  · exact Flow.code_1188
  · exact Flow.code_1197
  · exact Flow.code_1374
  · exact Flow.code_1381

private theorem mapPcBounds (i : Fin 14) :
    180 < mapCvtaPc i ∧ mapCvtaPc i < (inputSite i).pc ∧ (inputSite i).pc < 1901 := by
  fin_cases i <;> decide

private def mapWindowPcs : List Nat :=
  (List.ofFn fun i : Fin 14 => (List.range ((inputSite i).pc - mapCvtaPc i)).map
    (fun k => mapCvtaPc i + 1 + k)).flatten

private def mapWindowAvoided : Op → Bool
  | .bra target _ => !mapWindowPcs.contains target
  | .brx _ targets _ => targets.all (fun target => !mapWindowPcs.contains target)
  | _ => true

private theorem mapWindowBranches :
    kernel.code.all (fun ins => mapWindowAvoided ins.op) = true := by
  decide +kernel

private theorem noMapWindowBranch (i : Fin 14) {pc : Nat}
    (hl : mapCvtaPc i < pc) (hh : pc ≤ (inputSite i).pc) : kernel.branchTarget pc = false := by
  have hm : pc ∈ mapWindowPcs := by
    apply List.mem_flatten.mpr
    refine ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_map.mpr ⟨pc - (mapCvtaPc i + 1), ?_, ?_⟩⟩
    · simp only [List.mem_range]
      omega
    · exact Nat.add_sub_of_le (by omega)
  cases ht : kernel.branchTarget pc
  · rfl
  · obtain ⟨ins, hIns, hT⟩ := List.any_eq_true.mp ht
    have hAudit := List.all_eq_true.mp mapWindowBranches ins hIns
    cases hOp : ins.op <;> simp only [hOp, Bool.false_eq_true] at hT
    · obtain rfl := beq_iff_eq.mp hT
      simp [hOp, mapWindowAvoided, hm] at hAudit
    · rename_i targets _
      have hList : targets.all (fun target => !mapWindowPcs.contains target) = true := by
        simpa only [hOp, mapWindowAvoided] using hAudit
      have hAvoid := List.all_eq_true.mp hList pc (by simpa using hT)
      simp [hm] at hAvoid

private theorem mapWindowPreserves (i : Fin 14) :
    ((kernel.code.drop (mapCvtaPc i + 1)).take ((inputSite i).pc - mapCvtaPc i)).all
      (fun ins => !(loaderRingWrites ins.op).contains (inputSite i).mapReg) = true := by
  fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl

private def mapPtr (i : Fin 14) (generic : Bool) : Value :=
  .ptr 64 generic (.param (param (inputParam (inputSite i)))) 0

private def mapFrame (l : Launch) (warp : Fin 2) (i : Fin 14) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val)), (mapSource i, mapPtr i false)]

private def MapWindow (i : Fin 14) (t : TState) : Prop :=
  mapCvtaPc i < t.pc → t.pc ≤ (inputSite i).pc → t.regs (inputSite i).mapReg = some (mapPtr i true)

private theorem mapFrameCode (i : Fin 14) (l : Launch) (warp : Fin 2) (bound : Nat) :
    ((kernel.code.drop 180).take (1901 - 180)).all
      (fun ins => loaderPipelineCutOp 180 1901 bound ((mapFrame l warp i).map Prod.fst)
        ins.op) = true := by
  fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem tauMapWindow (i : Fin 14) {l : Launch} {g : Nat} {t u : TState}
    (ht : 180 ≤ t.pc ∧ t.pc < 1901) (hPtr : t.regs (mapSource i) = some (mapPtr i false))
    (hWas : MapWindow i t) (hs : Tau kernel Assumptions.all l g t u) : MapWindow i u := by
  intro hl hh
  have hTau : Tau kernel [] l g t u := by
    unfold Tau at hs ⊢
    rwa [← loaderOutCore (by omega) (by omega)]
  obtain ⟨ins, hc⟩ := tau_core_has_code hTau
  have hNext : u.pc = t.pc + 1 := by
    rcases tau_core_frame hc hTau with rfl | h
    · rfl
    · exact PTX.LocalFrame.pc_succ hc h (noMapWindowBranch i hl hh)
  by_cases hFirst : t.pc = mapCvtaPc i
  · rw [hFirst, mapCvtaCode i] at hc
    have hCode := hc.symm
    obtain rfl := Option.some.inj hCode
    have hHealthy : t.fault = none := by
      cases hf : t.fault <;> simp [Tau, out, hf] at hTau ⊢
    have hExec : execLocalA [] l g t (mapCvtaOp i) =
        .ok (next (setReg t (inputSite i).mapReg (mapPtr i true))) := by
      rw [execLocalA_nil]
      unfold mapCvtaOp
      rw [execLocal_cvta rfl, execCvta_param]
      simp [readValue, readReg, hPtr, mapPtr, bind, Except.bind, pure, Except.pure]
    have hOut : out kernel [] l g t =
        .tau (next (setReg t (inputSite i).mapReg (mapPtr i true))) := by
      simp [out, hHealthy, hFirst, mapCvtaCode i, guardHolds, hExec, pure, Except.pure]
      rfl
    obtain rfl : u = next (setReg t (inputSite i).mapReg (mapPtr i true)) :=
      (Out.tau.inj (hTau.symm.trans hOut))
    simp [next, setReg]
  · have hm : ins ∈ (kernel.code.drop (mapCvtaPc i + 1)).take
        ((inputSite i).pc - mapCvtaPc i) := by
      apply List.mem_of_getElem? (i := t.pc - (mapCvtaPc i + 1))
      rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        Nat.add_sub_of_le (by omega)]
    have hKeep : (inputSite i).mapReg ∉ loaderRingWrites ins.op := by
      simpa using List.all_eq_true.mp (mapWindowPreserves i) ins hm
    have hStep : WStep kernel Assumptions.all l g t none u := .inl ⟨rfl, hs⟩
    have hR := loaderPipelineStepRegs (r := (inputSite i).mapReg) (by omega) ht.2
      (fun ins' hc' => by rwa [Option.some.inj (hc'.symm.trans hc)]) hStep
    rw [hR]
    exact hWas (by omega) (by omega)

private theorem eventMapWindow (i : Fin 14) {l : Launch} {g : Nat} {t u : TState} {e : Event}
    (ht : 180 ≤ t.pc ∧ t.pc < 1901) (hWas : MapWindow i t)
    (he : EStep kernel Assumptions.all l g t e (some u)) : MapWindow i u := by
  intro hl hh
  obtain ⟨ins, hc, hNonlocal, _⟩ := estep_event_source he
  have hCore : EStep kernel [] l g t e (some u) := by
    obtain ⟨tmpl, hout, hf⟩ := he
    exact ⟨tmpl, by rwa [← loaderOutCore (by omega) (by omega)], hf⟩
  have hPc := (estep_return_pc hCore (fun _ _ _ h => execLocal_frame h)).2
  have hNe : t.pc ≠ mapCvtaPc i := by
    intro h
    rw [h, mapCvtaCode i] at hc
    obtain rfl := Option.some.inj hc.symm
    have hLocal : (mapCvtaOp i).isLocal = true := by fin_cases i <;> decide
    rw [hLocal] at hNonlocal
    cases hNonlocal
  have hm : ins ∈ (kernel.code.drop (mapCvtaPc i + 1)).take
      ((inputSite i).pc - mapCvtaPc i) := by
    apply List.mem_of_getElem? (i := t.pc - (mapCvtaPc i + 1))
    rwa [List.getElem?_take_of_lt (by rcases hPc <;> omega), List.getElem?_drop,
      Nat.add_sub_of_le (by rcases hPc <;> omega)]
  have hKeep : (inputSite i).mapReg ∉ loaderRingWrites ins.op := by
    simpa using List.all_eq_true.mp (mapWindowPreserves i) ins hm
  have hStep : WStep kernel Assumptions.all l g t (some e) u := .inr ⟨e, rfl, he⟩
  have hR := loaderPipelineStepRegs (r := (inputSite i).mapReg) (by omega) ht.2
    (fun ins' hc' => by rwa [Option.some.inj (hc'.symm.trans hc)]) hStep
  rw [hR]
  exact hWas (by rcases hPc <;> omega) (by rcases hPc <;> omega)


private def inputIssueOp (i : Fin 14) : Op :=
  let s := inputSite i
  .cpTensor false false 2535 s.sharedOffset (.reg s.mapReg)
    [.reg s.colReg, .reg s.rowReg, .reg 7169] s.barrierReg s.barrierOffset none .tile
    (some (.reg s.policyReg))

private theorem inputIssueFromWalk {l : Launch} {g addr : Nat} {s : TState}
    {es : List Event} {vs : List Visit} {spec : TensorCopy.Spec}
    (warp : Fin 2) (i : Fin 14)
    (hp : 180 ≤ s.pc ∧ s.pc ≤ 1901) (hs : RingShape s)
    (hF : Holds s.regs (mapFrame l warp i)) (hMap : MapWindow i s)
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hMem : (⟨(inputSite i).pc, .tensorIssue addr spec⟩ : Event) ∈ es) :
    ∃ t u, t.regs (inputSite i).mapReg = some (mapPtr i true) ∧
      t.regs 2535 = some (b32 l.sharedBase) ∧
      Fires (inputSite i).pc (eventTmpl Assumptions.all l g t (inputIssueOp i))
        ⟨(inputSite i).pc, .tensorIssue addr spec⟩ (some u) := by
  have hBounds := mapPcBounds i
  have step {t u : TState} {ev : Option Event} (hp : 180 ≤ t.pc ∧ t.pc < 1901)
      (hs : RingShape t) (hF : Holds t.regs (mapFrame l warp i)) (hMap : MapWindow i t)
      (hw : WStep kernel Assumptions.all l g t ev u) :
      (180 ≤ u.pc ∧ u.pc ≤ 1901) ∧ RingShape u ∧
        Holds u.regs (mapFrame l warp i) ∧ MapWindow i u := by
    obtain ⟨hLo, hHi, hShape, hFrame⟩ := pipelineCutStep (by decide : 174 ≤ 180)
      (by decide : 1901 ≤ 1901) hp (mapFrameCode i l warp u.pc) hw hs hF
    refine ⟨⟨hLo, hHi.resolve_right (Nat.lt_irrefl _)⟩, hShape, hFrame, ?_⟩
    rcases hw with ⟨_, hTau⟩ | ⟨_, _, he⟩
    · exact tauMapWindow i hp hF.2.2.1 hMap hTau
    · exact eventMapWindow i hp hMap he
  have exit {t : TState} {es : List Event} {vs : List Visit} (hp : t.pc = 1901)
      (hs : RingShape t) (hF : Holds t.regs (mapFrame l warp i))
      (hw : Walk kernel Assumptions.all l g t es vs)
      (hm : (⟨(inputSite i).pc, .tensorIssue addr spec⟩ : Event) ∈ es) : False := by
    have h := loaderExitEventPcs warp hp hs ⟨hF.1, hF.2.1, trivial⟩ hw _ hm
    change (inputSite i).pc = 1901 ∨ (inputSite i).pc = 9205 at h
    omega
  induction hw with
  | stop => simp at hMem
  | @tau t u es vs ht hw ih =>
    by_cases hx : t.pc = 1901
    · exact (exit hx hs hF (.tau ht hw) hMem).elim
    obtain ⟨hu, hShape, hFrame, hMap'⟩ :=
      step ⟨hp.1, by omega⟩ hs hF hMap (.inl ⟨rfl, ht⟩)
    exact ih hu hShape hFrame hMap' hMem
  | @ev t u e es vs he hw ih =>
    rcases List.mem_cons.mp hMem with hHere | hThere
    · subst e
      obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
      have ht := (estep_source_pc he).symm
      change t.pc = (inputSite i).pc at ht
      rw [ht, inputSiteCode i] at hc
      obtain rfl := Option.some.inj hc.symm
      exact ⟨t, u, hMap (by omega) (by omega), hF.1,
        by simpa only [ht, inputIssueOp] using hf⟩
    · by_cases hx : t.pc = 1901
      · exact (exit hx hs hF (.ev he hw) hMem).elim
      obtain ⟨hu, hShape, hFrame, hMap'⟩ :=
        step ⟨hp.1, by omega⟩ hs hF hMap (.inr ⟨e, rfl, he⟩)
      exact ih hu hShape hFrame hMap' hThere
  | @last t e he =>
    obtain rfl := (List.mem_singleton.mp hMem).symm
    obtain ⟨_, _, hf⟩ := he
    have hEnd := fires_none_ends hf
    simp [Ends] at hEnd

private theorem actualInputIssueAt {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index addr : Nat} (i : Fin 14) {spec : TensorCopy.Spec}
    (he : X.get (g, index) = some ⟨(inputSite i).pc, .tensorIssue addr spec⟩) :
    ∃ t u, t.regs (inputSite i).mapReg = some (mapPtr i true) ∧
      t.regs 2535 = some (b32 l.sharedBase) ∧
      Fires (inputSite i).pc (eventTmpl Assumptions.all l g t (inputIssueOp i))
        ⟨(inputSite i).pc, .tensorIssue addr spec⟩ (some u) := by
  have hBounds := mapPcBounds i
  have hPc : 173 < (inputSite i).pc := by omega
  have hNotHint : (inputSite i).pc ∉ registerHintSites := by fin_cases i <;> decide
  have hRole := roleBodyPcOfEvent hp hX he hPc hNotHint
  have hWarp : 14 ≤ warpIndex l g := by
    change roleBodyPc (warpIndex l g) (inputSite i).pc at hRole
    unfold roleBodyPc at hRole
    split_ifs at hRole <;> omega
  have hg : g < l.threads := event_thread_lt hX he
  obtain ⟨t, o, hIdx, hAt, hTid, hRun⟩ :=
    nonzeroCommonPrefixOfLateEventWithTid hp hX hg (by omega : 0 < warpIndex l g) he hPc
  let warp : Fin 16 := ⟨warpIndex l g, warpIndex_lt hp g⟩
  have hStart : At t 174 (loaderBarrierFacts p l g warp.val) := by
    have h := hAt.2.2.2.2
    have hAbi : Holds t.regs (abiFacts p l) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    apply hAt.mono
    rw [loaderBarrierFacts, holds_append]
    exact ⟨⟨h.1, h.2.1, hAbi⟩, hTid, trivial⟩
  have hNon : (X.tr g).drop 5 ≠ [] := by
    intro hh
    have hLt : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    have hLe := List.drop_eq_nil_iff.mp hh
    omega
  obtain ⟨inst, u, hHint, hEntry, hTail⟩ :=
    loaderHintObservedPrefix hp hg warp hWarp hStart hRun hNon
  have hPast : 6 ≤ index := by
    by_contra h
    have heq : index = 5 := by omega
    rw [heq, hHint] at he
    exact (by omega : (inputSite i).pc ≠ 179)
      (congrArg Event.pc (Option.some.inj he.symm))
  have hMem : (⟨(inputSite i).pc, .tensorIssue addr spec⟩ : Event) ∈ (X.tr g).drop 6 := by
    apply List.mem_of_getElem? (i := index - 6)
    rwa [List.getElem?_drop, Nat.add_sub_of_le hPast]
  let w : Fin 2 := ⟨warp.val - 14, by have := warp.isLt; omega⟩
  have hW : 14 + w.val = warp.val := Nat.add_sub_of_le hWarp
  have hF : Holds u.regs (mapFrame l w i) := by
    have hAbi : (mapSource i, mapPtr i false) ∈ abiFacts p l := by
      fin_cases i <;> simp [mapSource, mapPtr, inputParam, inputSite, abiFacts]
    have hRegs := hEntry.2.2.2.2
    rw [mapFrame, hW]
    exact ⟨holds_mem hRegs (by simp [loaderEntryFacts, loaderBarrierFacts]),
      holds_mem hRegs (by simp [loaderEntryFacts, loaderBarrierFacts]),
      holds_mem hRegs (by simp [loaderEntryFacts, loaderBarrierFacts, hAbi]), trivial⟩
  obtain ⟨_, hWalk⟩ := walkFromRun hTail
  exact inputIssueFromWalk w i (by rw [hEntry.1]; decide)
    (ringShapeOfAt hEntry) hF (by intro h; rw [hEntry.1] at h; omega) hWalk hMem


/-- One actual input issue uses the ABI and shared destination of its decoded subbox. -/
theorem actualInputBoxAt {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {spec : TensorCopy.Spec} (j : Fin 14)
    (he : X.get i = some ⟨(inputSite j).pc, .tensorIssue addr spec⟩) :
    addr = inputMapAddress p (inputSite j) ∧
      (⟨spec.outer, spec.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
        ⟨2, inputMap p (inputSite j)⟩ ∧ spec.rows = none ∧
      spec.sharedBase = ⟨.shared, i.1 / l.block, l.sharedBase + (inputSite j).sharedOffset⟩ ∧
      spec.clusterAddress = false ∧ spec.group = .one := by
  obtain ⟨t, u, hPtr, hShared, hf⟩ := actualInputIssueAt hp hX j he
  have hMap := (tensorMap_ok (inputMapReady hp (g := i.1) hPtr))
  have hCopy := fires_cpTensor_copy hf rfl
  obtain ⟨ha, _, desc, hRead, _, hTransfer, hRows⟩ := tensorLoadCopy_ok hCopy
  have hAddr := Except.ok.inj (ha.symm.trans hMap.1)
  rw [hAddr, hMap.2.1] at hRead
  have hDesc := (Option.some.inj hRead).symm
  obtain ⟨hDst, hCluster, hGroup⟩ := tensorLoadCopy_box hCopy
  have hOffset : (inputSite j).sharedOffset ≤ 216064 := by fin_cases j <;> decide
  have hBound : l.sharedBase + (inputSite j).sharedOffset < 2 ^ 32 := by
    have hAlloc := hp.shared.2.1
    omega
  have hExpected : sharedEffAddr l i.1 t false 2535 (inputSite j).sharedOffset =
      .ok ⟨.shared, i.1 / l.block, l.sharedBase + (inputSite j).sharedOffset⟩ :=
    effAddr_b32_off hShared hBound
  change sharedEffAddr l i.1 t false 2535 (inputSite j).sharedOffset = .ok spec.sharedBase at hDst
  rw [hExpected] at hDst
  refine ⟨hAddr, ?_, hRows.mpr rfl, (Except.ok.inj hDst).symm, hCluster, hGroup⟩
  rw [hTransfer]
  exact hDesc


/-- All actual Q and Bias loads use their ABI maps and decoded CTA destinations.
The descriptor and tile mode are fixed independently of the runtime coordinates. -/
theorem actualInputBox {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {spec : TensorCopy.Spec} (he : X.TensorIssue i addr spec) :
    ∃ site : Fin 14, addr = inputMapAddress p (inputSite site) ∧
      (⟨spec.outer, spec.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
        ⟨2, inputMap p (inputSite site)⟩ ∧ spec.rows = none ∧
      spec.sharedBase = ⟨.shared, i.1 / l.block, l.sharedBase + (inputSite site).sharedOffset⟩ ∧
      spec.clusterAddress = false ∧ spec.group = .one := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨j, rfl⟩ := actualInputIssuePc hX he
  exact ⟨j, actualInputBoxAt hp hX j he⟩

/-- All actual Q and Bias loads use their ABI tensor maps throughout finite executions.
The descriptor and tile mode are fixed without assuming the runtime box coordinates. -/
theorem actualInputDescriptor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {spec : TensorCopy.Spec} (he : X.TensorIssue i addr spec) :
    ∃ site : Fin 14, addr = inputMapAddress p (inputSite site) ∧
      (⟨spec.outer, spec.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
        ⟨2, inputMap p (inputSite site)⟩ ∧ spec.rows = none := by
  obtain ⟨j, ha, hd, hr, _⟩ := actualInputBox hp hX he
  exact ⟨j, ha, hd, hr⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
