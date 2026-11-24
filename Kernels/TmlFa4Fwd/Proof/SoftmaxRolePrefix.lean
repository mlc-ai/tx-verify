-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopInit
public import Kernels.TmlFa4Fwd.Proof.MmaRoleSetup
public import Kernels.TmlFa4Fwd.Proof.MmaScanPrefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxStartup
public import Kernels.TmlFa4Fwd.Proof.CountedVisits
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame Mma Prologue

noncomputable section


/-- A trace window ending at the first forward exit preserves every named register. -/
theorem cutSoftmaxWindow (win : ScoreWindow) {l : Launch} {g cutoff : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hLo : (windowSite win).head ≤ s.pc) (hHi : s.pc < (windowSite win).stop)
    (hSub : s.sub ≤ 3) (hCut : (windowSite win).stop ≤ cutoff) :
    let site := windowSite win
    let budget := 5 * (site.stop - site.head) + 2
    Mma.countedUntil cutoff vs ≤ budget ∨
      ∃ u rest tail, (u.pc = site.stop ∨ u.pc ∈ site.exits) ∧ u.fault = none ∧
        u.sub ≤ 3 ∧ (∀ r ∈ site.keeps, u.regs r = s.regs r) ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        Mma.countedUntil cutoff vs ≤ budget + Mma.countedUntil cutoff tail := by
  dsimp only
  let site := windowSite win
  have hPrefix := windowPrefix win hw hLo hSub
  let P := fun t : TState => t.sub ≤ 3 ∧ ∀ r ∈ site.keeps, t.regs r = s.regs r
  have hInit : P s := ⟨hSub, fun _ _ => rfl⟩
  have hStep {t u : TState} {e : Option Event} (hl : site.head ≤ t.pc) (hh : t.pc < site.stop)
      (he : WStep kernel Assumptions.all l g t e u) (ht : P t) :
      (site.head ≤ u.pc ∧ u.pc < site.stop ∨
        u.pc ∈ site.stop :: site.exits ∧ u.fault = none) ∧ P u := by
    obtain ⟨hl', hh', hs, hf, hR⟩ := windowStepFrame win hl hh ht.1 he
    have hu : P u := ⟨hs, fun r hr => (hR r hr).trans (ht.2 r hr)⟩
    by_cases hIn : u.pc < site.stop
    · exact ⟨.inl ⟨hl', hIn⟩, hu⟩
    · have hF : u.fault = none := hf.resolve_right (by omega)
      rcases hh' with h | h
      · change u.pc ≤ site.stop at h
        exact ⟨.inr ⟨List.mem_cons.mpr (.inl (by omega)), hF⟩, hu⟩
      · exact ⟨.inr ⟨List.mem_cons_of_mem _ h, hF⟩, hu⟩
  rcases Mma.cutWalkInterval hw hLo hHi hInit hCut hStep with
    h | ⟨u, rest, tail, hPc, hF, ⟨hS, hR⟩, hW, hC⟩
  · exact .inl (h.trans hPrefix)
  · exact .inr ⟨u, rest, tail, List.mem_cons.mp hPc, hF, hS, hR, hW,
      hC.trans (Nat.add_le_add_right hPrefix _)⟩

private def scanFor (drain : Bool) : GroupScan := if drain then .softmaxDrain else .softmaxSelect

private def scanCodeOk (site : ScanSite) (i : Instr) : Bool :=
  !(scoreEventWrites i.op).contains 1062 &&
    (match i.op with
    | .bra target _ => site.head ≤ target && target ≤ site.compare + 3
    | .brx .. => false
    | op => op.isLocal || scoreEventOp op)

private theorem scanCodeWitness (drain : Bool) {pc : Nat} {i : Instr}
    (hLo : (scanSite (scanFor drain)).head ≤ pc) (hHi : pc < (scanSite (scanFor drain)).compare + 3)
    (hc : kernel.code[pc]? = some i) : scanCodeOk (scanSite (scanFor drain)) i = true := by
  let site := scanSite (scanFor drain)
  have hAll : ((kernel.code.drop site.head).take (site.compare + 3 - site.head)).all
      (scanCodeOk site) = true := by
    cases drain <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll i
  apply List.mem_of_getElem? (i := pc - site.head)
  have hlo : site.head ≤ pc := hLo
  have hhi : pc < site.compare + 3 := hHi
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo, hc]

private theorem scanKeepsLocal {op : Op} (h : 1062 ∉ scoreEventWrites op) :
    1062 ∉ writesRegs op := by cases op <;> first | exact h | simp [writesRegs]

private theorem scanRoleStep (drain : Bool) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hLo : (scanSite (scanFor drain)).head ≤ s.pc)
    (hHi : s.pc < (scanSite (scanFor drain)).compare + 3) (hs : s.sub ≤ 3)
    (he : WStep kernel Assumptions.all l g s e u) :
    let site := scanSite (scanFor drain)
    site.head ≤ u.pc ∧ u.pc ≤ site.compare + 3 ∧ u.sub ≤ 3 ∧
      (u.fault = none ∨ u.pc = s.pc) ∧ u.regs 1062 = s.regs 1062 := by
  dsimp only
  let site := scanSite (scanFor drain)
  change site.head ≤ s.pc at hLo
  change s.pc < site.compare + 3 at hHi
  have hAdv : s.pc + 1 ≤ site.compare + 3 := by omega
  have hLo' : site.head ≤ s.pc + 1 := by omega
  rcases he with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← groupScanOut (scanFor drain) ((Nat.sub_le site.head 3).trans hLo) hHi]
    obtain ⟨i, hc⟩ := tau_core_has_code ht'
    have hf : s.fault = none := (tauScoreSource ht).choose_spec.2.1
    have hCode := scanCodeWitness drain hLo hHi hc
    simp only [scanCodeOk, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hCode
    rcases tau_core_frame hc ht' with rfl | hT
    · exact ⟨hLo', hAdv, Nat.zero_le _, .inl hf, rfl⟩
    · have hp := hT.pc
      have hPc : site.head ≤ u.pc ∧ u.pc ≤ site.compare + 3 := by
        cases hop : i.op <;> simp only [hop, BrxTarget, or_false, nextPc] at hp
        case bra target uni =>
          rw [hp]
          simpa [hop, Bool.and_eq_true] using hCode.2
        case brx => simp [hop] at hCode
        all_goals exact ⟨hp.symm ▸ hLo', hp.symm ▸ hAdv⟩
      exact ⟨hPc.1, hPc.2, hT.sub.symm ▸ hs, .inl (hT.fault.trans hf),
        hT.regs 1062 (scanKeepsLocal hCode.1)⟩
  · obtain ⟨i, hc, hl, _⟩ := estep_event_source he
    have hf : s.fault = none := by
      cases h : s.fault
      · rfl
      · obtain ⟨m, hm, hf⟩ := he
        simp only [out, h, Out.ev.injEq] at hm
        subst m
        cases hf.2
    have hCode := scanCodeWitness drain hLo hHi hc
    simp only [scanCodeOk, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hCode
    have hOp : scoreEventOp i.op = true := by
      have h := hCode.2
      cases hop : i.op
      case bra => simp [hop, Op.isLocal] at hl
      case brx => simp [hop] at h
      all_goals
        rw [hop] at hl
        simpa only [hop, hl, Bool.false_or] using h
    obtain ⟨hS, hReg⟩ := scoreEventStep hc hOp hs hCode.1 he
    rcases hS.pc with ⟨hPc, hUf⟩ | ⟨hPc, _⟩
    · exact ⟨hPc.symm ▸ hLo', hPc.symm ▸ hAdv, hS.sub, .inl (hUf.trans hf), hReg⟩
    · exact ⟨hPc.symm ▸ hLo, hPc.symm ▸ hHi.le, hS.sub, .inr hPc, hReg⟩

private theorem cutScanRole (drain : Bool) {l : Launch} {g batch cta cutoff : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hBatch : batch + 31 < 2 ^ 31) (hCta : cta + 1 < 2 ^ 31)
    (ht : At s (scanSite (scanFor drain)).head (groupScanFacts (scanFor drain) 0 batch cta))
    (hCut : (scanSite (scanFor drain)).compare + 3 ≤ cutoff) :
    Mma.countedUntil cutoff vs ≤ 64 * (batch + 1) ∨
      ∃ u rest tail, u.pc = (scanSite (scanFor drain)).compare + 3 ∧
        u.fault = none ∧ u.sub ≤ 3 ∧ u.regs 1062 = s.regs 1062 ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        Mma.countedUntil cutoff vs ≤ 64 * (batch + 1) + Mma.countedUntil cutoff tail := by
  let scan := scanFor drain
  let site := scanSite scan
  let stop := site.compare + 3
  have hLo : site.head ≤ s.pc := ht.1.ge
  have hHi : s.pc < stop := by rw [ht.1]; cases drain <;> decide
  have hBound : Mma.countedUntil stop vs ≤ 64 * (batch + 1) := by
    simpa only [Nat.sub_zero] using groupScanPrefixBound scan hBatch hCta (Nat.zero_le _) ht hw
  let P := fun t : TState => t.sub ≤ 3 ∧ t.regs 1062 = s.regs 1062
  have hInit : P s := ⟨ht.2.1.symm ▸ Nat.zero_le _, rfl⟩
  have hStep {t u : TState} {e : Option Event} (hL : site.head ≤ t.pc) (hH : t.pc < stop)
      (he : WStep kernel Assumptions.all l g t e u) (hT : P t) :
      (site.head ≤ u.pc ∧ u.pc < stop ∨ u.pc ∈ [stop] ∧ u.fault = none) ∧ P u := by
    obtain ⟨hLo, hHi, hs, hf, hr⟩ := scanRoleStep drain hL hH hT.1 he
    have hHi' : u.pc ≤ stop := hHi
    refine ⟨?_, hs, hr.trans hT.2⟩
    rcases hHi'.lt_or_eq with hh | hE
    · exact .inl ⟨hLo, hh⟩
    · exact .inr ⟨by simp [hE], hf.resolve_right (by omega)⟩
  rcases Mma.cutWalkInterval hw hLo hHi hInit hCut hStep with
    h | ⟨u, rest, tail, hp, hf, ⟨hS, hR⟩, hW, hb⟩
  · exact .inl (h.trans hBound)
  · exact .inr ⟨u, rest, tail, List.mem_singleton.mp hp, hf, hS, hR, hW,
      hb.trans (Nat.add_le_add_right hBound _)⟩

private theorem localRoleRun {l : Launch} {g : Nat} {s u : TState} {i : Instr}
    (hF : s.fault = none) (hc : kernel.code[s.pc]? = some i)
    (hl : i.op.isLocal = true) (hG : guardHolds s i.guard = .ok true)
    (hOff : s.pc ∉ Assumptions.swExp2Sites) (hCore : Assumptions.coreOp i.op = true)
    (hExec : execLocal l g s i.op = .ok u) :
    run kernel Assumptions.all l g 1 s = some u := by
  have hA : execLocalA Assumptions.all l g s i.op = .ok u := by
    rwa [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff hCore,
      execLocalA_nil]
  simp only [run, tauStep, out_tau hF hc hG hl hA]
  rfl

private def batchPc (drain : Bool) : Nat := if drain then 7605 else 3101
private def batchReg (drain : Bool) : Nat := if drain then 7151 else 7247

private theorem actualBatchLoad {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (drain : Bool) {g : Nat} {s : TState}
    (hs : s.pc = batchPc drain) (hf : s.fault = none) :
    run kernel Assumptions.all l g 1 s = some (next (setReg s (batchReg drain) (b32 p.batch))) := by
  obtain ⟨hWord, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [Mma.param19_name] at hParam
  cases drain <;> simp only [batchPc, batchReg, Bool.false_eq_true, ite_false, ite_true] at hs ⊢
  · refine localRoleRun hf (by rw [hs]; exact Flow.code_3101) rfl rfl (by rw [hs]; decide) rfl ?_
    rw [execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq,
      hParam, DType.width, MemExt.extendBits_same, pure, Except.pure]
    rw [truncBits_ofNat hWord (by decide)]
    rfl
  · refine localRoleRun hf (by rw [hs]; exact Flow.code_7605) rfl rfl (by rw [hs]; decide) rfl ?_
    rw [execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq,
      hParam, DType.width, MemExt.extendBits_same, pure, Except.pure]
    rw [truncBits_ofNat hWord (by decide)]
    rfl

/-- A softmax warp takes the decoded branch from the shared role check to return. -/
theorem softExitRun {l : Launch} {g : Nat} (warp : Fin 8) {s : TState}
    (hs : s.pc = 7742) (hf : s.fault = none) (hr : s.regs 1062 = some (b32 warp.val)) :
    ∃ u, run kernel Assumptions.all l g 3 s = some u ∧
      u.pc = 9205 ∧ out kernel Assumptions.all l g u = .ev .exit := by
  let v := next (setReg s 5867 (.bits 32 (BitVec.ofNat 64 (4 * (warp.val / 4)))))
  let w := next (setReg v 681 (.pred true))
  let u := {w with pc := 9205}
  have hv : run kernel Assumptions.all l g 1 s = some v := by
    refine localRoleRun hf (by rw [hs]; exact Flow.code_7742) rfl rfl (by rw [hs]; decide) rfl ?_
    rw [execLocal_int rfl]
    fin_cases warp <;> simp only [execInt, DType.width, readBits, readReg, hr, bind,
      Except.bind, pure, Except.pure] <;> rfl
  have hPcV : v.pc = 7743 := by simp [v, next, setReg, hs]
  have hvR := show v.regs 5867 = some (.bits 32 (BitVec.ofNat 64 (4 * (warp.val / 4)))) from
    by simp [v, next, setReg]
  have hw : run kernel Assumptions.all l g 1 v = some w := by
    refine localRoleRun hf (by rw [hPcV]; exact Flow.code_7743) rfl rfl
      (by rw [hPcV]; decide) rfl ?_
    rw [execLocal_int rfl]
    fin_cases warp <;> simp only [execInt, DType.width, readBits, readReg, hvR, bind,
      Except.bind, pure, Except.pure] <;> rfl
  have hPcW : w.pc = 7744 := by simp [w, next, setReg, hPcV]
  have hG : guardHolds w (some (681, false)) = .ok true := by
    have hr : w.regs 681 = some (.pred true) := by simp [w, next, setReg]
    simp [guardHolds, readReg, hr, bind, Except.bind, pure, Except.pure]
  have hu : run kernel Assumptions.all l g 1 w = some u :=
    localRoleRun hf (by rw [hPcW]; exact Flow.code_7744) rfl hG (by rw [hPcW]; decide) rfl rfl
  have he : out kernel Assumptions.all l g u = .ev .exit :=
    out_event (t := u) (show u.fault = none from hf) Flow.code_9205 rfl rfl
  exact ⟨u, run_comp (run_comp hv hw) hu, rfl, he⟩

private theorem terminalCount {l : Launch} {g cutoff : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (ho : out kernel Assumptions.all l g s = .ev .exit) :
    Mma.countedUntil cutoff vs ≤ 1 := by
  cases hw with
  | stop => simp [Mma.countedUntil]
  | tau ht _ => exact (not_tau_of_stops ⟨_, ho⟩ ht).elim
  | ev he _ =>
    obtain ⟨m, hm, hf⟩ := he
    obtain rfl := Out.ev.inj (hm.symm.trans ho)
    cases hf.2
  | @last s e he =>
    by_cases hp : s.pc < cutoff
    · simpa [Mma.countedUntil, visit_pc, visit_ev, List.filterMap_cons, hp] using
        (List.countP_le_length (l := [e]) (p := Event.counts))
    · simp [Mma.countedUntil, hp, visit_pc]

private theorem exitSoftmaxBound {l : Launch} {g : Nat} (warp : Fin 8) {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : s.pc = 7742) (hf : s.fault = none) (hr : s.regs 1062 = some (b32 warp.val)) :
    Mma.countedUntil 9206 vs ≤ 1 := by
  obtain ⟨u, hu, hp, ho⟩ := softExitRun (l := l) (g := g) warp hs hf hr
  rcases Mma.advanceWalkLocals hu hw with h | ⟨tail, _, hC, hW⟩
  · subst es
    simp [Mma.zeroCountNoEvents hw]
  · exact (hC 9206).trans (terminalCount hW ho)

private theorem localNeverReturns {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {i : Instr} (hc : kernel.code[s.pc]? = some i) (hl : i.op.isLocal = true)
    (he : EStep kernel Assumptions.all l g s e (some u)) : False := by
  obtain ⟨j, hj, hFalse, _⟩ := estep_event_source he
  rw [hc] at hj
  obtain rfl := Option.some.inj hj
  rw [hl] at hFalse
  contradiction

private theorem cutScanGate {l : Launch} {g cutoff dst pred : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hc : kernel.code[s.pc]? = some ⟨some (pred, false), .bra dst false⟩)
    (hf : s.pc ∉ Assumptions.swExp2Sites) (hCut : s.pc < cutoff) :
    countedUntil cutoff vs ≤ 1 ∨
      ∃ u rest tail, (u.pc = dst ∨ u.pc = s.pc + 1 ∧ u.sub = 0 ∧ u.acc = []) ∧
        u.sub ≤ s.sub ∧ u.fault = none ∧ u.regs = s.regs ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil cutoff vs ≤ countedUntil cutoff tail := by
  cases hw with
  | stop => exact .inl (by simp [countedUntil])
  | ev he _ => exact (localNeverReturns hc rfl he).elim
  | @last s e he =>
    left
    simpa [countedUntil, hCut, visit_pc, visit_ev, List.filterMap_cons] using
      (List.countP_le_length (l := [e]) (p := Event.counts))
  | @tau s u es vs ht hw =>
    obtain ⟨i, hi, hFault, hx⟩ := tauScoreSource ht
    rw [hc] at hi
    obtain rfl := Option.some.inj hi
    have hC : countedUntil cutoff (visit kernel l g s none :: vs) ≤
        countedUntil cutoff vs := by
      simp [countedUntil, hCut, visit_pc, visit_ev, List.filterMap_cons]
    rcases hx with ⟨rfl, _⟩ | ⟨_, _, he⟩
    · exact .inr ⟨skip s, es, vs, .inr ⟨rfl, rfl, rfl⟩, Nat.zero_le _, hFault, rfl, hw, hC⟩
    · have hu := (scoreExecLocal he).resolve_right (fun ⟨_, hm, _, _⟩ => hf hm)
      exact .inr ⟨u, es, vs, .inl (hu.pc.resolve_right id), hu.sub.le, hu.fault.trans hFault,
        funext fun r => hu.regs r (by simp [writesRegs]), hw, hC⟩

private def localSlice (i : Fin 5) : Nat × Nat :=
  match i with
  | 0 => (3155, 3158)
  | 1 => (7663, 7666)
  | 2 => (5025, 5032)
  | 3 => (6657, 6661)
  | _ => (7660, 7662)

private def localKeeps (i : Fin 5) : List Nat :=
  if i = 4 then [1062, 7151, 1606] else [1062]

private def simpleLocal (i : Fin 5) (ins : Instr) (pc : Nat) : Bool :=
  ins.op.isLocal && (localKeeps i).all (fun r => !(writesRegs ins.op).contains r) &&
    !(Assumptions.swExp2Sites.contains pc) &&
    match ins.op with
    | .bra .. | .brx .. => false
    | _ => true

private theorem simpleLocalCode (i : Fin 5) {pc : Nat} {ins : Instr}
    (hLo : (localSlice i).1 ≤ pc) (hHi : pc < (localSlice i).2)
    (hc : kernel.code[pc]? = some ins) : simpleLocal i ins pc = true := by
  let lo := (localSlice i).1
  let hi := (localSlice i).2
  have hAll : (((kernel.code.drop lo).take (hi - lo)).zipIdx lo).all
      (fun p => simpleLocal i p.1 p.2) = true := by
    fin_cases i <;> set_option maxRecDepth 100000 in kernel_rfl
  have hLo' : lo ≤ pc := hLo
  have hHi' : pc < hi := hHi
  apply List.all_eq_true.mp hAll (ins, pc)
  apply List.mem_of_getElem? (i := pc - lo)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo', hc]
  rfl

private theorem simpleLocalFrame (i : Fin 5) {l : Launch} {g : Nat} {s u : TState}
    (hLo : (localSlice i).1 ≤ s.pc) (hHi : s.pc < (localSlice i).2)
    (ht : Tau kernel Assumptions.all l g s u) :
    u.pc = s.pc + 1 ∧ u.sub ≤ s.sub ∧ u.fault = none ∧
      ∀ r ∈ localKeeps i, u.regs r = s.regs r := by
  obtain ⟨ins, hc, hF, hx⟩ := tauScoreSource ht
  have hOk := simpleLocalCode i hLo hHi hc
  simp only [simpleLocal, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hOk
  rcases hx with ⟨rfl, _⟩ | ⟨_, _, he⟩
  · exact ⟨rfl, Nat.zero_le _, hF, fun _ _ => rfl⟩
  · have h := (scoreExecLocal he).resolve_right (fun ⟨_, hm, _, _⟩ => hOk.1.2 hm)
    have hP : u.pc = s.pc + 1 := by
      have hPc := h.pc
      cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
      case bra => simp [hop] at hOk
      case brx => simp [hop] at hOk
      all_goals exact hPc
    exact ⟨hP, h.sub.le, h.fault.trans hF, fun r hr =>
      h.regs r (by simpa using List.all_eq_true.mp hOk.1.1.2 r hr)⟩

private theorem cutSilentSlice (i : Fin 5) {l : Launch} {g cutoff : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hLo : (localSlice i).1 ≤ s.pc) (hHi : s.pc ≤ (localSlice i).2)
    (hF : s.fault = none) (hCut : (localSlice i).2 ≤ cutoff) :
    countedUntil cutoff vs ≤ 1 ∨
      ∃ u rest tail, u.pc = (localSlice i).2 ∧ u.sub ≤ s.sub ∧ u.fault = none ∧
        (∀ r ∈ localKeeps i, u.regs r = s.regs r) ∧
        run kernel Assumptions.all l g ((localSlice i).2 - s.pc) s = some u ∧
        Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil cutoff vs ≤ countedUntil cutoff tail := by
  induction hw with
  | stop => exact .inl (by simp [countedUntil])
  | @last s e he =>
    left
    by_cases hPc : s.pc < cutoff
    · simpa [countedUntil, hPc, visit_pc, visit_ev, List.filterMap_cons] using
        (List.countP_le_length (l := [e]) (p := Event.counts))
    · simp [countedUntil, hPc, visit_pc]
  | @tau s t es vs ht hw ih =>
    by_cases hEnd : s.pc = (localSlice i).2
    · exact .inr ⟨s, es, _, hEnd, le_rfl, hF, fun _ _ => rfl,
        by rw [hEnd, Nat.sub_self]; rfl, .tau ht hw, le_rfl⟩
    · have hLt : s.pc < (localSlice i).2 := by omega
      obtain ⟨hp, hS, hF', hRegs⟩ := simpleLocalFrame i hLo hLt ht
      have hLen : (localSlice i).2 - s.pc = ((localSlice i).2 - t.pc) + 1 := by omega
      have hLt' := hLt.trans_le hCut
      rcases ih (by omega) (by omega) hF' with h | ⟨u, rest, tail, hu, huS, huF, huR, hr, hW, hC⟩
      · exact .inl (by
          simpa [countedUntil, hLt', visit_pc, visit_ev, List.filterMap_cons] using h)
      · refine .inr ⟨u, rest, tail, hu, huS.trans hS, huF,
          fun r h => (huR r h).trans (hRegs r h), ?_, hW, ?_⟩
        · rw [hLen, run, tauStep_iff.mpr ht, Option.bind_some]
          exact hr
        · simpa [countedUntil, hLt', visit_pc, visit_ev, List.filterMap_cons] using hC
  | @ev s t e es vs he hw ih =>
    by_cases hEnd : s.pc = (localSlice i).2
    · exact .inr ⟨s, e :: es, _, hEnd, le_rfl, hF, fun _ _ => rfl,
        by rw [hEnd, Nat.sub_self]; rfl, .ev he hw, le_rfl⟩
    · obtain ⟨j, hj, hl, _⟩ := estep_event_source he
      have h := simpleLocalCode i hLo (by omega) hj
      simp only [simpleLocal, hl, Bool.false_and, Bool.false_eq_true] at h

private theorem cutDynamicLoop (loop : ScoreLoop) {l : Launch} {g w cutoff : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : s.pc = (scoreLoopSite loop).head) (hSub : s.sub ≤ 3)
    (hWord : s.regs (scoreLoopSite loop).word = some (b32 w)) (hw₀ : w < 2 ^ 32)
    (hCut : (scoreLoopSite loop).increment + 4 ≤ cutoff) :
    let stop := (scoreLoopSite loop).increment + 4
    countedUntil cutoff vs ≤ 8192 * 2 ^ 32 ∨
      ∃ u rest tail, u.pc = stop ∧ u.fault = none ∧ u.sub ≤ 3 ∧
        u.regs 1062 = s.regs 1062 ∧ Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil cutoff vs ≤ 8192 * 2 ^ 32 + countedUntil cutoff tail := by
  dsimp only
  let site := scoreLoopSite loop
  let stop := site.increment + 4
  have hHi : s.pc < stop := by rw [hs]; cases loop <;> decide
  have hBound := scoreLoopPrefixUniform loop hw hs hSub hWord hw₀
  let P := fun t : TState => t.sub ≤ 3 ∧ t.regs 1062 = s.regs 1062
  have hInit : P s := ⟨hSub, rfl⟩
  have hStep {t u : TState} {e : Option Event} (hL : site.head ≤ t.pc) (hH : t.pc < stop)
      (he : WStep kernel Assumptions.all l g t e u) (hT : P t) :
      (site.head ≤ u.pc ∧ u.pc < stop ∨ u.pc ∈ [stop] ∧ u.fault = none) ∧ P u := by
    obtain ⟨hLo, hHi, hs, hf, hr⟩ := scoreLoopStepFrame loop hL hH hT.1 he
    have hHi' : u.pc ≤ stop := hHi
    refine ⟨?_, hs, hr.trans hT.2⟩
    rcases hHi'.lt_or_eq with hh | hE
    · exact .inl ⟨hLo, hh⟩
    · exact .inr ⟨by simp [hE], hf.resolve_right (by omega)⟩
  rcases cutWalkInterval hw hs.ge hHi hInit hCut hStep with
    h | ⟨u, rest, tail, hp, hf, ⟨hS, hR⟩, hW, hb⟩
  · exact .inl (h.trans hBound)
  · exact .inr ⟨u, rest, tail, List.mem_singleton.mp hp, hf, hS, hR, hW,
      hb.trans (Nat.add_le_add_right hBound _)⟩

private theorem boundWindow {l : Launch} {g n : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (win : ScoreWindow) (hw : Walk kernel Assumptions.all l g s es vs)
    (hl : (windowSite win).head ≤ s.pc) (hh : s.pc < (windowSite win).stop)
    (hs : s.sub ≤ 3)
    (cont : ∀ {t rest tail}, (t.pc = (windowSite win).stop ∨
      t.pc ∈ (windowSite win).exits) → t.fault = none → t.sub ≤ 3 →
      (∀ r ∈ (windowSite win).keeps, t.regs r = s.regs r) →
      Walk kernel Assumptions.all l g t rest tail → countedUntil 9206 tail ≤ n) :
    countedUntil 9206 vs ≤ 5 * ((windowSite win).stop - (windowSite win).head) + 2 + n := by
  have hCut : (windowSite win).stop ≤ 9206 := by cases win <;> decide
  rcases cutSoftmaxWindow win hw hl hh hs hCut with
    h | ⟨u, rest, tail, hp, hf, hS, hR, hW, hC⟩
  · exact h.trans (Nat.le_add_right _ _)
  · exact hC.trans (Nat.add_le_add_left (cont hp hf hS hR hW) _)

private theorem terminalPhase {l : Launch} {g : Nat} (warp : Fin 8) {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hP : s.pc = 7720 ∨ s.pc = 7733) (hs : s.sub ≤ 3) (hW : s.regs 1062 = some (b32 warp.val)) :
    countedUntil 9206 vs ≤ 113 := by
  have hl : (windowSite .finalWait).head ≤ s.pc := by change 7720 ≤ s.pc; omega
  have hh : s.pc < (windowSite .finalWait).stop := by change s.pc < 7742; omega
  exact boundWindow .finalWait hw hl hh hs (n := 1) (by
    intro u rest tail hp hf hSub hR hWalk
    exact exitSoftmaxBound warp hWalk (by simpa [windowSite] using hp) hf
      ((hR 1062 (by decide)).trans hW))

private def scanBudget (p : Params) : Nat := 64 * (p.batch + 1)
private def scoreBudget : Nat := 8192 * 2 ^ 32

private theorem softmaxScanBound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g cta n : Nat} (drain : Bool) (hCta : cta + 1 < 2 ^ 31)
    {s : TState} {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hs : At s ((scanSite (scanFor drain)).head - 3)
      [((scanSite (scanFor drain)).cta, b32 cta), ((scanSite (scanFor drain)).batch, b32 p.batch)])
    (cont : ∀ {u rest tail}, u.pc = (scanSite (scanFor drain)).compare + 3 →
      u.fault = none → u.sub ≤ 3 → u.regs 1062 = s.regs 1062 →
      Walk kernel Assumptions.all l g u rest tail → countedUntil 9206 tail ≤ n) :
    countedUntil 9206 vs ≤ scanBudget p + n := by
  let i : Fin 5 := if drain then 1 else 0
  let scan := scanFor drain
  let site := scanSite scan
  have hFrom : (localSlice i).1 = site.head - 3 := by cases drain <;> rfl
  have hEnd : (localSlice i).2 = site.head := by cases drain <;> rfl
  have hSpan : site.head - (site.head - 3) = 3 := by cases drain <;> decide
  have hLt : s.pc ≤ (localSlice i).2 := by rw [hs.1, hEnd]; exact Nat.sub_le _ _
  have hBatch : p.batch + 31 < 2 ^ 31 := by have := hp.shape.2.2.2.2.2; omega
  have hCut : (localSlice i).2 ≤ 9206 := by cases drain <;> decide
  have hCut' : site.compare + 3 ≤ 9206 := by cases drain <;> decide
  rcases cutSilentSlice i hw (hFrom.symm ▸ hs.1.ge) hLt hs.2.2.2.1 hCut with
    h | ⟨v, rest, tail, hv, hvS, hvF, hvR, hr, hvW, hvC⟩
  · exact h.trans (by unfold scanBudget; omega)
  · rw [hEnd, hs.1, hSpan] at hr
    have hvA := groupInitFromRun scan hCta hs hr
    rcases cutScanRole drain hvW hBatch hCta hvA hCut' with
      h | ⟨u, after, post, hu, huF, huS, huR, huW, huC⟩
    · exact (hvC.trans h).trans (Nat.le_add_right _ _)
    · have he : u.regs 1062 = s.regs 1062 := huR.trans (hvR 1062 (by cases drain <;> decide))
      exact (hvC.trans huC).trans (Nat.add_le_add_left (cont hu huF huS he huW) _)

private def loopInitSlice : ScoreLoop → Fin 5
  | .biased => 2
  | .plain => 3

private theorem computeLoopBound {l : Launch} {g n : Nat} (loop : ScoreLoop)
    {s : TState} {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hp : s.pc = scoreInitPc loop) (hf : s.fault = none) (hs : s.sub ≤ 3)
    (hBias : loop = .biased → ∃ v, s.regs 1359 = some (.bits 32 v))
    (cont : ∀ {u rest tail}, u.pc = (scoreLoopSite loop).increment + 4 →
      u.fault = none → u.sub ≤ 3 → u.regs 1062 = s.regs 1062 →
      Walk kernel Assumptions.all l g u rest tail → countedUntil 9206 tail ≤ n) :
    countedUntil 9206 vs ≤ scoreBudget + n := by
  let i := loopInitSlice loop
  have hLo : (localSlice i).1 = scoreInitPc loop := by cases loop <;> rfl
  have hHi : (localSlice i).2 = (scoreLoopSite loop).head := by cases loop <;> rfl
  have hLe : s.pc ≤ (localSlice i).2 := by rw [hp]; cases loop <;> decide
  have hCut : (localSlice i).2 ≤ 9206 := by cases loop <;> decide
  have hExit : (scoreLoopSite loop).increment + 4 ≤ 9206 := by cases loop <;> decide
  rcases cutSilentSlice i hw (hLo.symm ▸ hp.ge) hLe hf hCut with
    h | ⟨v, rest, tail, hv, hvS, hvF, hvR, hr, hvW, hvC⟩
  · exact h.trans (by unfold scoreBudget; omega)
  · rw [hHi, hp] at hr
    obtain ⟨hP, hS, w, hW, hR⟩ := scoreLoopInitialized loop hp hs hBias hr
    rcases cutDynamicLoop loop hvW hP hS hR hW hExit with
      h | ⟨u, after, post, hu, huF, huS, huR, huW, huC⟩
    · exact (hvC.trans h).trans (Nat.le_add_right _ _)
    · have he : u.regs 1062 = s.regs 1062 := huR.trans (hvR 1062 (by cases loop <;> decide))
      exact (hvC.trans huC).trans (Nat.add_le_add_left (cont hu huF huS he huW) _)

private theorem drainCtaRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) {s : TState} (hs : s.pc = 7659) (hf : s.fault = none) :
    run kernel Assumptions.all l g 1 s = some (next (setReg s 1606 (b32 (g / l.block)))) := by
  have hGrid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hWord : g / l.block < 2 ^ 32 := by have := hp.grid.2.2; omega
  have hCta := (sregValue_oneDim hp.cluster.2.2 g).2.2.1
  refine localRoleRun hf (by rw [hs]; exact Flow.code_7659) rfl rfl (by rw [hs]; decide) rfl ?_
  rw [execLocal_move rfl]
  simp only [execMove, DType.width, readValue, SReg.width, readBits,
    hCta, bind, Except.bind, pure, Except.pure, truncBits_ofNat hWord (by decide)]
  rfl

private theorem ctaWithin {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) : g / l.block + 1 < 2 ^ 31 :=
  (Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg)).trans_lt hp.grid.2.2

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat} (hg : g < l.threads)
    (warp : Fin 8) {s : TState} {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs)
include hp hg warp hw

private theorem drainGateBound (hpC : s.pc = 7662) (hs : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 warp.val)) (hB : s.regs 7151 = some (b32 p.batch))
    (hC : s.regs 1606 = some (b32 (g / l.block))) :
    countedUntil 9206 vs ≤ scanBudget p + 113 := by
  rcases cutScanGate (cutoff := 9206) hw (hpC.symm ▸ Flow.code_7662) (by rw [hpC]; decide)
    (by rw [hpC]; decide) with h | ⟨u, rest, tail, hu, hS, hF, hR, hW, hCount⟩
  · exact h.trans (by omega)
  · have hU : u.regs 1062 = some (b32 warp.val) := by rw [hR]; exact hWarp
    rcases hu with hLate | ⟨hEarly, hSub, hAcc⟩
    · exact hCount.trans ((terminalPhase warp hW (.inl hLate) (hS.trans hs) hU).trans
        (Nat.le_add_left _ _))
    · have ht : At u 7663 [(1606, b32 (g / l.block)), (7151, b32 p.batch)] :=
        ⟨by rw [hEarly, hpC], hSub, hAcc, hF, by rw [hR]; exact ⟨hC, hB, trivial⟩⟩
      exact hCount.trans (softmaxScanBound hp true (ctaWithin hp hg) hW ht (n := 113) (by
        intro t rest tail hp hf hs hR hW
        exact terminalPhase warp hW (.inl hp) hs (hR.trans hU)))

omit hp hg warp hw in
private def drainBudget (p : Params) : Nat := scanBudget p + 512

private theorem drainPhase (hPc : s.pc = 7605) (hF : s.fault = none) (hs : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 warp.val)) :
    countedUntil 9206 vs ≤ drainBudget p := by
  let t := next (setReg s 7151 (b32 p.batch))
  have hr : run kernel Assumptions.all l g 1 s = some t := actualBatchLoad hp true hPc hF
  have hPt : t.pc = 7606 := by simp [t, next, setReg, hPc]
  have htB : t.regs 7151 = some (b32 p.batch) := by simp [t, next, setReg]
  have htW : t.regs 1062 = some (b32 warp.val) := by
    simpa [t, next, setReg, Function.update_of_ne] using hWarp
  rcases Mma.advanceWalkLocals hr hw with h | ⟨tail, _, hCount, hWalk⟩
  · subst es
    simp [Mma.zeroCountNoEvents hw]
  · have hb := boundWindow .drainPrelude hWalk (by rw [hPt]; decide)
      (by rw [hPt]; decide) (show t.sub ≤ 3 from hs) (n := scanBudget p + 113) (by
        intro v rest tail hP hf hS hR hW
        have hpV : v.pc = 7659 := by simpa [windowSite] using hP
        let w := next (setReg v 1606 (b32 (g / l.block)))
        have hRun : run kernel Assumptions.all l g 1 v = some w := drainCtaRun hp hg hpV hf
        have hPcW : w.pc = 7660 := by simp [w, next, setReg, hpV]
        have hwC : w.regs 1606 = some (b32 (g / l.block)) := by simp [w, next, setReg]
        have hwB : w.regs 7151 = some (b32 p.batch) := by
          change Function.update v.regs 1606 (some (b32 (g / l.block))) 7151 = _
          rw [Function.update_of_ne (by decide : 7151 ≠ 1606)]
          exact (hR 7151 (by decide)).trans htB
        have hwW : w.regs 1062 = some (b32 warp.val) := by
          change Function.update v.regs 1606 (some (b32 (g / l.block))) 1062 = _
          rw [Function.update_of_ne (by decide : 1062 ≠ 1606)]
          exact (hR 1062 (by decide)).trans htW
        rcases Mma.advanceWalkLocals hRun hW with h | ⟨tail, _, hC, hW'⟩
        · subst rest
          simp [Mma.zeroCountNoEvents hW]
        · rcases cutSilentSlice (cutoff := 9206) 4 hW' (by rw [hPcW]; decide) (by rw [hPcW]; decide)
            (show w.fault = none from hf) (by decide) with h |
              ⟨u, rest, tail, hu, huS, huF, huR, _, huW, huC⟩
          · exact ((hC 9206).trans h).trans (by omega)
          · exact ((hC 9206).trans huC).trans (drainGateBound hp hg warp huW hu
              (huS.trans (show w.sub ≤ 3 from hS)) ((huR 1062 (by decide)).trans hwW)
              ((huR 7151 (by decide)).trans hwB) ((huR 1606 (by decide)).trans hwC)))
    exact (hCount 9206).trans (hb.trans (by
      unfold drainBudget
      change 267 + (scanBudget p + 113) ≤ scanBudget p + 512
      omega))

omit hp hg warp hw in
private def plainBudget (p : Params) : Nat := scoreBudget + drainBudget p + 32

private theorem plainPhase (hPc : s.pc = 6654) (hs : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 warp.val)) :
    countedUntil 9206 vs ≤ plainBudget p := by
  have hb := boundWindow .plainPrelude hw (by rw [hPc]; decide) (by rw [hPc]; decide)
    hs (n := scoreBudget + drainBudget p) (by
      intro u rest tail hu hf hS hR hW
      have hRole := (hR 1062 (by decide)).trans hWarp
      have hCases : u.pc = 6657 ∨ u.pc = 7605 := by simpa [windowSite] using hu
      rcases hCases with hLoop | hDrain
      · exact computeLoopBound .plain hW hLoop hf hS (by intro h; cases h) (by
          intro t rest tail ht hF htS htR htW
          exact drainPhase hp hg warp htW ht hF htS (htR.trans hRole))
      · exact (drainPhase hp hg warp hW hDrain hf hS hRole).trans (Nat.le_add_left _ _))
  exact hb.trans (by
    unfold plainBudget
    change 17 + (scoreBudget + drainBudget p) ≤ scoreBudget + drainBudget p + 32
    omega)

private theorem biasedPreludeBound (hPc : s.pc = 5009) (hs : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 warp.val)) (hInput : ∃ v, s.regs 1359 = some (.bits 32 v)) :
    countedUntil 9206 vs ≤ scoreBudget + plainBudget p + 128 := by
  have hb := boundWindow .biasedPrelude hw (by rw [hPc]; decide) (by rw [hPc]; decide)
    hs (n := scoreBudget + plainBudget p) (by
      intro u rest tail hu hf hS hR hW
      have hRole := (hR 1062 (by decide)).trans hWarp
      have hCases : u.pc = 5025 ∨ u.pc = 6654 := by simpa [windowSite] using hu
      rcases hCases with hLoop | hPlain
      · exact computeLoopBound .biased hW hLoop hf hS (fun _ => by
          rw [hR 1359 (by decide)]
          exact hInput) (by
            intro t rest tail ht hF htS htR htW
            exact plainPhase hp hg warp htW ht htS (htR.trans hRole))
      · exact (plainPhase hp hg warp hW hPlain hS hRole).trans (Nat.le_add_left _ _))
  exact hb.trans (by
    change 82 + (scoreBudget + plainBudget p) ≤ scoreBudget + plainBudget p + 128
    omega)

omit hp hg warp hw in
private theorem biasedTripInput {l : Launch} {g : Nat} {s u : TState}
    (hp : s.pc = 5008) (ht : Tau kernel Assumptions.all l g s u) :
    u.pc = 5009 ∧ u.sub = s.sub ∧ u.regs 1062 = s.regs 1062 ∧
      ∃ v, u.regs 1359 = some (.bits 32 v) := by
  obtain ⟨i, hc, hf, hex⟩ := tauScoreSource ht
  rw [hp, Flow.code_5008] at hc
  obtain rfl := (Option.some.inj hc).symm
  rcases hex with ⟨_, hG⟩ | ⟨_, _, he⟩
  · cases hG
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hp]; decide
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl,
      execLocalA_nil, execLocal_int rfl] at he
    have hExpr : execInt l g s
        { op := .max false, ty := .int .s 32, dsts := [some 1359],
          srcs := [.reg 3955, .imm 0] } =
        (readBits l g s 32 (.reg 3955) >>= fun a =>
          pure (next (setReg s 1359 (.bits 32 (if compare .gt .s 32 a 0 then a else 0))))) := rfl
    rw [hExpr] at he
    cases hR : readBits l g s 32 (.reg 3955) with
    | error e => simp [hR, bind, Except.bind] at he
    | ok a =>
      simp only [hR, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at he
      subst u
      refine ⟨by simp [next, setReg, hp], rfl, by simp [next, setReg], ?_⟩
      exact ⟨if compare .gt .s 32 a 0 then a else 0, by simp [next, setReg]⟩

omit hp hg warp hw in
private def biasedBudget (p : Params) : Nat := scoreBudget + plainBudget p + 128

private theorem biasedPhase (hPc : s.pc = 5008) (hs : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 warp.val)) :
    countedUntil 9206 vs ≤ biasedBudget p := by
  have hLt : s.pc < 9206 := by rw [hPc]; decide
  cases hw with
  | stop => simp [countedUntil]
  | ev he _ => exact (localNeverReturns (hPc.symm ▸ Flow.code_5008) rfl he).elim
  | @last s e he =>
    have h := List.countP_le_length (l := [e]) (p := Event.counts)
    have hC : countedUntil 9206 [visit kernel l g s (some e)] ≤ 1 := by
      simpa [countedUntil, hLt, visit_pc, visit_ev, List.filterMap_cons] using h
    exact hC.trans (by unfold biasedBudget; omega)
  | tau hTau hW =>
    have ⟨hU, hS, hR, hBits⟩ := biasedTripInput hPc hTau
    have hBound := biasedPreludeBound hp hg warp hW hU (hS.symm ▸ hs) (hR.trans hWarp) hBits
    simpa [biasedBudget, countedUntil, hLt, visit_pc, visit_ev, List.filterMap_cons] using hBound

omit hp hg warp hw in
private def firstBudget (p : Params) : Nat := biasedBudget p + 10000

private theorem firstPhase (hPc : s.pc = 3212) (hs : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 warp.val)) :
    countedUntil 9206 vs ≤ firstBudget p := by
  have hb := boundWindow .firstRound hw (by rw [hPc]; decide) (by rw [hPc]; decide)
    hs (n := biasedBudget p) (by
      intro u rest tail hu hf hS hR hW
      have hRole := (hR 1062 (by decide)).trans hWarp
      have hCases : u.pc = 5008 ∨ u.pc = 7733 := by simpa [windowSite] using hu
      rcases hCases with hLoop | hTail
      · exact biasedPhase hp hg warp hW hLoop hS hRole
      · exact (terminalPhase warp hW (.inr hTail) hS hRole).trans (by unfold biasedBudget; omega))
  exact hb.trans (by
    unfold firstBudget
    change 8982 + biasedBudget p ≤ biasedBudget p + 10000
    omega)

private theorem selectGateBound (hPc : s.pc = 3154) (hs : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 warp.val)) (hB : s.regs 7247 = some (b32 p.batch))
    (hC : s.regs 1072 = some (b32 (g / l.block))) :
    countedUntil 9206 vs ≤ scanBudget p + firstBudget p := by
  rcases cutScanGate (cutoff := 9206) hw (hPc.symm ▸ Flow.code_3154)
    (by rw [hPc]; decide) (by rw [hPc]; decide) with h | ⟨u, rest, tail, hu, hS, hF, hR, hW, hCount⟩
  · exact h.trans (by unfold scanBudget; omega)
  · have hU : u.regs 1062 = some (b32 warp.val) := by rw [hR]; exact hWarp
    rcases hu with hLate | ⟨hEarly, hSub, hAcc⟩
    · exact hCount.trans ((firstPhase hp hg warp hW hLate (hS.trans hs) hU).trans
        (Nat.le_add_left _ _))
    · have ht : At u 3155 [(1072, b32 (g / l.block)), (7247, b32 p.batch)] :=
        ⟨by rw [hEarly, hPc], hSub, hAcc, hF, by rw [hR]; exact ⟨hC, hB, trivial⟩⟩
      exact hCount.trans (softmaxScanBound hp false (ctaWithin hp hg) hW ht (n := firstBudget p)
        (by
          intro t rest tail hp hf hs hR hWalk
          exact firstPhase ‹Pre p l m› hg warp hWalk hp hs (hR.trans hU)))

private theorem selectPhase (hPc : s.pc = 3104) (hs : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 warp.val)) (hB : s.regs 7247 = some (b32 p.batch))
    (hC : s.regs 1072 = some (b32 (g / l.block))) :
    countedUntil 9206 vs ≤ 252 + (scanBudget p + firstBudget p) :=
  boundWindow .selectPrelude hw (by rw [hPc]; decide) (by rw [hPc]; decide)
    hs (n := scanBudget p + firstBudget p) (by
      intro u rest tail hu hf hS hR hW
      have hP : u.pc = 3154 := by simpa [windowSite] using hu
      exact selectGateBound hp hg warp hW hP hS ((hR 1062 (by decide)).trans hWarp)
        ((hR 7247 (by decide)).trans hB) ((hR 1072 (by decide)).trans hC))

omit hp hg warp hw in
private theorem consumeFixed {l : Launch} {g cutoff : Nat} {s u : TState}
    {es : List Event} {vs : List Visit} {tmpl : Tmpl}
    (hw : Walk kernel Assumptions.all l g s es vs)
    (ho : out kernel Assumptions.all l g s = .ev tmpl)
    (hNext : ∀ e t, Fires s.pc tmpl e (some t) → t = u) :
    countedUntil cutoff vs ≤ 1 ∨
      ∃ rest tail, Walk kernel Assumptions.all l g u rest tail ∧
        countedUntil cutoff vs ≤ countedUntil cutoff tail + 1 := by
  cases hw with
  | stop => exact .inl (by simp [countedUntil])
  | tau ht _ => exact (not_tau_of_stops ⟨_, ho⟩ ht).elim
  | @last s e he =>
    left
    by_cases hp : s.pc < cutoff
    · simpa [countedUntil, hp, visit_pc, visit_ev, List.filterMap_cons] using
        (List.countP_le_length (l := [e]) (p := Event.counts))
    · simp [countedUntil, hp, visit_pc]
  | @ev s t e rest tail he hw =>
    obtain ⟨real, hr, hFire⟩ := he
    obtain rfl := Out.ev.inj (hr.symm.trans ho)
    obtain rfl := hNext _ _ hFire
    refine .inr ⟨rest, tail, hw, ?_⟩
    by_cases hp : s.pc < cutoff
    · have he : (if e.counts then 1 else 0) ≤ 1 := by split <;> decide
      simpa [countedUntil, hp, visit_pc, visit_ev, List.filterMap_cons, List.countP_cons] using
        Nat.add_le_add_left he (countedUntil cutoff tail)
    · simp [countedUntil, hp, visit_pc]

omit hp hg warp hw in
/-- Bound for the two score loops, both group scans, and intervening control and dataflow. -/
def softmaxRoleBudget (p : Params) : Nat := 254 + (64 * (p.batch + 1) +
  (8192 * 2 ^ 32 + (8192 * 2 ^ 32 + (64 * (p.batch + 1) + 512) + 32) + 128 + 10000))

private theorem softmaxEntryBound
    (hS : At s 3101 [(1062, b32 warp.val), (1072, b32 (g / l.block)), (2535, b32 l.sharedBase)]) :
    countedUntil 9206 vs ≤ softmaxRoleBudget p := by
  let t := next (setReg s 7247 (b32 p.batch))
  have hr : run kernel Assumptions.all l g 1 s = some t :=
    actualBatchLoad hp false hS.1 hS.2.2.2.1
  have ht : At t 3102 [(7247, b32 p.batch), (1062, b32 warp.val),
      (1072, b32 (g / l.block)), (2535, b32 l.sharedBase)] := hS.set (by simp)
  rcases Mma.advanceWalkLocals hr hw with h | ⟨tail, _, hC, hW⟩
  · subst es
    simp [Mma.zeroCountNoEvents hw]
  · rcases consumeFixed hW (firstHint ht)
        (fun e u h => Option.some.inj h.choose_spec.2) (cutoff := 9206) with
      h | ⟨rest, tail, hW', hC'⟩
    · exact ((hC 9206).trans h).trans (by unfold softmaxRoleBudget; omega)
    · have hbOut := entryBarrier (g := g) hp.block ht.next
      rcases consumeFixed hW' hbOut (fun e u h => Option.some.inj h.2) (cutoff := 9206) with
        h | ⟨rest₂, tail₂, hW₂, hC₂⟩
      · have hFinal := (hC 9206).trans (hC'.trans (Nat.add_le_add_right h 1))
        exact hFinal.trans (by unfold softmaxRoleBudget; omega)
      · have hua := ht.next.next
        have hFin := selectPhase hp hg warp hW₂ hua.1
          (hua.2.1.symm ▸ Nat.zero_le _) hua.2.2.2.2.2.1
          hua.2.2.2.2.1 hua.2.2.2.2.2.2.1
        have hTotal := (hC 9206).trans (hC'.trans (Nat.add_le_add_right
          (hC₂.trans (Nat.add_le_add_right hFin 1)) 1))
        exact hTotal.trans (by
          change 252 + (scanBudget p + firstBudget p) + 1 + 1 ≤
            254 + (scanBudget p + firstBudget p)
          omega)

/-- Both softmax groups have a uniform counted-event bound on every actual post-prologue walk. -/
theorem softmaxRolePrefixBound (hs : At s 174 [(1062, b32 warp.val), (2535, b32 l.sharedBase)]) :
    es.countP Event.counts ≤ softmaxRoleBudget p + 1 := by
  have hCount : countedUntil 9206 vs ≤ softmaxRoleBudget p := by
    let wide := Fin.castLE (by decide : 8 ≤ 16) warp
    obtain ⟨u, hu, hU⟩ := dispatchRunFromCommon hp wide hg hs
    have hPc : dispatchParamPc wide = 3101 := by fin_cases warp <;> rfl
    rw [hPc] at hU
    rcases Mma.advanceWalkLocals hu hw with h | ⟨tail, _, hC, hW⟩
    · subst es
      simp [Mma.zeroCountNoEvents hw]
    · exact (hC 9206).trans (softmaxEntryBound hp hg warp hW hU)
  have hAll := countedThroughCode hw
  have hLen : kernel.code.length = 9206 := by
    set_option maxRecDepth 100000 in kernel_rfl
  rw [hLen] at hAll
  exact hAll.trans (Nat.add_le_add_right hCount 1)

end
end PTX.Kernels.TmlFa4Fwd.Softmax
