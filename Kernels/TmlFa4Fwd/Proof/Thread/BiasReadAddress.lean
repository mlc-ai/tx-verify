-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedBiasAddresses
public import Kernels.TmlFa4Fwd.Proof.Thread.SharedReadSites
public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstAddress
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasAddresses
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasAddressArithmetic
import Kernels.TmlFa4Fwd.Proof.MmaQkKeyLayout
import Lemmas.Flow.ElemAccess
import Lemmas.Flow.TcLdTmpl
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreTrace
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainScoreEntry
import Kernels.TmlFa4Fwd.Proof.StatsBarrierSetup
import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasLeader
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRendezvous
import Kernels.TmlFa4Fwd.Proof.SoftmaxWaits
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasFmaEntry
import Kernels.TmlFa4Fwd.Flow.Code.Part056
import Lemmas.Flow.PackMul
import Lemmas.Flow.Polls
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores

open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption Softmax

private inductive BiasSegment where
  | initial
  | row
  | statisticsBarrier
  | firstScoreBase
  | firstScoreExtra (late : Bool)
  | biasedScore
  | unbiasedScore
  | firstProbability
  | biasedProbabilityStage
  | biasedProbability
  | unbiasedProbability
  | vector (i : Fin 14)
  | first
  | scaleLoad
  | scalePack

private def segments : List BiasSegment :=
  [.initial, .row, .statisticsBarrier, .first, .scaleLoad, .scalePack, .firstProbability,
    .biasedProbabilityStage, .biasedProbability, .unbiasedProbability, .firstScoreBase,
    .firstScoreExtra false, .firstScoreExtra true, .biasedScore, .unbiasedScore] ++
    (List.finRange 14).map BiasSegment.vector

private theorem memSegments (b : BiasSegment) : b ∈ segments := by
  cases b <;> try simp [segments, List.mem_finRange]

private def BiasSegment.start : BiasSegment → Nat
  | .statisticsBarrier => 3274
  | .firstScoreBase => 3286
  | .firstScoreExtra late => if late then 3480 else 3445
  | .biasedScore => 5032
  | .unbiasedScore => 6661
  | .initial => 3286
  | .firstProbability => 3850
  | .biasedProbabilityStage => 5675
  | .biasedProbability => 6299
  | .unbiasedProbability => 6661
  | .row => 5032
  | .vector i => 5046 + 4 * i.val
  | .first => 5184
  | .scaleLoad => 3591
  | .scalePack => 3596

private def BiasSegment.length : BiasSegment → Nat
  | .statisticsBarrier => 9
  | .firstScoreBase => 23
  | .firstScoreExtra _ => 1
  | .biasedScore => 9
  | .unbiasedScore => 11
  | .initial => 79
  | .firstProbability => 13
  | .biasedProbabilityStage => 1
  | .biasedProbability => 9
  | .unbiasedProbability => 15
  | .row => 14
  | .vector _ => 4
  | .first => 5
  | .scaleLoad => 2
  | .scalePack => 1

private def BiasSegment.stop (b : BiasSegment) : Nat :=
  b.start + b.length

private def BiasSegment.inputs (p : Params) (l : Launch) (g : Nat) (w : Fin 8) :
    BiasSegment → List (Nat × Value)
  | .statisticsBarrier => [(1062,b32 w.val)]
  | .firstScoreBase => [(1062,b32 w.val),(2535,b32 l.sharedBase)]
  | .firstScoreExtra _ => [(2788,b32 (scoreAddress l g (stageOf w) 0))]
  | .biasedScore => [(1062,b32 w.val),(2535,b32 l.sharedBase)]
  | .unbiasedScore => [(1062,b32 w.val)]
  | .scaleLoad => []
  | .scalePack => [(7135,b32 p.invScaleBits)]
  | .initial => [(1062, b32 w.val), (2535, b32 l.sharedBase)]
  | .firstProbability => tailFrame l w
  | .biasedProbabilityStage => [(1062,b32 w.val)]
  | .unbiasedProbability => [(1062,b32 w.val),(2535,b32 l.sharedBase)]
  | .biasedProbability => [(637,.pred ((stageOf w).val = 1))]
  | .row => [(1062, b32 w.val), (2535, b32 l.sharedBase)]
  | .vector _ => [(3978, b32 (repeatedBiasRowBase l g + repeatedBiasStageOffset w))]
  | .first => [(3976, b32 (repeatedBiasRowBase l g)), (3977, b32 (repeatedBiasStageOffset w))]

private noncomputable def BiasSegment.outputs (p : Params) (l : Launch) (g : Nat) (w : Fin 8) :
    BiasSegment → List (Nat × Value)
  | .statisticsBarrier => [(5127,b32 (3+w.val))]
  | .firstScoreBase => [(2788,b32 (scoreAddress l g (stageOf w) 0)),
      (2789,b32 (scoreAddress l g (stageOf w) 2))]
  | .firstScoreExtra late => [(scoreReg .first (if late then 3 else 1),
      b32 (scoreAddress l g (stageOf w) (if late then 3 else 1)))]
  | .biasedScore => roundScoreFacts l g (stageOf w) .biased
  | .unbiasedScore => roundScoreFacts l g (stageOf w) .unbiased
  | .initial => firstBiasBases l g w
  | .scaleLoad => [(7135,b32 p.invScaleBits)]
  | .scalePack => [(7896,joinValue (b32 p.invScaleBits) (b32 p.invScaleBits))]
  | .firstProbability => (firstAddressFacts l g (stageOf w)).take 4
  | .biasedProbabilityStage => [(637,.pred ((stageOf w).val = 1))]
  | .biasedProbability => biasedAddressFacts l g (stageOf w)
  | .unbiasedProbability => (5187,b32 (l.sharedBase+8*(stageOf w).val)) ::
      (unbiasedAddressRows l g w).drop 1 ++ unbiasedProbabilityFacts l g (stageOf w)
  | .row => [(3976, b32 (repeatedBiasRowBase l g)), (3977, b32 (repeatedBiasStageOffset w)),
      (3978, b32 (repeatedBiasRowBase l g + repeatedBiasStageOffset w)),
      (631, .pred ((stageOf w).val = 1))]
  | .vector i => [(3982 + 4 * i.val, b32 (kvSwizzle (repeatedBiasRowBase l g +
        repeatedBiasStageOffset w + repeatedVectorDisplacement i))),
      (3978, b32 (repeatedBiasRowBase l g + repeatedBiasStageOffset w))]
  | .first => [(4170, b32 (kvSwizzle (repeatedBiasRowBase l g + 166912) +
        repeatedBiasStageOffset w))]

private theorem BiasSegment.run {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (w : Fin 8) (b : BiasSegment) :
    Seg kernel Assumptions.all l g b.length b.start (b.inputs p l g w)
      b.stop (b.outputs p l g w) := by
  cases b with
  | firstScoreBase => exact firstScoreBaseSetup hp g w
  | statisticsBarrier => exact softmaxStatsBarrierSetup l g w
  | firstScoreExtra late => cases late <;> exact firstScoreOtherQuarter l g (stageOf w) _
  | biasedScore => exact biasedScoreAddressSegment hp g w
  | unbiasedScore =>
    intro t ht
    obtain ⟨u,hr,hu⟩ := (unbiasedTensorAddressSegment hp g w).apply ht
    exact ⟨u,hr,hu.mono ((holds_append _ _ _).mp hu.2.2.2.2).2⟩
  | initial => exact firstBiasAddressBases hp g w
  | firstProbability =>
    intro t ht
    obtain ⟨u, hRun, hu⟩ := (firstPAddressSegment hp g w).apply ht
    exact ⟨u, hRun, hu.mono ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.1,
      hu.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.1, trivial⟩⟩
  | biasedProbabilityStage =>
    intro t ht
    fin_cases w <;>
      simp only [BiasSegment.inputs,BiasSegment.outputs,BiasSegment.length,
        BiasSegment.start,BiasSegment.stop] at ht ⊢ <;> seg_fp ht using decide
  | biasedProbability => exact biasedPAddressSegment hp g (stageOf w)
  | unbiasedProbability => exact plainReadyGeometrySegment hp g w
  | row => exact repeatedBiasRowSetupFramed hp g w
  | first => exact repeatedBiasFirstVectorSetup hp g w
  | scaleLoad =>
    intro t ht
    obtain ⟨u,hu,hRun,_⟩ := firstBiasFmaScaleLoads hp (g := g) ht
    exact ⟨u,hRun,hu.mono ⟨hu.2.2.2.2.1,trivial⟩⟩
  | scalePack =>
    intro t ht
    have hReg : t.regs 7135 = some (b32 p.invScaleBits) := ht.2.2.2.2.1
    let u := next (setReg t 7896 (joinValue (b32 p.invScaleBits) (b32 p.invScaleBits)))
    have hu : PTX.run kernel Assumptions.all l g 1 t = some u := by
      apply run_local Flow.code_3596 rfl ht
      rw [Assumptions.execLocalA_all_eq_numeric,
        Assumptions.execLocalA_eq_nil (by rw [show t.pc = 3596 from ht.1]; decide) rfl]
      have hc := exec_pack (A := []) (L := l) (g := g) (d := 7896)
        (by simp [NoPack]) hReg hReg SegFreePc.nil
      simpa only [show (b32 p.invScaleBits).bytes = 4 by rfl, beq_self_eq_true, true_and,
        Bool.and_true, ite_true] using hc
    have hU : Holds u.regs (BiasSegment.scalePack.outputs p l g w) :=
      ⟨by simp [u,next,setReg],trivial⟩
    exact ⟨u,hu,(ht.set (r := 7896) (v := joinValue (b32 p.invScaleBits) (b32 p.invScaleBits))
      (by simp [BiasSegment.inputs])).mono hU⟩
  | vector i =>
    have hStop : (BiasSegment.vector i).stop = 5050 + 4 * i.val := by
      simp only [BiasSegment.stop, BiasSegment.start, BiasSegment.length]
      omega
    rw [hStop]
    exact repeatedBiasOtherVectorSetup hp g w i

private def BiasSegment.executing (b : BiasSegment) (site : Nat) : Prop :=
  b.start ≤ site ∧ site < b.stop

private def BiasSegment.last : BiasSegment → Nat
  | .statisticsBarrier => 7604
  | .initial => 3576
  | .firstProbability => 4856
  | .biasedProbabilityStage => 6299
  | .biasedProbability => 6541
  | .unbiasedProbability => 7446
  | .firstScoreBase => 3480
  | .firstScoreExtra late => if late then 3481 else 3446
  | .biasedScore => 5163
  | .unbiasedScore => 6730
  | .scaleLoad => 3596
  | .scalePack => 7732
  | _ => 5264

private def BiasSegment.holding (b : BiasSegment) (site : Nat) : Prop :=
  b.stop ≤ site ∧ site ≤ b.last

private instance (b : BiasSegment) (site : Nat) : Decidable (b.executing site) :=
  inferInstanceAs (Decidable (b.start ≤ site ∧ site < b.stop))

private instance (b : BiasSegment) (site : Nat) : Decidable (b.holding site) :=
  inferInstanceAs (Decidable (b.stop ≤ site ∧ site ≤ b.last))

private def BiasSegment.registers : BiasSegment → List Nat
  | .statisticsBarrier => [5127]
  | .firstScoreBase => [2788,2789]
  | .firstScoreExtra late => [scoreReg .first (if late then 3 else 1)]
  | .biasedScore => List.ofFn (scoreReg .biased)
  | .unbiasedScore => List.ofFn (scoreReg .unbiased)
  | .scaleLoad => [7135]
  | .scalePack => [7896]
  | .firstProbability => [3223, 3224, 3225, 3226]
  | .biasedProbabilityStage => [637]
  | .biasedProbability => [4821, 4822, 4823, 4824]
  | .unbiasedProbability => [5187, 5176, 5177, 5183, 5185, 5181, 5184]
  | .initial => (List.finRange 16).map (fun i => (biasReadSite false i).base)
  | .row => [3976, 3977, 3978, 631]
  | .vector i => [3982 + 4 * i.val, 3978]
  | .first => [4170]

private theorem BiasSegment.outputRegisters (b : BiasSegment) (p : Params) (l : Launch)
    (g : Nat) (w : Fin 8) :
    (b.outputs p l g w).map Prod.fst = b.registers := by
  cases b <;> rfl

private def biasWrites (op : Op) : List Nat := writesRegs op ++ scoreEventWrites op

private def biasStepCode (site : Nat) (ins : Instr) : Bool :=
  ((ins.op.isLocal || scoreEventOp ins.op) && !(biasWrites ins.op).contains 2535) &&
  segments.all (fun b =>
    (if b.executing site then
      ins.op.isLocal && ins.guard.isNone && Epilogue.schedulerFallsThrough ins.op else true) &&
    (if b.holding site then b.registers.all (fun r => !(biasWrites ins.op).contains r) else true) &&
    match ins.op with
    | .bra dst _ =>
      decide (¬ (b.start < dst ∧ dst < b.stop)) &&
        decide (b.holding dst → b.holding site)
    | .brx .. => false
    | _ => true)

private def biasAddressAudit : List (Instr × Nat) :=
  ((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103

set_option maxRecDepth 100000 in
private theorem biasAddressAuditOk :
    biasAddressAudit.all (fun (ins,site) => biasStepCode site ins) = true := by decide +kernel

private theorem biasStepCodeAt {site : Nat} {ins : Instr} (hLo : 3103 ≤ site) (hHi : site < 7742)
    (hc : kernel.code[site]? = some ins) : biasStepCode site ins = true := by
  have hAt : biasAddressAudit[site - 3103]? = some (ins, site) := by
    dsimp only [biasAddressAudit]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo, hc]
    rfl
  have hMem : (ins,site) ∈ biasAddressAudit := List.mem_of_getElem? hAt
  exact List.all_eq_true.mp biasAddressAuditOk (ins,site) hMem

private def BiasSegment.remainder (b : BiasSegment) (p : Params) (l : Launch) (g : Nat)
    (w : Fin 8) (s : TState) : Prop :=
  ∃ t, PTX.run kernel Assumptions.all l g (b.stop - s.pc) s = some t ∧
    At t b.stop (b.outputs p l g w)

private def BiasAddressFrame (p : Params) (l : Launch) (g : Nat) (w : Fin 8) (s : TState) : Prop :=
  (∀ b : BiasSegment, b.start < s.pc → s.pc < b.stop → b.remainder p l g w s) ∧
    ∀ b : BiasSegment, b.holding s.pc → Holds s.regs (b.outputs p l g w)

private theorem BiasSegment.remainderStep {p : Params} {b : BiasSegment} {l : Launch}
    {g : Nat} {w : Fin 8} {s u : TState} (h : b.remainder p l g w s) (hLt : s.pc < b.stop)
    (hNext : u.pc = s.pc + 1) (ht : Tau kernel Assumptions.all l g s u) :
    b.remainder p l g w u := by
  obtain ⟨t, hr, hAt⟩ := h
  refine ⟨t, ?_, hAt⟩
  rwa [show b.stop - s.pc = (b.stop - u.pc) + 1 by omega, PTX.run, tauStep_iff.mpr ht,
    Option.bind_some] at hr

private theorem BiasSegment.remainderResult {p : Params} {b : BiasSegment} {l : Launch}
    {g : Nat} {w : Fin 8} {s : TState} (h : b.remainder p l g w s) (hAt : s.pc = b.stop) :
    Holds s.regs (b.outputs p l g w) := by
  obtain ⟨u, hRun, hResult⟩ := h
  rw [hAt, Nat.sub_self] at hRun
  obtain rfl := Option.some.inj hRun
  exact hResult.2.2.2.2

private theorem initialFrame {p : Params} {l : Launch} {g : Nat} {w : Fin 8} {s : TState}
    (hAt : s.pc = 3103) : BiasAddressFrame p l g w s := by
  have hStatic : ∀ b ∈ segments, 3103 ≤ b.start ∧ 3103 < b.stop := by decide
  constructor
  · intro b hStart _
    have h := (hStatic b (memSegments b)).1
    omega
  · intro b h
    have hs := (hStatic b (memSegments b)).2
    exact (Nat.not_le_of_lt hs (hAt ▸ h.1)).elim

private theorem inputAtEntry {p : Params} {l : Launch} {g : Nat} {w : Fin 8}
    {s : TState} {b : BiasSegment} (hAt : s.pc = b.start) (hFrame : BiasAddressFrame p l g w s)
    (hWarp : s.regs 1062 = some (b32 w.val)) (hBase : s.regs 2535 = some (b32 l.sharedBase)) :
    Holds s.regs (b.inputs p l g w) := by
  cases b with
  | initial | row | firstProbability | firstScoreBase | biasedScore => exact ⟨hWarp, hBase, trivial⟩
  | biasedProbabilityStage | unbiasedScore | statisticsBarrier => exact ⟨hWarp,trivial⟩
  | unbiasedProbability => exact ⟨hWarp,hBase,trivial⟩
  | firstScoreExtra late =>
    have hHold : BiasSegment.firstScoreBase.holding s.pc := by
      rw [hAt]
      cases late <;> decide
    exact ⟨(hFrame.2 .firstScoreBase hHold).1,trivial⟩
  | scaleLoad => trivial
  | scalePack => exact hFrame.2 .scaleLoad (by rw [hAt]; decide)
  | biasedProbability =>
    exact hFrame.2 .biasedProbabilityStage (hAt.symm ▸ (by decide))
  | first =>
    have hRow := hFrame.2 .row (by rw [hAt]; decide)
    exact ⟨hRow.1, hRow.2.1, trivial⟩
  | vector i =>
    have hRow := hFrame.2 .row (by
      rw [hAt]
      change 5046 ≤ 5046 + 4 * i.val ∧ 5046 + 4 * i.val ≤ 5264
      have := i.isLt
      omega)
    exact ⟨hRow.2.2.1, trivial⟩

private def segmentAddressStep (b : BiasSegment) (site : Nat) (seg : SegMatch CuteSlot) : Bool :=
  !decide (b.start < seg.stop ∧ seg.stop < b.stop) &&
    (!decide (b.holding seg.stop) ||
      (decide (b.holding site) &&
        b.registers.all fun r => !(scoreSegmentWrites seg).contains r))

set_option maxRecDepth 100000 in
private theorem segmentAddressAudit {site : Nat} {seg : SegMatch CuteSlot}
    (hSite : site ∈ Assumptions.swExp2Sites) (hMatch : cuteExp2.matchAt kernel site = some seg)
    (b : BiasSegment) : segmentAddressStep b site seg = true := by
  have hAudit : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | none => false
      | some seg => segments.all fun b => segmentAddressStep b site seg) = true := by
    kernel_rfl
  have hAll := List.all_eq_true.mp hAudit site hSite
  rw [hMatch] at hAll
  exact List.all_eq_true.mp hAll b (memSegments b)

private theorem biasAddressStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {w : Fin 8} {s u : TState} {event : Option Event}
    (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3)
    (hWarp : s.regs 1062 = some (b32 w.val)) (hBase : s.regs 2535 = some (b32 l.sharedBase))
    (hScratch : ScoreScratchState s) (hFrame : BiasAddressFrame p l g w s)
    (hStep : WStep kernel Assumptions.all l g s event u) : BiasAddressFrame p l g w u := by
  have checked {ins : Instr} (hc : kernel.code[s.pc]? = some ins) (b : BiasSegment) :=
    List.all_eq_true.mp (Bool.and_eq_true_iff.mp (biasStepCodeAt hLo hHi hc)).2 b (memSegments b)
  have localInSegment {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
      {b : BiasSegment} (hb : b.executing s.pc) : ins.op.isLocal = true := by
    have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (checked hc b)).1).1
    rw [ite_eq_left hb] at h
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  have keepFacts {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
      (keep : ∀ r, r ∉ biasWrites ins.op → u.regs r = s.regs r) {b : BiasSegment}
      (hb : b.holding s.pc) : Holds u.regs (b.outputs p l g w) := by
    have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (checked hc b)).1).2
    rw [ite_eq_left hb] at h
    refine Epilogue.holdsSchedulerFrame (hFrame.2 b hb)
      (fun r hr => keep r (by simpa using List.all_eq_true.mp h r hr)) ?_
    intro pair hPair
    rw [← b.outputRegisters p l g w]
    exact List.mem_map_of_mem hPair
  have starts (b : BiasSegment) : b.start < b.stop := by
    cases b <;> simp [BiasSegment.stop, BiasSegment.start, BiasSegment.length]
  have advance {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
      (keep : ∀ r, r ∉ biasWrites ins.op → u.regs r = s.regs r)
      (hNext : u.pc = s.pc + 1)
      (hLocal : ∀ b : BiasSegment, b.executing s.pc → b.remainder p l g w u) :
      BiasAddressFrame p l g w u := by
    refine ⟨fun b hlo hhi => hLocal b ⟨by omega, by omega⟩, ?_⟩
    intro b hb
    have hBounds : b.stop ≤ u.pc ∧ u.pc ≤ b.last := hb
    by_cases hAt : u.pc = b.stop
    · exact BiasSegment.remainderResult
        (hLocal b ⟨by have := starts b; omega, by omega⟩) hAt
    · exact keepFacts hc keep (show b.holding s.pc from ⟨by omega, by omega⟩)
  have replay {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
      (hf : s.fault = none) (ht : Tau kernel Assumptions.all l g s u)
      (hNext : u.pc = s.pc + 1) (b : BiasSegment) (hb : b.executing s.pc) :
      b.remainder p l g w u := by
    have hBounds : b.start ≤ s.pc ∧ s.pc < b.stop := hb
    apply BiasSegment.remainderStep _ hBounds.2 hNext ht
    rcases Nat.eq_or_lt_of_le hBounds.1 with hEq | hPrev
    · have hAt : s.pc = b.start := hEq.symm
      obtain ⟨hZero, hAcc⟩ := scratchClearOfLocal hc (localInSegment hc hb) hScratch
      obtain ⟨t, hRun, hEnd⟩ := (b.run hp g w).apply
        ⟨hAt, hZero, hAcc, hf, inputAtEntry hAt hFrame hWarp hBase⟩
      exact ⟨t, by simpa only [hAt, BiasSegment.stop, Nat.add_sub_cancel_left] using hRun, hEnd⟩
    · exact hFrame.1 b hPrev hBounds.2
  rcases hStep with ⟨rfl, ht⟩ | ⟨_, rfl, he⟩
  · obtain ⟨ins, hc, hf, hSrc⟩ := tauScoreSource ht
    rcases hSrc with ⟨rfl, _⟩ | ⟨_, _, hRun⟩
    · exact advance hc (fun _ _ => rfl) rfl (replay hc hf ht rfl)
    rcases scoreExecLocal hRun with hLocal | ⟨seg, hSite, hMatch, hExec⟩
    · have hPc := hLocal.pc
      have hKeep : ∀ r, r ∉ biasWrites ins.op → u.regs r = s.regs r :=
        fun r hr => hLocal.regs r (fun hm => hr (List.mem_append_left _ hm))
      cases hOp : ins.op <;> simp only [hOp, nextPc, BrxTarget, or_false] at hPc
      case bra dst uni =>
        constructor
        · intro b hStart hEnd
          have hBranch := (Bool.and_eq_true_iff.mp (checked hc b)).2
          simp only [hOp, Bool.and_eq_true] at hBranch
          exact ((of_decide_eq_true hBranch.1) ⟨hPc ▸ hStart, hPc ▸ hEnd⟩).elim
        · intro b hb
          have hBranch := (Bool.and_eq_true_iff.mp (checked hc b)).2
          simp only [hOp, Bool.and_eq_true] at hBranch
          exact keepFacts hc hKeep ((of_decide_eq_true hBranch.2) (hPc ▸ hb))
      case brx =>
        have hBranch := (Bool.and_eq_true_iff.mp (checked hc .row)).2
        simp [hOp] at hBranch
      all_goals exact advance hc hKeep hPc (replay hc hf ht hPc)
    · obtain ⟨hEnd,_,_,hKeep⟩ := scoreSegmentFrame hExec
      constructor
      · intro b hStart hStop
        have hAudit := (Bool.and_eq_true_iff.mp (segmentAddressAudit hSite hMatch b)).1
        simp only [Bool.not_eq_true',decide_eq_false_iff_not] at hAudit
        exact (hAudit ⟨hEnd ▸ hStart,hEnd ▸ hStop⟩).elim
      · intro b hHold
        have hAudit := (Bool.and_eq_true_iff.mp (segmentAddressAudit hSite hMatch b)).2
        have hb : b.holding seg.stop := hEnd ▸ hHold
        have hBoth : decide (b.holding s.pc) = true ∧
          (b.registers.all fun r => !(scoreSegmentWrites seg).contains r) = true := by
          simpa only [decide_eq_true hb,Bool.not_true,Bool.false_or,Bool.and_eq_true] using hAudit
        refine Epilogue.holdsSchedulerFrame (hFrame.2 b (of_decide_eq_true hBoth.1))
          (fun r hr => hKeep r (by simpa using List.all_eq_true.mp hBoth.2 r hr)) ?_
        intro pair hPair
        rw [← b.outputRegisters p l g w]
        exact List.mem_map_of_mem hPair
  · obtain ⟨ins, hc, hl, _⟩ := estep_event_source he
    have hAudit := (Bool.and_eq_true_iff.mp (biasStepCodeAt hLo hHi hc)).1
    have hOp := (Bool.and_eq_true_iff.mp hAudit).1
    simp only [hl, Bool.false_or] at hOp
    have hNotLocal (b : BiasSegment) (hb : b.executing s.pc) : False := by
      have hLoc := localInSegment hc hb
      rw [hl] at hLoc
      cases hLoc
    have kept r (hr : r ∉ biasWrites ins.op) : u.regs r = s.regs r :=
      (scoreEventStep hc hOp hSub (fun h => hr (List.mem_append_right _ h)) he).2
    have hBaseKeep : 2535 ∉ biasWrites ins.op := by
      simpa using (Bool.and_eq_true_iff.mp hAudit).2
    have hProgress := (scoreEventStep (r := 2535) hc hOp hSub
      (fun hm => hBaseKeep (List.mem_append_right _ hm)) he).1
    rcases hProgress.pc with ⟨hNext, _⟩ | ⟨hSame, _⟩
    · exact advance hc kept hNext (fun b hb => (hNotLocal b hb).elim)
    · refine ⟨fun b hStart hEnd => (hNotLocal b ⟨by omega, by omega⟩).elim, ?_⟩
      intro b hb
      exact keepFacts hc kept (hSame ▸ hb)

private theorem repeatedBiasSwizzle {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (i : Fin 16) :
    kvSwizzle (biasBoxStart l stage (i.val/8) +
      128*((g % l.block) % 128) + 16*(i.val%8)) = biasVectorAddress l g stage i := by
  have hBase : biasBoxStart l stage (i.val/8) % 128 = 0 := by
    have h := hp.shared.1
    unfold biasBoxStart
    omega
  unfold kvSwizzle biasVectorAddress
  rw [Nat.xor_comm]
  exact biasSwizzleWord hBase (Nat.mod_lt i.val (by decide))

private theorem repeatedReadAddressOfRegisters {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {w : Fin 8} {s : TState} (i : Fin 16)
    (hFirst : s.regs 4170 = some (b32 (kvSwizzle (repeatedBiasRowBase l g + 166912) +
      repeatedBiasStageOffset w)))
    (hOther : ∀ j : Fin 14, s.regs (3982+4*j.val) = some (b32 (kvSwizzle
      (repeatedBiasRowBase l g + repeatedBiasStageOffset w + repeatedVectorDisplacement j)))) :
    s.regs (biasReadSite true i).base = some (b32 (biasVectorBase l g (stageOf w) true i)) := by
  let stage := stageOf w
  by_cases hForFirst : i = 0 ∨ i = 8
  · have hReg : (biasReadSite true i).base = 4170 := by
      rcases hForFirst with rfl | rfl <;> rfl
    have hZero : i.val % 8 = 0 := by rcases hForFirst with rfl | rfl <;> rfl
    have hOffset : (biasReadSite true i).offset = 16384*(i.val/8) := by
      rcases hForFirst with rfl | rfl <;> rfl
    let raw := repeatedBiasRowBase l g + 166912
    let words := 32*stage.val+16*(i.val/8)
    have hRaw : biasBoxStart l stage (i.val/8) +
        128*((g % l.block) % 128) + 16*(i.val%8) = raw + 1024*words := by
      rw [hZero]
      dsimp [biasBoxStart,raw,words,repeatedBiasRowBase]
      omega
    have hAddress := repeatedBiasSwizzle hp g stage i
    rw [hRaw,Mma.kvSwizzle_add_period] at hAddress
    have hVec := biasVectorBase_add l g stage true i
    rw [hOffset] at hVec
    have hEq : kvSwizzle raw + repeatedBiasStageOffset w = biasVectorBase l g stage true i := by
      change kvSwizzle raw + 32768*stage.val = _
      dsimp only [words] at hAddress
      omega
    rw [← hEq,hReg]
    exact hFirst
  · have hIndex := (by decide :
        ∀ j : Fin 16, ¬ (j = 0 ∨ j = 8) → ∃ k : Fin 14, repeatedBiasVector k = j) i hForFirst
    obtain ⟨j, rfl⟩ := hIndex
    let i := repeatedBiasVector j
    obtain ⟨hReg, hOffset⟩ := (by decide : ∀ k : Fin 14,
      (biasReadSite true (repeatedBiasVector k)).base = 3982 + 4 * k.val ∧
      (biasReadSite true (repeatedBiasVector k)).offset = 0) j
    have hRaw : repeatedBiasRowBase l g + repeatedBiasStageOffset w +
        repeatedVectorDisplacement j = biasBoxStart l stage (i.val/8) +
        128*((g % l.block) % 128) + 16*(i.val%8) := by
      dsimp only [repeatedBiasRowBase,repeatedBiasStageOffset,repeatedVectorDisplacement,
        biasBoxStart,i,stage]
      omega
    have hAddress := repeatedBiasSwizzle hp g stage i
    rw [← hRaw] at hAddress
    change s.regs (biasReadSite true i).base = some (b32 (biasVectorBase l g stage true i))
    rw [biasVectorBase,hOffset,Nat.sub_zero,← hAddress,hReg]
    exact hOther j

private theorem repeatedReadAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {w : Fin 8} {s : TState} (hFrame : BiasAddressFrame p l g w s) (i : Fin 16)
    (hPc : s.pc = biasReadPc true i) :
    s.regs (biasReadSite true i).base = some (b32 (biasVectorBase l g (stageOf w) true i)) := by
  apply repeatedReadAddressOfRegisters hp
  · exact (hFrame.2 .first (hPc ▸
      (by decide : ∀ k : Fin 16, (BiasSegment.first).holding (biasReadPc true k)) i)).1
  · intro j
    exact (hFrame.2 (.vector j) (hPc ▸ (by decide : ∀ (k : Fin 16) (q : Fin 14),
      (BiasSegment.vector q).holding (biasReadPc true k)) i j)).1

private theorem repeatedBiasWaitResult {l : Launch} {g : Nat} {t : TState} {o : Option TState}
    {obj : Loc} {phase : Nat} {acq : Bool} {scope : MbarScope}
    (hPc : t.pc = 5181)
    (he : EStep kernel Assumptions.all l g t ⟨5181,.wait obj phase true acq scope⟩ o) :
    t.fault = none ∧ o = some (next (setReg t 9755 (.pred true))) := by
  cases o with
  | none =>
    obtain ⟨_,_,hf⟩ := he
    exact (fires_none_notWait hf obj phase true acq scope rfl).elim
  | some u =>
    have hFault : t.fault = none := by
      obtain ⟨tmpl,ho,hFire⟩ := he
      cases hf : t.fault with
      | none => rfl
      | some fault =>
        simp [out,hf] at ho
        subst tmpl
        exact nomatch hFire.2
    obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source he
    have hc := (waitCode 5).1
    change kernel.code[5181]? = _ at hc
    rw [hPc,hc] at hCode
    obtain rfl := Option.some.inj hCode.symm
    obtain ⟨_,_,ok,_,hE,hU⟩ := fires_wait hFire
    have hOk : true = ok := (Kind.wait.inj (congrArg Event.kind hE)).2.2.1
    exact ⟨hFault, by rw [hU,← hOk]; rfl⟩

def repeatedBiasSavedBases (l : Launch) (g : Nat) (w : Fin 8) : List (Nat × Value) :=
  (List.finRange 14).map fun i =>
    (3982+4*i.val,b32 (kvSwizzle (repeatedBiasRowBase l g+
      repeatedBiasStageOffset w+repeatedVectorDisplacement i)))

noncomputable def repeatedBiasFencePack (p : Params) (l : Launch) (g : Nat) (w : Fin 8) :
    List (Nat × Value) :=
  (7896,joinValue (b32 p.invScaleBits) (b32 p.invScaleBits)) :: biasFenceFacts l g w true

/-- Register values ready when the repeated Bias acquire returns. -/
noncomputable def repeatedBiasAcquireFacts (p : Params) (l : Launch) (g : Nat) (w : Fin 8) :
    List (Nat × Value) :=
  repeatedBiasFencePack p l g w ++
    [(3976,b32 (repeatedBiasRowBase l g)),(3977,b32 (repeatedBiasStageOffset w))] ++
    repeatedBiasSavedBases l g w

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (w : Fin 8)
    {g pos j phase : Nat} {seed : TState} {ending : Option TState}
    (hEntry : At seed 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)])
    (hRunEntry : Run kernel Assumptions.all l g seed ((X.tr g).drop pos) ending) (hPos : pos ≤ j)
    {obj : Loc} {acq : Bool} {scope : MbarScope}
    (he : X.get (g,j) = some ⟨5181,.wait obj phase true acq scope⟩)
include hp w hEntry hRunEntry hPos he

/-- Recover the actual Bias wait inputs and the local returning branch. -/
theorem repeatedBiasAcquireBranchFromEntry :
    ∃ pre after,
      pre.pc = 5181 ∧
      EStep kernel Assumptions.all l g pre ⟨5181,.wait obj phase true acq scope⟩
        (some (next (setReg pre 9755 (.pred true)))) ∧
      Run kernel Assumptions.all l g pre ((X.tr g).drop j) ending ∧
      run kernel Assumptions.all l g 1 (next (setReg pre 9755 (.pred true))) = some after ∧
      At after 5184 (repeatedBiasAcquireFacts p l g w) ∧
      after.regs = (setReg pre 9755 (.pred true)).regs ∧
      TraceReach kernel Assumptions.all l g seed (((X.tr g).drop pos).take (j-pos)) pre := by
  have hInit : BiasAddressFrame p l g w seed ∧ BiasLeaderFrame l g seed :=
    ⟨initialFrame hEntry.1,leaderStart hEntry.1⟩
  obtain ⟨t,o,hPc,_,hWarp,hBase,hScratch,⟨hAddr,hLeader⟩,hStep,hRun,hReach⟩ :=
    softmaxRoleEventFromEntryWithScratch hp w hEntry hRunEntry he hPos (show 5181 < 7742 by decide)
      (Q := fun t => BiasAddressFrame p l g w t ∧ BiasLeaderFrame l g t) hInit
      (fun hLo hHi hSub hWarp hBase hScratch hF hStep =>
        ⟨biasAddressStep hp (w := w) hLo hHi hSub hWarp hBase hScratch hF.1 hStep,
          leaderWalkStep hp hLo hHi hSub hF.2 hStep⟩)
  change t.pc = 5181 at hPc
  have hCode := (waitCode 5).1
  change kernel.code[5181]? = _ at hCode
  have hClear : ScoreScratchClear t := by
    simpa only [ScoreScratchState,hPc,hCode,Op.isLocal,ite_false,ScoreScratchReady,
      Bool.false_eq_true] using hScratch
  obtain ⟨hFault,rfl⟩ := repeatedBiasWaitResult hPc hStep
  let facts := repeatedBiasAcquireFacts p l g w
  have hRow := hAddr.2 .row (by rw [hPc]; decide)
  have hScale := (hAddr.2 .scalePack (by rw [hPc]; decide)).1
  have hAt : At t 5181 facts := by
    refine ⟨hPc,hClear.1,hClear.2,hFault,?_⟩
    apply (holds_append _ _ _).mpr
    constructor
    · apply (holds_append _ _ _).mpr
      exact ⟨⟨hScale,hRow.2.2.2.1,hLeader.repeatedPredicate (by omega) (by omega),
        hWarp,hBase,trivial⟩,⟨hRow.1,hRow.2.1,trivial⟩⟩
    · unfold repeatedBiasSavedBases
      have hVector (i : Fin 14) :
          t.regs (3982+4*i.val) = some (b32 (kvSwizzle (repeatedBiasRowBase l g +
            repeatedBiasStageOffset w + repeatedVectorDisplacement i))) := by
        have hi : (BiasSegment.vector i).holding t.pc := by
          rw [hPc]
          exact (by decide : ∀ k : Fin 14, (BiasSegment.vector k).holding 5181) i
        exact (hAddr.2 (.vector i) hi).1
      generalize List.finRange 14 = is
      induction is with
      | nil => trivial
      | cons i is ih => exact ⟨hVector i,ih⟩
  have hFresh : ∀ x ∈ facts, x.1 ≠ 9755 := by
    intro x hx
    simp only [facts,repeatedBiasAcquireFacts,repeatedBiasFencePack,repeatedBiasSavedBases,
      List.mem_append,List.mem_map,List.mem_finRange,
      true_and,biasFenceFacts,biasStageReg,biasKeep,ite_true,List.mem_cons,List.not_mem_nil,
      or_false] at hx
    rcases hx with hSmall | ⟨i,rfl⟩
    · rcases hSmall with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;> norm_num
    · have := i.isLt
      change 3982+4*i.val ≠ 9755
      omega
  have hAfter := hAt.set (v := .pred true) hFresh
  obtain ⟨u,hBranch,hU⟩ := waitBranch (l := l) (g := g) 5 true (hAfter.mono hAfter.2.2.2.2.2)
    hAfter.2.2.2.2.1
  have hBranchRegs : u.regs = (setReg t 9755 (.pred true)).regs := by
    have hAfterPc := hAfter.1
    have hAfterFault := hAfter.2.2.2.1
    have hPred := hAfter.2.2.2.2.1
    have hBranchStep :
        tauStep kernel Assumptions.all l g (next (setReg t 9755 (.pred true))) =
          some {next (setReg t 9755 (.pred true)) with pc := 5184} := by
      have hd := (waitCode 5).2.1
      change kernel.code[5182]? = some ⟨some (9755,false),.bra 5184 true⟩ at hd
      change (next (setReg t 9755 (.pred true))).pc = 5182 at hAfterPc
      rw [Assumptions.tauStep_all_eq_nil (by rw [hAfterPc]; decide)
        (by rw [hAfterPc]; exact hd) rfl]
      simp [tauStep,out,hAfterFault,hAfterPc,hd,guardHolds,Op.isLocal,execLocalA,
        execLocalRule,execLocal,Op.rule,execBranch,readReg,hPred,bind,Except.bind,
        pure,Except.pure]
    change run kernel Assumptions.all l g 1 _ = some u at hBranch
    simp only [run,hBranchStep,Option.bind_some] at hBranch
    cases hBranch
    rfl
  exact ⟨t,u,hPc,hStep,hRun,hBranch,hU,hBranchRegs,hReach⟩

/-- Replay the actual successful repeated Bias poll to its first word, retaining the
packed inverse scale and the trace suffix immediately after that poll. -/
theorem repeatedBiasVectorStartWithPath (hMore : (X.tr g).drop (j+1) ≠ []) :
    ∃ pre t,
      pre.pc = 5181 ∧
      Run kernel Assumptions.all l g pre ((X.tr g).drop j) ending ∧
      (∀ r, 7367 ≤ r → r < 7431 → t.regs r = pre.regs r) ∧
      At t (biasReadPc true 0) (biasFenceFacts l g w true) ∧
      t.regs 7896 = some (joinValue (b32 p.invScaleBits) (b32 p.invScaleBits)) ∧
      (∀ i, t.regs (biasReadSite true i).base =
        some (b32 (biasVectorBase l g (stageOf w) true i))) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (j+1)) ending ∧
      TraceReach kernel Assumptions.all l g seed (((X.tr g).drop pos).take (j-pos)) pre ∧
      Stops kernel Assumptions.all l g pre ∧
      (∀ r ∉ [9755,4166,4167,4168,4169,4170], t.regs r = pre.regs r) ∧
      TraceReach kernel Assumptions.all l g pre (((X.tr g).drop j).take 1) t := by
  obtain ⟨t,u,hPc,hStep,hRun,hBranch,hU,hBranchRegs,hReach⟩ :=
    repeatedBiasAcquireBranchFromEntry hp w hEntry hRunEntry hPos he
  have hStop := stops_of_estep hStep
  let fence := repeatedBiasFencePack p l g w
  have hHead : (X.tr g).drop j =
      ⟨5181,.wait obj phase true acq scope⟩ :: (X.tr g).drop (j+1) := by
    have hLen := len_of_get he
    calc
      _ = (X.tr g)[j] :: (X.tr g).drop (j+1) := List.drop_eq_getElem_cons hLen
      _ = _ := congrArg (fun e => e :: (X.tr g).drop (j+1))
        (Option.some.inj ((List.getElem?_eq_getElem hLen).symm.trans he))
  have hTail := afterSoftmaxEvent hStep (hHead ▸ hRun)
  have hUFacts := (holds_append _ _ _).mp hU.2.2.2.2
  have hFence := ((holds_append _ _ _).mp hUFacts.1).1
  have hRow := ((holds_append _ _ _).mp hUFacts.1).2
  obtain ⟨v,hVector,hV,hFrame⟩ := repeatedBiasFirstVectorSetupFramed hp g w (hU.mono hRow)
  have hVStable (r v') (hm : (r,v') ∈ fence) :
      v.regs r = u.regs r := by
    apply hFrame
    simp only [fence,repeatedBiasFencePack,biasFenceFacts,biasStageReg,biasKeep,ite_true,
      List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hm
    rcases hm with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  have hvFence := Epilogue.holdsSchedulerFrame hFence
    (fun r hr => by
      obtain ⟨⟨rr,vv⟩,hm,heq⟩ := List.mem_map.mp hr
      change rr = r at heq
      subst r
      exact hVStable rr vv hm)
    (fun _ hh => List.mem_map_of_mem hh)
  change Holds v.regs fence at hvFence
  refine ⟨t,v,hPc,hRun,?_,hV.mono hvFence.2,hvFence.1,?_,
    hTail.after_local_nonempty (run_rtg (run_comp hBranch hVector)) hMore,hReach,hStop,?_,?_⟩
  · intro r hLower hUpper
    have hNotWritten : r ∉ [4166,4167,4168,4169,4170] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      omega
    rw [hFrame r hNotWritten,hBranchRegs]
    simp [setReg,show r ≠ 9755 by omega]
  · intro i
    apply repeatedReadAddressOfRegisters hp i hV.2.2.2.2.1
    intro k
    have hk : 3982+4*k.val ∉ [4166,4167,4168,4169,4170] := by
      have := k.isLt
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      omega
    rw [hFrame _ hk]
    exact holds_mem hUFacts.2 (List.mem_map_of_mem (List.mem_finRange k))

  · intro r hNot
    rw [hFrame r (fun h => hNot (List.mem_cons_of_mem _ h)),hBranchRegs]
    have hNe : r ≠ 9755 := fun h => hNot (by simp [h])
    exact Function.update_of_ne hNe _ _
  · rw [hHead]
    exact .event hStep (.of_local (run_rtg (run_comp hBranch hVector)))

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem biasReadFrame (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos : Nat} {vector : Fin 16} {repeated : Bool} {a : Acc} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X (g, pos) repeated vector a bytes) :
    ∃ w t o, w.val = Prologue.warpIndex l g ∧ t.pc = biasReadPc repeated vector ∧
      t.sub ≤ 3 ∧ BiasAddressFrame p l g w t ∧
      EStep kernel Assumptions.all l g t ⟨biasReadPc repeated vector, .rd a bytes⟩ o := by
  have hSite : 3420 ≤ biasReadPc repeated vector ∧ biasReadPc repeated vector < 7742 :=
    (by decide : ∀ (b : Bool) (k : Fin 16), 3420 ≤ biasReadPc b k ∧ biasReadPc b k < 7742)
      repeated vector
  obtain ⟨w, hw, t, o, ht, hSub, hf, he⟩ :=
    softmaxRoleEventWithScratch hp hX hRead hSite.1 hSite.2
      (Q := BiasAddressFrame p l g)
      (fun _ _ ha => initialFrame ha.1)
      (fun w {_ _ _} hLo hHi hSub hWarp hBase hScratch hf hs =>
        biasAddressStep hp (w := w) hLo hHi hSub hWarp hBase hScratch hf hs)
  exact ⟨w, t, o, hw, ht, hSub, hf, he⟩

private def scoreSegment (round : Round) (q : Fin 4) : BiasSegment :=
  match round with
  | .first => if q = 1 then .firstScoreExtra false else if q = 3 then .firstScoreExtra true
      else .firstScoreBase
  | .biased => .biasedScore
  | .unbiased => .unbiasedScore

private theorem scoreSegmentHolds (round : Round) (q : Fin 4) :
    (scoreSegment round q).holding (scorePc round q) := by
  cases round <;> decide +revert

private theorem scoreSegmentMember (p : Params) (l : Launch) (g : Nat) (w : Fin 8)
    (round : Round) (q : Fin 4) :
    (scoreReg round q,b32 (scoreAddress l g (stageOf w) q)) ∈
      (scoreSegment round q).outputs p l g w := by
  cases round
  · fin_cases q <;> simp [scoreSegment,BiasSegment.outputs,scoreReg]
  · exact List.mem_ofFn.mpr ⟨q,rfl⟩
  · exact List.mem_ofFn.mpr ⟨q,rfl⟩

/-- The actual first biased score load has all four stage addresses on
the chosen role-entry trace, before any of its packed score words are written. -/
theorem biasedScoreStartFromEntry (hp : Pre p l m) (w : Fin 8) {g pos j : Nat} {s : TState}
    {ending : Option TState} (hs : At s 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) {address : Nat}
    {values : List Value} {shape : TcShape}
    (he : X.get (g,j) = some ⟨scorePc .biased 0,.tc (.ld address values shape)⟩) (hPos : pos ≤ j) :
    ∃ t o, At t (scorePc .biased 0) [] ∧
      (∀ q : Fin 4, t.regs (scoreReg .biased q) =
        some (b32 (scoreAddress l g (stageOf w) q))) ∧
      EStep kernel Assumptions.all l g t ⟨scorePc .biased 0,.tc (.ld address values shape)⟩ o ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop j) ending ∧
      TraceReach kernel Assumptions.all l g s (((X.tr g).drop pos).take (j-pos)) t := by
  obtain ⟨t,o,ht,_,_,_,hScratch,hFrame,hStep,hRun,hReach⟩ :=
    softmaxRoleEventFromEntryWithScratch hp w hs hr he hPos (show 5112 < 7742 by decide)
      (initialFrame (p := p) (l := l) (g := g) (w := w) hs.1)
      (fun hLo hHi hSub hWarp hBase hScratch hF hStep =>
        biasAddressStep hp (w := w) hLo hHi hSub hWarp hBase hScratch hF hStep)
  change t.pc = scorePc .biased 0 at ht
  have hFault : t.fault = none := by
    obtain ⟨tm,ho,hFire⟩ := hStep
    cases h : t.fault with
    | none => rfl
    | some f =>
      simp only [out,h,Out.ev.injEq] at ho
      subst tm
      cases congrArg Event.kind hFire.1
  obtain ⟨ds,_,hCode⟩ := scoreCode .biased 0
  have hCore : Assumptions.all.any (·.tcLdWait t.pc) = false := by
    rw [ht,scoreWaitHook]
    rfl
  have hClear : ScoreScratchClear t := by
    have hLookup := ht.symm ▸ hCode
    simpa only [ScoreScratchState,hLookup,Op.isLocal,ite_false,ScoreScratchReady,
      ScoreScratchClear,hCore,Bool.false_eq_true,false_or] using hScratch
  have hHeld := hFrame.2 .biasedScore (by rw [ht]; decide)
  exact ⟨t,o,⟨ht,hClear.1,hClear.2,hFault,trivial⟩,
    (fun q => holds_mem hHeld (scoreSegmentMember p l g w .biased q)),hStep,hRun,hReach⟩

/-- The actual first plain score load has the four score addresses and the probability
geometry before any score words are written. -/
theorem unbiasedScoreStartWithProbabilityGeometryFromEntry (hp : Pre p l m) (w : Fin 8)
    {g pos j : Nat} {s : TState} {ending : Option TState}
    (hs : At s 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) {address : Nat}
    {values : List Value} {shape : TcShape}
    (he : X.get (g,j) = some ⟨scorePc .unbiased 0,.tc (.ld address values shape)⟩) (hPos : pos ≤ j)
    :
    ∃ t o, At t (scorePc .unbiased 0) [] ∧
      (∀ q : Fin 4, t.regs (scoreReg .unbiased q) =
        some (b32 (scoreAddress l g (stageOf w) q))) ∧
      EStep kernel Assumptions.all l g t ⟨scorePc .unbiased 0,.tc (.ld address values shape)⟩ o ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop j) ending ∧
      TraceReach kernel Assumptions.all l g s (((X.tr g).drop pos).take (j-pos)) t ∧
      Holds t.regs ((5127,b32 (3+w.val)) :: (5187,b32 (l.sharedBase+8*(stageOf w).val)) ::
        (unbiasedAddressRows l g w).drop 1 ++ unbiasedProbabilityFacts l g (stageOf w)) := by
  obtain ⟨t,o,ht,_,_,_,hScratch,hFrame,hStep,hRun,hReach⟩ :=
    softmaxRoleEventFromEntryWithScratch hp w hs hr he hPos (show 6679 < 7742 by decide)
      (initialFrame (p := p) (l := l) (g := g) (w := w) hs.1)
      (fun hLo hHi hSub hWarp hBase hScratch hF hStep =>
        biasAddressStep hp (w := w) hLo hHi hSub hWarp hBase hScratch hF hStep)
  change t.pc = scorePc .unbiased 0 at ht
  have hFault : t.fault = none := by
    obtain ⟨tm,ho,hFire⟩ := hStep
    cases h : t.fault with
    | none => rfl
    | some f =>
      simp only [out,h,Out.ev.injEq] at ho
      subst tm
      cases congrArg Event.kind hFire.1
  obtain ⟨ds,_,hCode⟩ := scoreCode .unbiased 0
  have hWait : Assumptions.all.any (·.tcLdWait t.pc) = true := by
    rw [ht,scoreWaitHook]
    rfl
  have hClear : ScoreScratchClear t := by
    have hLookup := ht.symm ▸ hCode
    have hAcc : t.acc = [] := by
      simpa only [ScoreScratchState,hLookup,Op.isLocal,ite_false,ScoreScratchReady,
        hWait,true_or,true_and,Bool.false_eq_true,ite_false] using hScratch
    refine ⟨?_,hAcc⟩
    by_contra hSub
    cases o with
    | none =>
      obtain ⟨_,_,hFire⟩ := hStep
      obtain ⟨_,hEnd⟩ | hEnd := fires_none_ends hFire <;> cases hEnd
    | some v =>
      obtain ⟨_,hDecoded,_,hFire⟩ := estep_event_source hStep
      obtain rfl := Option.some.inj (hDecoded.symm.trans hLookup)
      have hEvent := (fires_tcLd_wait hWait hSub hFire).1
      cases Kind.tc.inj (congrArg Event.kind hEvent)
  have hHeld := hFrame.2 .unbiasedScore (by rw [ht]; decide)
  refine ⟨t,o,⟨ht,hClear.1,hClear.2,hFault,trivial⟩,
    (fun q => holds_mem hHeld (scoreSegmentMember p l g w .unbiased q)),hStep,hRun,hReach,?_⟩
  exact ⟨(hFrame.2 .statisticsBarrier (by rw [ht]; decide)).1,
    hFrame.2 .unbiasedProbability (by rw [ht]; decide)⟩

/-- The actual first plain score load has all four stage addresses on
the chosen role-entry trace, before any of its packed score words are written. -/
theorem unbiasedScoreStartFromEntry (hp : Pre p l m) (w : Fin 8) {g pos j : Nat} {s : TState}
    {ending : Option TState} (hs : At s 3103 [(1062,b32 w.val),(2535,b32 l.sharedBase)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) {address : Nat}
    {values : List Value} {shape : TcShape}
    (he : X.get (g,j) = some ⟨scorePc .unbiased 0,.tc (.ld address values shape)⟩) (hPos : pos ≤ j)
    :
    ∃ t o, At t (scorePc .unbiased 0) [] ∧
      (∀ q : Fin 4, t.regs (scoreReg .unbiased q) =
        some (b32 (scoreAddress l g (stageOf w) q))) ∧
      EStep kernel Assumptions.all l g t ⟨scorePc .unbiased 0,.tc (.ld address values shape)⟩ o ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop j) ending ∧
      TraceReach kernel Assumptions.all l g s (((X.tr g).drop pos).take (j-pos)) t := by
  obtain ⟨t,o,ht,hAddr,hEvent,hRun,hReach,_⟩ :=
    unbiasedScoreStartWithProbabilityGeometryFromEntry hp w hs hr he hPos
  exact ⟨t,o,ht,hAddr,hEvent,hRun,hReach⟩

/-- The softmax statistics barrier is fixed by the physical warp and is carried
through every recorded ordinary repeated-body event. -/
theorem statisticsBarrierFromEntry (hp : Pre p l m) (warp : Fin 8) {g entry j : Nat} {s : TState}
    {ending : Option TState} (hs : At s 3103 [(1062,b32 warp.val),(2535,b32 l.sharedBase)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop entry) ending) {e : Event}
    (he : X.get (g,j) = some e) (hBefore : entry ≤ j) (hLo : 3283 ≤ e.pc) (hHi : e.pc ≤ 7604) :
    ∃ t o, EStep kernel Assumptions.all l g t e o ∧
      TraceReach kernel Assumptions.all l g s (((X.tr g).drop entry).take (j-entry)) t ∧
      t.regs 1062 = some (b32 warp.val) ∧ t.regs 2535 = some (b32 l.sharedBase) ∧
      t.regs 5127 = some (b32 (3+warp.val)) := by
  obtain ⟨t,o,hPc,_,hWarp,hBase,_,hGeom,hEvent,_,hPath⟩ :=
    softmaxRoleEventFromEntryWithScratch hp warp hs hr he hBefore (by omega)
      (Q := BiasAddressFrame p l g warp) (initialFrame hs.1)
      (fun hStart hEnd hSub hWarp hBase hScratch hFrame hStep =>
        biasAddressStep hp (w := warp) hStart hEnd hSub hWarp hBase hScratch hFrame hStep)
  have hBar := hGeom.2 .statisticsBarrier (show BiasSegment.statisticsBarrier.holding t.pc by
    change 3283 ≤ t.pc ∧ t.pc ≤ 7604
    omega)
  exact ⟨t,o,hEvent,hPath,hWarp,hBase,hBar.1⟩

/-- Every actual score load uses the issuing lane's row and physical score bank. -/
theorem scoreLoadAddress (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (round : Round) (q : Fin 4) {i : EvId} {address : Nat} {vals : List Value} {shape : TcShape}
    (he : X.get i = some ⟨scorePc round q,.tc (.ld address vals shape)⟩) :
    ∃ w : Fin 8, w.val = Prologue.warpIndex l i.1 ∧
      address = scoreAddress l i.1 (stageOf w) q ∧ vals.length = 32 ∧ shape = .s32x32b := by
  obtain ⟨g,j⟩ := i
  have scoreSites : ∀ (r : Round), ∀ k : Fin 4, 3420 ≤ scorePc r k ∧ scorePc r k < 7742 := by
    intro r
    cases r <;> decide
  have hRange := scoreSites round q
  obtain ⟨w,hw,t,o,ht,_,hFrame,hStep⟩ :=
    softmaxRoleEventWithScratch hp hX he hRange.1 hRange.2
      (Q := BiasAddressFrame p l g)
      (fun _ _ ha => initialFrame ha.1)
      (fun w {_ _ _} hLo hHi hSub hWarp hBase hScratch hf hs =>
        biasAddressStep hp (w := w) hLo hHi hSub hWarp hBase hScratch hf hs)
  have hHeld := hFrame.2 (scoreSegment round q) (ht.symm ▸ scoreSegmentHolds round q)
  have hReg := holds_mem hHeld (scoreSegmentMember p l g w round q)
  have hWidth : scoreAddress l g (stageOf w) q < 2^32 := by
    apply tmem_warp_encoding_lt
    have hScore := scoreColumn_range (stageOf w)
    have hQ := q.isLt
    omega
  cases o with
  | none =>
    obtain ⟨_,_,hFire⟩ := hStep
    obtain ⟨_,hFalse⟩ | hFalse := fires_none_ends hFire <;> cases hFalse
  | some v =>
    obtain ⟨_,hCode,_,hFire⟩ := estep_event_source hStep
    obtain ⟨ds,hLength,hLoadCode⟩ := scoreCode round q
    rw [ht,hLoadCode] at hCode
    obtain rfl := Option.some.inj hCode
    have hVals := fires_tcLd_len (fun _ h => by cases h) hFire rfl
    have core {u : Option TState}
        (hf : Fires t.pc (tcTmpl l g t (.tcLd ds (scoreReg round q) .s32x32b none))
          ⟨scorePc round q,.tc (.ld address vals shape)⟩ u) :
        address = scoreAddress l g (stageOf w) q ∧ shape = .s32x32b := by
      rw [tcTmpl_tcLd_none (by intro sh h; cases h)] at hf
      obtain ⟨_,_,hEq⟩ := fires_tcLd_ofTmpl hReg hWidth rfl hf
      have h := TcKind.ld.inj (Kind.tc.inj (congrArg Event.kind hEq))
      exact ⟨h.1,h.2.2⟩
    refine ⟨w,hw,?_⟩
    rcases eventTmpl_tcLd_cases (A := Assumptions.all) (L := l) (g := g) (t := t)
      (ds := ds) (ta := scoreReg round q) (sh := .s32x32b) with hh | hh | hh <;> rw [hh] at hFire
    · have h := core hFire
      exact ⟨h.1,hVals.trans hLength,h.2⟩
    · obtain ⟨_,hFire⟩ := fires_thenWaitLd hFire
      have h := core hFire
      exact ⟨h.1,hVals.trans hLength,h.2⟩
    · cases congrArg Event.kind hFire.1

private def probabilitySegment : Round → BiasSegment
  | .first => .firstProbability
  | .biased => .biasedProbability
  | .unbiased => .unbiasedProbability

private theorem probabilitySegmentHolds (round : Round) (q : Fin 4) :
    (probabilitySegment round).holding (probabilityPc round q) := by
  cases round <;> fin_cases q <;> decide

/-- Every actual probability tile store uses the issuing lane's row and physical stage. -/
theorem probabilityStoreAddress (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (round : Round) (q : Fin 4) {i : EvId} {address : Nat} {vals : List Value} {shape : TcShape}
    (he : X.get i = some ⟨probabilityPc round q,.tc (.st address vals shape)⟩) :
    ∃ w : Fin 8, w.val = Prologue.warpIndex l i.1 ∧
      address = probabilityAddress l i.1 (stageOf w) q ∧ vals.length = 16 ∧ shape = .s32x32b := by
  obtain ⟨g,j⟩ := i
  have hRange : 3420 ≤ probabilityPc round q ∧ probabilityPc round q < 7742 := by
    cases round <;> fin_cases q <;> decide +revert
  obtain ⟨w,hw,t,o,ht,_,hF,hStep⟩ :=
    softmaxRoleEventWithScratch hp hX he hRange.1 hRange.2
      (Q := BiasAddressFrame p l g)
      (fun _ _ ha => initialFrame ha.1)
      (fun w {_ _ _} hLo hHi hSub hWarp hBase hScratch hf hs =>
        biasAddressStep hp (w := w) hLo hHi hSub hWarp hBase hScratch hf hs)
  let b := probabilitySegment round
  have hHold : b.holding t.pc := by
    have hPc : t.pc = probabilityPc round q := ht
    rw [hPc]
    exact probabilitySegmentHolds round q
  have hRegs := hF.2 b hHold
  have hReg : t.regs (probabilityReg round q) =
      some (b32 (probabilityAddress l g (stageOf w) q)) := by
    apply holds_mem hRegs
    cases round <;> fin_cases q <;>
      simp [b,probabilitySegment,BiasSegment.outputs,firstAddressFacts,biasedAddressFacts,
        unbiasedProbabilityFacts,
        probabilityReg]
  have hCol : probabilityColumn (stageOf w)+16*q.val < 512 := by
    have hProb := probabilityColumn_range (stageOf w)
    have hScore := scoreColumn_range (stageOf w)
    have hQ := q.isLt
    omega
  have hAddress : probabilityAddress l g (stageOf w) q < 2^32 :=
    tmem_warp_encoding_lt l g hCol
  cases o with
  | none =>
    obtain ⟨_,_,hFire⟩ := hStep
    obtain ⟨_,hFalse⟩ | hFalse := fires_none_ends hFire <;> cases hFalse
  | some v =>
    obtain ⟨ins,hCode,_,hFire⟩ := estep_event_source hStep
    obtain ⟨ss,hLength,hStoreCode⟩ := probabilityCode round q
    have hPc : t.pc = probabilityPc round q := ht
    rw [hPc,hStoreCode] at hCode
    obtain rfl := Option.some.inj hCode
    have hVals := fires_tcSt_len (fun _ h => by cases h) hFire rfl
    obtain ⟨u,hUReg,hUFire⟩ := fires_tcSt_core hFire rfl (by intro h; cases h)
    rw [← eventTmpl_tcSt_noWait (A := []) (by rfl)] at hUFire
    have hU := hUReg.symm ▸ hReg
    obtain ⟨⟨words,hE⟩,_⟩ := fires_tcSt hU hAddress hUFire
    have hComponents := TcKind.st.inj (Kind.tc.inj (congrArg Event.kind hE))
    exact ⟨w,hw,hComponents.1,hVals.trans hLength,hComponents.2.2⟩

/-- Every actual Bias vector element reads its physical stage, row and word. -/
theorem biasVectorReadAccess (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {vector : Fin 16} {repeated : Bool} {a : Acc} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X i repeated vector a bytes) :
    ∃ w : Fin 8, ∃ sub : Fin 4, w.val = Prologue.warpIndex l i.1 ∧
      (stageOf w).val = Prologue.warpIndex l i.1/4 ∧
      a = biasReadAcc l i.1 (biasVectorBase l i.1 (stageOf w) repeated vector)
        repeated vector sub.val := by
  obtain ⟨g,pos⟩ := i
  obtain ⟨w,t,o,hw,ht,hSub,hFrame,he⟩ := biasReadFrame hp hX hRead
  let stage := stageOf w
  let base := biasVectorBase l g stage repeated vector
  have hReg : t.regs (biasReadSite repeated vector).base = some (b32 base) := by
    cases repeated
    · have hHold : (BiasSegment.initial).holding t.pc := by
        rw [ht]
        exact (by decide : ∀ i : Fin 16, (BiasSegment.initial).holding (biasReadPc false i)) vector
      exact holds_mem (hFrame.2 .initial hHold) (List.mem_map_of_mem (List.mem_finRange vector))
    · exact repeatedReadAddress hp hFrame vector ht
  have hPc := (biasVectorAddressBounds hp g stage vector)
  have hAddr := biasVectorBase_add l g stage repeated vector
  have hEq := biasReadAccessAtRegister repeated vector ht hReg (hAddr ▸ hPc.1) (hAddr ▸ hPc.2) he
  have hStage : stage.val = Prologue.warpIndex l g/4 := by
    rw [← hw]
    fin_cases w <;> rfl
  exact ⟨w,⟨t.sub,by omega⟩,hw,hStage,hEq⟩

/-- Every actual Bias word uses a shared address in the Bias storage. -/
theorem biasVectorReadRange (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {vector : Fin 16} {repeated : Bool} {a : Acc} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X i repeated vector a bytes) :
    l.sharedBase + 166912 ≤ a.loc.addr ∧ a.size = 4 ∧
      a.loc.addr + a.size ≤ l.sharedBase + 232448 := by
  obtain ⟨w,sub,_,_,rfl⟩ := biasVectorReadAccess hp hX hRead
  have hLo := biasVectorAddressLower l i.1 (stageOf w) vector
  have hHi := biasVectorAddressEnd l i.1 (stageOf w) vector
  have hSub := sub.isLt
  change l.sharedBase + 166912 ≤
      biasVectorBase l i.1 (stageOf w) repeated vector + (biasReadSite repeated vector).offset +
        4*sub.val ∧ 4 = 4 ∧
    biasVectorBase l i.1 (stageOf w) repeated vector + (biasReadSite repeated vector).offset +
      4*sub.val + 4 ≤ l.sharedBase + 232448
  rw [biasVectorBase_add]
  omega

theorem biasVectorReadLower (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {vector : Fin 16} {repeated : Bool} {a : Acc} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X i repeated vector a bytes) :
    l.sharedBase + 166912 ≤ a.loc.addr ∧ a.size = 4 :=
  let h := biasVectorReadRange hp hX hRead
  ⟨h.1, h.2.1⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
