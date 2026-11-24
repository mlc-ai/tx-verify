-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSignals
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedAddress

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasVector
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder
import Lemmas.Step.Object
import Lemmas.Kernel.ProgressDescent
import Lemmas.Snoc.SnocAsyncSilent
import Lemmas.Snoc.SnocObjectMemory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

def biasFencePc (repeated : Bool) : Nat := if repeated then 5269 else 3581

def biasStageReg (repeated : Bool) : Nat := if repeated then 631 else 481

def biasBarReg (repeated : Bool) : Nat := if repeated then 4235 else 3075

def biasKeep (l : Launch) (g : Nat) (warp : Fin 8) (repeated : Bool) :
    List (Nat × Value) :=
  [(if repeated then 632 else 482, .pred (laneOf l g ≠ 0)),
    (1062, b32 warp.val), (2535, b32 l.sharedBase)]

def biasFenceFacts (l : Launch) (g : Nat) (warp : Fin 8) (repeated : Bool) :
    List (Nat × Value) :=
  (biasStageReg repeated, .pred ((stageOf warp).val = 1)) :: biasKeep l g warp repeated

private def biasProxy : ProxyFence := .async (some (.shared .cta))

private theorem biasFenceCode (repeated : Bool) : kernel.code[biasFencePc repeated]? =
    some ⟨none, .fence (.proxy biasProxy none none)⟩ := by
  cases repeated
  · exact Flow.code_3581
  · exact Flow.code_5269

private theorem biasBarCode (repeated : Bool) : kernel.code[biasFencePc repeated + 2]? =
    some ⟨none, .barSyncN (.reg (biasBarReg repeated)) (.imm 128) true⟩ := by
  cases repeated
  · exact Flow.code_3583
  · exact Flow.code_5271

theorem biasBarSetup (l : Launch) (g : Nat) (warp : Fin 8) (repeated : Bool) :
    Seg kernel Assumptions.all l g 1 (biasFencePc repeated + 1) (biasFenceFacts l g warp repeated)
      (biasFencePc repeated + 2)
      ((biasBarReg repeated, b32 (11 + (stageOf warp).val)) :: biasKeep l g warp repeated) := by
  have hStage : (stageOf warp).val = 0 ∨ (stageOf warp).val = 1 := by
    have := (stageOf warp).isLt
    omega
  cases repeated <;> rcases hStage with h | h <;> intro t ht <;>
    simp only [biasFencePc, biasFenceFacts, biasKeep, biasStageReg, biasBarReg, h] at ht ⊢ <;>
    seg_fp ht using (simp [b32]; decide)

private theorem singleCoreRegs {l : Launch} {g r : Nat} {t u : TState} {ins : Instr}
    (hc : kernel.code[t.pc]? = some ins) (hRun : run kernel [] l g 1 t = some u)
    (hKeep : r ∉ writesRegs ins.op) : u.regs r = t.regs r := by
  have ht : tauStep kernel [] l g t = some u := by
    cases hs : tauStep kernel [] l g t <;> simp_all only [run, Option.bind_none,
      Option.bind_some, Option.some.injEq, reduceCtorEq]
  exact tau_core_regs hc (tauStep_iff.mp ht) hKeep

theorem biasBarSetupFrame {l : Launch} {g : Nat} {t u : TState}
    (repeated : Bool) (hPc : t.pc = biasFencePc repeated + 1)
    (hRun : run kernel Assumptions.all l g 1 t = some u) :
    ∀ r, r ≠ biasBarReg repeated → u.regs r = t.regs r := by
  have hCode : ∃ ins, kernel.code[t.pc]? = some ins ∧
      Assumptions.coreOp ins.op = true ∧ writesRegs ins.op = [biasBarReg repeated] := by
    rw [hPc]
    cases repeated
    · exact ⟨_, Flow.code_3582, rfl, rfl⟩
    · exact ⟨_, Flow.code_5270, rfl, rfl⟩
  obtain ⟨ins, hc, hCore, hWrites⟩ := hCode
  have heq := Assumptions.tauStep_all_eq_nil (L := l) (g := g)
    (by rw [hPc]; cases repeated <;> decide) hc hCore
  have hRun' : run kernel [] l g 1 t = some u := by
    simpa only [run, heq] using hRun
  intro r hKeep
  exact singleCoreRegs hc hRun' (by simpa [hWrites] using hKeep)

theorem biasFenceTemplate {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (repeated : Bool) (ht : At t (biasFencePc repeated) F) :
    out kernel Assumptions.all l g t =
      .ev (.fenceProxy (.async (some (.shared .cta))) none (next t)) := by
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact biasFenceCode repeated) rfl rfl]
  rfl

theorem biasBarTemplate {l : Launch} {g : Nat} {t : TState} (hBlock : l.block = 512)
    (warp : Fin 8) (repeated : Bool)
    (ht : At t (biasFencePc repeated+2)
      ((biasBarReg repeated,b32 (11+(stageOf warp).val)) :: biasKeep l g warp repeated)) :
    out kernel Assumptions.all l g t =
      .ev (.bar (11+(stageOf warp).val) (next t) (some 128) .sync) := by
  let id := 11 + (stageOf warp).val
  have hId : id < 16 := by have := (stageOf warp).isLt; unfold id; omega
  have hId32 : id < 2 ^ 32 := by omega
  have hId64 : id < 18446744073709551616 := by omega
  have hImm : readBits l g t 32 (.imm 128) = .ok 128#64 := rfl
  have hReg := ht.2.2.2.2.1
  rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact biasBarCode repeated) rfl rfl]
  change Out.ev (barTmpl l g t (.reg (biasBarReg repeated)) (some (.imm 128)) .sync) = _
  have hRead : readBits l g t 32 (.reg (biasBarReg repeated)) = .ok (BitVec.ofNat 64 id) :=
    readBits_b32 hReg hId32
  simp [barTmpl, hRead, hImm, hBlock, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hId64, Nat.not_le_of_lt hId]
  rfl

private theorem biasRendezvousReplay {l : Launch} {X : Execution} (hBlock : l.block = 512)
    (warp : Fin 8) (repeated : Bool) {g j : Nat} {t : TState}
    {ending : Option TState}
    (ht : At t (biasFencePc repeated) (biasFenceFacts l g warp repeated))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    {cursor : Nat → Prop} (hCursor : cursor j)
    (hPresent : ∀ k, cursor k → ending = none ∨ k < (X.tr g).length)
    (hAdvance : ∀ k e, X.get (g,k) = some e →
      (∀ a bytes, e.kind ≠ .wr a bytes) → cursor k → cursor (k+1)) :
    ∃ u, X.get (g, j) = some
        ⟨biasFencePc repeated, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, j + 1) = some
        ⟨biasFencePc repeated + 2, .bar (11 + (stageOf warp).val) (some 128) .sync⟩ ∧
      At u (biasFencePc repeated + 3) (biasKeep l g warp repeated) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 2)) ending ∧
      (∀ r, r ≠ biasBarReg repeated → u.regs r = t.regs r) ∧ cursor (j+2) ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 2) u := by
  have present (k : Nat) (hCursor : cursor k) {s : TState}
      (hr : Run kernel Assumptions.all l g s ((X.tr g).drop k) ending) :
      (X.tr g).drop k ≠ [] := by
    intro hEmpty
    rw [hEmpty] at hr
    cases hr
    have hBound := List.drop_eq_nil_iff.mp hEmpty
    exact (hPresent k hCursor).elim (by simp) (Nat.not_lt_of_ge hBound)
  have hOut := biasFenceTemplate (l := l) (g := g) repeated ht
  have hn : Next kernel Assumptions.all l g t t (.fenceProxy biasProxy none (next t)) :=
    ⟨.refl, hOut⟩
  obtain ⟨e,s,he,hFire,hTail⟩ := hn.continuing_at_nonempty (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hRun (present j hCursor hRun)
  have hFenceStep : EStep kernel Assumptions.all l g t e (some s) := ⟨_,hOut,hFire⟩
  obtain ⟨rfl,hS⟩ := hFire
  obtain rfl := Option.some.inj hS
  have hC1 := hAdvance j _ he (by intro a bytes h; cases h) hCursor
  obtain ⟨v, hLocal, hV⟩ := (biasBarSetup l g warp repeated).apply ht.next
  let id := 11 + (stageOf warp).val
  have ho := biasBarTemplate hBlock warp repeated hV
  have hBar : Next kernel Assumptions.all l g (next t) v (.bar id (next v) (some 128) .sync) :=
    ⟨run_rtg hLocal, ho⟩
  obtain ⟨f,u,hf,hBarFire,hRest⟩ := hBar.continuing_at_nonempty (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hTail (present (j+1) hC1 hTail)
  have hBarStep : EStep kernel Assumptions.all l g v f (some u) := ⟨_,ho,hBarFire⟩
  obtain ⟨rfl,hU⟩ := hBarFire
  obtain rfl := Option.some.inj hU
  refine ⟨_, by simpa only [ht.1, biasProxy] using he, by simpa only [hV.1] using hf,
    hV.next.mono hV.2.2.2.2.2, hRest, ?_,
    hAdvance (j+1) _ hf (by intro a bytes h; cases h) hC1,?_⟩
  · exact biasBarSetupFrame (t := next t) (u := v) repeated ht.next.1 hLocal
  · change (X.tr g)[j]? = some _ at he
    change (X.tr g)[j+1]? = some _ at hf
    simp only [List.take_add_one,List.getElem?_drop,Nat.add_zero,he,hf,
      List.take_zero,Option.toList,List.nil_append,List.cons_append]
    have hPath := (TraceReach.of_local (run_rtg hLocal)).append
      (TraceReach.event hBarStep (.refl _))
    exact .event hFenceStep (by simpa only [List.nil_append] using hPath)

/-- The opening stage's simultaneous and counted Bias rendezvous event. -/
def FirstBiasArrival (X : Execution) (g index : Nat) (stage : Fin 2) : Prop :=
  X.get (g,index) = some ⟨biasFencePc false+2,.bar (11+stage.val) (some 128) .sync⟩

def biasReleaseSite (repeated : Bool) : Fin 8 := if repeated then 3 else 0

private def biasSkipReg (repeated : Bool) : Nat := if repeated then 632 else 482

def biasJoinFacts (l : Launch) (warp : Fin 8) : List (Nat × Value) :=
  [(1062, b32 warp.val), (2535, b32 l.sharedBase)]

private theorem biasReleaseBranch (repeated : Bool) :
    kernel.code[biasFencePc repeated + 3]? =
      some ⟨some (biasSkipReg repeated, false),
        .bra ((signalSite (biasReleaseSite repeated)).pc + 1) false⟩ := by
  cases repeated
  · exact Flow.code_3584
  · exact Flow.code_5272

theorem biasReleaseSetup {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (warp : Fin 8) (repeated : Bool) :
    let s := signalSite (biasReleaseSite repeated)
    Seg kernel Assumptions.all l g 5 (biasFencePc repeated + 4) (biasJoinFacts l warp)
      s.pc ([(s.base, b32 (l.sharedBase + 8 * (stageOf warp).val)), (s.count, b32 1)] ++
        biasJoinFacts l warp) := by
  have hShared := hp.shared.2.1
  have hBase : l.sharedBase < 2 ^ 32 := by omega
  have hBase8 : l.sharedBase + 8 < 2 ^ 32 := by omega
  dsimp only
  cases repeated <;> fin_cases warp <;> intro t ht <;>
    simp only [biasJoinFacts, biasFencePc, signalSite, biasReleaseSite, List.cons_append,
      List.nil_append] at ht ⊢ <;>
    seg_fp ht using
      first
      | (change Value.bits 32
          (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase) + 0#64)) =
            Value.bits 32 (BitVec.ofNat 64 l.sharedBase)
         rw [BitVec.add_zero, truncBits_ofNat hBase (by decide), truncBits_ofNat hBase (by decide)])
      | (change Value.bits 32
          (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase) + BitVec.ofNat 64 8)) =
            Value.bits 32 (BitVec.ofNat 64 (l.sharedBase + 8))
         rw [truncBits_ofNat hBase (by decide), ← BitVec.ofNat_add,
           truncBits_ofNat hBase8 (by decide)])
      | decide

def biasReleaseSetupRegs : Bool → List Nat
  | false => [492, 1046, 3076, 3077, 3078]
  | true => [633, 1051, 4236, 4237, 4238]

private theorem biasReleaseSetupCode (repeated : Bool) (i : Fin 5) :
    let pc := biasFencePc repeated + 4 + i.val
    ∃ ins, kernel.code[pc]? = some ins ∧ Assumptions.coreOp ins.op = true ∧
      nextPc ins.op pc = pc + 1 ∧ (∀ target, ¬ BrxTarget ins.op target) ∧
      (writesRegs ins.op).all (biasReleaseSetupRegs repeated).contains = true := by
  cases repeated <;> fin_cases i
  · exact ⟨_, Flow.code_3585, rfl, rfl, fun _ => nofun, rfl⟩
  · exact ⟨_, Flow.code_3586, rfl, rfl, fun _ => nofun, rfl⟩
  · exact ⟨_, Flow.code_3587, rfl, rfl, fun _ => nofun, rfl⟩
  · exact ⟨_, Flow.code_3588, rfl, rfl, fun _ => nofun, rfl⟩
  · exact ⟨_, Flow.code_3589, rfl, rfl, fun _ => nofun, rfl⟩
  · exact ⟨_, Flow.code_5273, rfl, rfl, fun _ => nofun, rfl⟩
  · exact ⟨_, Flow.code_5274, rfl, rfl, fun _ => nofun, rfl⟩
  · exact ⟨_, Flow.code_5275, rfl, rfl, fun _ => nofun, rfl⟩
  · exact ⟨_, Flow.code_5276, rfl, rfl, fun _ => nofun, rfl⟩
  · exact ⟨_, Flow.code_5277, rfl, rfl, fun _ => nofun, rfl⟩

theorem biasReleaseSetupFrame {l : Launch} {g : Nat} {t u : TState} (repeated : Bool)
    (hPc : t.pc = biasFencePc repeated + 4)
    (hRun : run kernel Assumptions.all l g 5 t = some u) :
    ∀ r ∉ biasReleaseSetupRegs repeated, u.regs r = t.regs r := by
  let first := biasFencePc repeated + 4
  apply fixedFrame (first := first) (stop := first + 5) _ _ hPc.ge (by simp [first, hPc]) hRun
  · intro pc hLo hHi
    let i : Fin 5 := ⟨pc - first, by omega⟩
    have hIndex : first + i.val = pc := by dsimp [i]; omega
    obtain ⟨ins, hc, hCore, hNext, hNoBrx, hWrites⟩ := biasReleaseSetupCode repeated i
    change kernel.code[first + i.val]? = some ins at hc
    change nextPc ins.op (first + i.val) = first + i.val + 1 at hNext
    rw [hIndex] at hc hNext
    refine ⟨ins, hc, hCore, hNext, hNoBrx, ?_⟩
    intro r hKeep hWritten
    exact hKeep (by simpa using List.all_eq_true.mp hWrites r hWritten)
  · intro pc hLo hHi
    cases repeated <;> simp only [first, biasFencePc, Bool.false_eq_true, ite_false, ite_true,
      Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at * <;> omega

def biasReleaseWritten (repeated : Bool) : List Nat :=
  (signalSite (biasReleaseSite repeated)).state :: biasReleaseSetupRegs repeated

/-- The branch after the Bias rendezvous selects lane zero for the release. -/
theorem biasReleaseBranchFrame {l : Launch} {g : Nat} {t : TState}
    (warp : Fin 8) (repeated : Bool)
    (ht : At t (biasFencePc repeated+3) (biasKeep l g warp repeated)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u (if laneOf l g = 0 then biasFencePc repeated+4
        else (signalSite (biasReleaseSite repeated)).pc+1) (biasJoinFacts l warp) ∧
      ∀ r, u.regs r = t.regs r := by
  obtain ⟨u,hu,hU⟩ := run_bra (A := []) (K := kernel) (L := l) (g := g)
    (biasReleaseBranch repeated) (decide (laneOf l g ≠ 0)) (ht.mono ht.2.2.2.2.2)
    ht.2.2.2.2.1 (by simp)
  have hTau : tauStep kernel Assumptions.all l g t = tauStep kernel [] l g t := by
    apply Assumptions.tauStep_all_eq_nil (by rw [ht.1]; cases repeated <;> decide)
      (by rw [ht.1]; exact biasReleaseBranch repeated) rfl
  have hu' : run kernel Assumptions.all l g 1 t = some u := by
    simpa only [run,hTau] using hu
  refine ⟨u,hu',?_,fun r => ?_⟩
  · by_cases hLane : laneOf l g = 0
    · simpa [biasJoinFacts,hLane,Nat.add_assoc] using hU
    · simpa only [biasJoinFacts,decide_eq_true_eq,ite_eq_right hLane,ite_eq_left hLane] using hU
  · exact singleCoreRegs (ht.1.symm ▸ biasReleaseBranch repeated) hu (by simp [writesRegs])

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (warp : Fin 8)
    (repeated : Bool) {g j : Nat} {t : TState}
include hp warp repeated

private theorem biasReleaseReplay {ending : Option TState}
    (ht : At t (biasFencePc repeated + 3) (biasKeep l g warp repeated))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending) {cursor : Nat → Prop}
    (hCursor : cursor j) (hPresent : ∀ k, cursor k → ending = none ∨ k < (X.tr g).length)
    (hAdvance : ∀ k e, X.get (g,k) = some e →
      (∀ a bytes, e.kind ≠ .wr a bytes) → cursor k → cursor (k+1)) :
    let i := biasReleaseSite repeated
    ∃ u, (laneOf l g = 0 → X.get (g, j) = some
        ⟨(signalSite i).pc, .arrive (signalLoc l g (stageOf warp) i) 0 1 true .cta⟩) ∧
      At u ((signalSite i).pc + 1) (biasJoinFacts l warp) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (if laneOf l g = 0 then j + 1 else j))
        ending ∧
      (∀ r ∉ biasReleaseWritten repeated, u.regs r = t.regs r) ∧
      cursor (if laneOf l g = 0 then j+1 else j) ∧
      TraceReach kernel Assumptions.all l g t
        (((X.tr g).drop j).take (if laneOf l g = 0 then 1 else 0)) u := by
  dsimp only
  let i := biasReleaseSite repeated
  obtain ⟨u,hu',hU,hFrame⟩ := biasReleaseBranchFrame warp repeated ht
  have hMore : (X.tr g).drop j ≠ [] := by
    intro hEmpty
    rw [hEmpty] at hRun
    cases hRun
    have hLength := List.drop_eq_nil_iff.mp hEmpty
    exact (hPresent j hCursor).elim (by simp) (Nat.not_lt_of_ge hLength)
  have hTail := hRun.after_local_nonempty (run_rtg hu') hMore
  by_cases hLane : laneOf l g = 0
  · have hU' : At u (biasFencePc repeated + 4) (biasJoinFacts l warp) := by
      simpa only [ite_eq_left hLane] using hU
    obtain ⟨v, hLocal, hV⟩ := (biasReleaseSetup hp g warp repeated).apply hU'
    obtain ⟨hSignal, hAfter⟩ := signalTraceInPrefix hp (stageOf warp) i hV.1 hV.2.2.2.1
      hV.2.2.2.2.1 hV.2.2.2.2.2.1 (hTail.after_local_nonempty (run_rtg hLocal) hMore)
      (by simpa only [ne_eq,List.drop_eq_nil_iff,not_le] using hMore)
    let w := next (mbarStateDest v (some (signalSite i).state))
    have hKeep := hV.2.2.2.2.2.2
    have hNotWarp : (signalSite i).state ≠ 1062 := by cases repeated <;> decide
    have hNotBase : (signalSite i).state ≠ 2535 := by cases repeated <;> decide
    refine ⟨w, fun _ => hSignal, ⟨congrArg (· + 1) hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1,
      ?_⟩,?_,?_,?_,?_⟩
    · exact ⟨by simpa [w, mbarStateDest, next, Function.update_of_ne hNotWarp.symm] using hKeep.1,
        by simpa [w, mbarStateDest, next, Function.update_of_ne hNotBase.symm] using hKeep.2.1,
        trivial⟩
    · simpa only [ite_eq_left hLane] using hAfter
    · intro r hKeep
      have hr : r ≠ (signalSite i).state := by
        intro he
        exact hKeep (he ▸ List.mem_cons_self)
      have hScratch : r ∉ biasReleaseSetupRegs repeated :=
        fun hw => hKeep (List.mem_cons_of_mem _ hw)
      have hx := biasReleaseSetupFrame repeated hU'.1 hLocal r hScratch
      simpa only [w, next, mbarStateDest, Function.update_of_ne hr] using (hx.trans (hFrame r))
    · simpa only [ite_eq_left hLane] using
        hAdvance j _ hSignal (by intro a bytes h; cases h) hCursor
    · let e : Event := ⟨(signalSite i).pc,.arrive (signalLoc l g (stageOf warp) i) 0 1 true .cta⟩
      have hSignal' : (X.tr g)[j]? = some e := hSignal
      have hStep : EStep kernel Assumptions.all l g v e (some w) := by
        refine ⟨_,signalTemplate hp (stageOf warp) i hV.1 hV.2.2.2.1
          hV.2.2.2.2.1 hV.2.2.2.2.2.1,?_⟩
        exact ⟨by simp only [e,hV.1,i],rfl⟩
      simp only [hLane,ite_true,List.take_add_one,List.take_zero,List.getElem?_drop,
        Nat.add_zero,hSignal',Option.toList,List.nil_append]
      simpa only [List.nil_append] using
        (TraceReach.of_local ((run_rtg hu').trans (run_rtg hLocal))).append
          (.event hStep (.refl _))
  · exact ⟨u, fun h => (hLane h).elim,
      by simpa only [ite_eq_right hLane] using hU,
      by simpa only [ite_eq_right hLane] using hTail,fun r _ => hFrame r,
      by simpa only [ite_eq_right hLane] using hCursor,
      by simpa only [hLane,ite_false,List.take_zero] using TraceReach.of_local (run_rtg hu')⟩

omit hp warp repeated in
/-- Register destinations of the Bias rendezvous and the optional lane-zero release. -/
def biasFenceWritten (repeated : Bool) : List Nat :=
  biasBarReg repeated :: biasReleaseWritten repeated

/-- The actual Bias events preserve all registers except the audited barrier setup destinations. -/
theorem biasFinishTraceWithPathGuarded {ending : Option TState}
    (ht : At t (biasFencePc repeated) (biasFenceFacts l g warp repeated))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending) {cursor : Nat → Prop}
    (hCursor : cursor j) (hPresent : ∀ k, cursor k → ending = none ∨ k < (X.tr g).length)
    (hAdvance : ∀ k e, X.get (g,k) = some e →
      (∀ a bytes, e.kind ≠ .wr a bytes) → cursor k → cursor (k+1)) :
    let i := biasReleaseSite repeated
    ∃ u, X.get (g, j) = some
        ⟨biasFencePc repeated, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, j + 1) = some
        ⟨biasFencePc repeated + 2, .bar (11 + (stageOf warp).val) (some 128) .sync⟩ ∧
      (laneOf l g = 0 → X.get (g, j + 2) = some
        ⟨(signalSite i).pc, .arrive (signalLoc l g (stageOf warp) i) 0 1 true .cta⟩) ∧
      At u ((signalSite i).pc + 1) (biasJoinFacts l warp) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (if laneOf l g = 0 then j + 3 else j + 2))
        ending ∧
      (∀ r ∉ biasFenceWritten repeated, u.regs r = t.regs r) ∧
      cursor (if laneOf l g = 0 then j+3 else j+2) ∧
      TraceReach kernel Assumptions.all l g t
        (((X.tr g).drop j).take (if laneOf l g = 0 then 3 else 2)) u := by
  obtain ⟨u,hFence,hBar,hU,hTail,hKeeps,hC,hFirst⟩ :=
    biasRendezvousReplay hp.block warp repeated ht hRun hCursor hPresent hAdvance
  obtain ⟨v,hRelease,hV,hRest,hFrame,hEnd,hSecond⟩ :=
    biasReleaseReplay hp warp repeated hU hTail hC hPresent hAdvance
  refine ⟨v,hFence,hBar,hRelease,hV,hRest,?_,?_,?_⟩
  · intro r hKeep
    exact (hFrame r (fun h => hKeep (List.mem_cons_of_mem _ h))).trans
      (hKeeps r (fun h => hKeep (h ▸ List.mem_cons_self)))
  · simpa only [Nat.add_assoc] using hEnd

  · have hList : (if laneOf l g = 0 then 3 else 2 : Nat) =
        2+(if laneOf l g = 0 then 1 else 0) := by split <;> rfl
    rw [hList,List.take_add,List.drop_drop]
    exact hFirst.append hSecond

theorem biasFinishTraceFramedGuarded {ending : Option TState}
    (ht : At t (biasFencePc repeated) (biasFenceFacts l g warp repeated))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending) {cursor : Nat → Prop}
    (hCursor : cursor j) (hPresent : ∀ k, cursor k → ending = none ∨ k < (X.tr g).length)
    (hAdvance : ∀ k e, X.get (g,k) = some e →
      (∀ a bytes, e.kind ≠ .wr a bytes) → cursor k → cursor (k+1)) :
    let i := biasReleaseSite repeated
    ∃ u, X.get (g, j) = some
        ⟨biasFencePc repeated, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, j + 1) = some
        ⟨biasFencePc repeated + 2, .bar (11 + (stageOf warp).val) (some 128) .sync⟩ ∧
      (laneOf l g = 0 → X.get (g, j + 2) = some
        ⟨(signalSite i).pc, .arrive (signalLoc l g (stageOf warp) i) 0 1 true .cta⟩) ∧
      At u ((signalSite i).pc + 1) (biasJoinFacts l warp) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (if laneOf l g = 0 then j + 3 else j + 2))
        ending ∧
      (∀ r ∉ biasFenceWritten repeated, u.regs r = t.regs r) ∧
      cursor (if laneOf l g = 0 then j+3 else j+2) := by
  obtain ⟨u,hFence,hBar,hRelease,hV,hRest,hKeep,hEnd,_⟩ :=
    biasFinishTraceWithPathGuarded hp warp repeated ht hRun hCursor hPresent hAdvance
  exact ⟨u,hFence,hBar,hRelease,hV,hRest,hKeep,hEnd⟩

theorem biasFinishTraceFramed (ht : At t (biasFencePc repeated) (biasFenceFacts l g warp repeated))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let i := biasReleaseSite repeated
    ∃ u, X.get (g, j) = some
        ⟨biasFencePc repeated, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, j + 1) = some
        ⟨biasFencePc repeated + 2, .bar (11 + (stageOf warp).val) (some 128) .sync⟩ ∧
      (laneOf l g = 0 → X.get (g, j + 2) = some
        ⟨(signalSite i).pc, .arrive (signalLoc l g (stageOf warp) i) 0 1 true .cta⟩) ∧
      At u ((signalSite i).pc + 1) (biasJoinFacts l warp) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (if laneOf l g = 0 then j + 3 else j + 2))
        none ∧
      ∀ r ∉ biasFenceWritten repeated, u.regs r = t.regs r := by
  obtain ⟨u,hFence,hBar,hRelease,hu,hTail,hFrame,_⟩ := biasFinishTraceFramedGuarded
    hp warp repeated ht hRun (cursor := fun _ => True) trivial
    (fun _ _ => .inl rfl) (fun _ _ _ _ _ => trivial)
  exact ⟨u,hFence,hBar,hRelease,hu,hTail,hFrame⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
