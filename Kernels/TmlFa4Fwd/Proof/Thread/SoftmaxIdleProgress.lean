-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxFallbackProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWaits
import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackStart
import Kernels.TmlFa4Fwd.Proof.StatsBarrierSetup
import Kernels.TmlFa4Fwd.Flow.Code.Part051

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

/-- The launch warp and shared base retained by the idle softmax path. -/
def idleCarry (l : Launch) (warp : Fin 8) : List (Nat × Value) :=
  [(1062, b32 warp.val), (2535, b32 l.sharedBase)]

private theorem signedIdleWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem exhaustedComparison {l : Launch} {g cta batch : Nat} (warp : Fin 8)
    (hCta : cta + 1 < 2 ^ 31) :
    Seg kernel Assumptions.all l g 2 3209
      ([(7244,b32 (cta+1)),(1072,b32 cta),(7243,b32 batch),(7247,b32 batch)] ++ idleCarry l warp)
      3211 ((464,.pred false) :: (7243,b32 batch) :: (7247,b32 batch) :: idleCarry l warp) := by
  intro t ht
  have h0 : cta < 2 ^ 31 := by omega
  have h1 : cta < 2 ^ 32 := by omega
  have h2 : cta + 1 < 2 ^ 32 := by omega
  simp only [idleCarry, List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using
    simp [truncBits_ofNat h1 (by decide), truncBits_ofNat h2 (by decide),
      signedIdleWord h0, signedIdleWord hCta, compare, Option.getD_some]

private theorem exhaustedFallsThrough {l : Launch} {g batch : Nat} (warp : Fin 8)
    {t : TState}
    (ht : At t 3211
      ((464,.pred false) :: (7243,b32 batch) :: (7247,b32 batch) :: idleCarry l warp)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u 3212 ((7243,b32 batch) :: (7247,b32 batch) :: idleCarry l warp) := by
  obtain ⟨u, hu, hU⟩ := run_bra (A := []) (K := kernel) (L := l) (g := g)
    Flow.code_3211 false ht ht.2.2.2.2.1 (by simp)
  have hEq : tauStep kernel Assumptions.all l g t = tauStep kernel [] l g t :=
    Assumptions.tauStep_all_eq_nil (by rw [ht.1]; decide) (ht.1.symm ▸ Flow.code_3211) rfl
  exact ⟨u, by simpa only [run,hEq] using hu, hU.mono hU.2.2.2.2.2⟩

private theorem noWorkPredicate {l : Launch} {g batch : Nat} (warp : Fin 8)
    (hBatch : batch < 2 ^ 31) :
    Seg kernel Assumptions.all l g 3 3212
      ((7243,b32 batch) :: (7247,b32 batch) :: idleCarry l warp)
      3215 ((465,.pred true) :: (783,.pred false) :: idleCarry l warp) := by
  intro t ht
  have hb : batch < 2 ^ 32 := by omega
  simp only [idleCarry] at ht ⊢
  seg_fp ht using
    simp [truncBits_ofNat hb (by decide), signedIdleWord hBatch, compare, Option.getD_some]

private theorem exhaustedGoesToSetup {l : Launch} {g : Nat} (warp : Fin 8) {t : TState}
    (ht : At t 3215 ((465,.pred true) :: (783,.pred false) :: idleCarry l warp)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u 3274 ((783,.pred false) :: idleCarry l warp) := by
  obtain ⟨u, hu, hU⟩ := run_bra (A := []) (K := kernel) (L := l) (g := g)
    Flow.code_3215 true ht ht.2.2.2.2.1 (by simp)
  have hEq : tauStep kernel Assumptions.all l g t = tauStep kernel [] l g t :=
    Assumptions.tauStep_all_eq_nil (by rw [ht.1]; decide) (ht.1.symm ▸ Flow.code_3215) rfl
  exact ⟨u, by simpa only [run,hEq] using hu, hU.mono hU.2.2.2.2.2⟩

set_option maxRecDepth 100000 in
private theorem idleSetupBranch {l : Launch} {g : Nat} (warp : Fin 8) {t : TState}
    (ht : At t 3274 ((783,.pred false) :: idleCarry l warp)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 7733 ((7258,b32 1) :: idleCarry l warp) := by
  let F := (783,.pred false) :: idleCarry l warp
  have hF : Holds t.regs F := ht.2.2.2.2
  obtain ⟨u, hu, hU⟩ := (softmaxStatsBarrierCore l g warp).apply
    (ht.mono ⟨hF.2.1,trivial⟩)
  have hStraight : ((kernel.code.drop 3274).take 8).all
      (fun i => schedulerFallsThrough i.op) = true := by
    decide +kernel
  have hWrites : ((kernel.code.drop 3274).take 9).all
      (fun i => (F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    change ((kernel.code.drop 3274).take 9).all
      (fun i => [783,1062,2535].all (fun r => !(writesRegs i.op).contains r)) = true
    decide +kernel
  have hCore (s : TState) (hLo : 3274 ≤ s.pc) (hHi : s.pc < 3283) :
      out kernel Assumptions.all l g s = out kernel [] l g s := by
    cases hs : kernel.code[s.pc]? with
    | none => simp [out, hs]
    | some ins =>
      have hOps : ((kernel.code.drop 3274).take 9).all
          (fun i => Assumptions.coreOp i.op) = true := by decide +kernel
      have hm : ins ∈ (kernel.code.drop 3274).take 9 := by
        apply List.mem_of_getElem? (i := s.pc - 3274)
        rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      apply Assumptions.out_all_eq_nil _ _ _ hs (List.all_eq_true.mp hOps ins hm)
      all_goals
        simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
          Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
        omega
  have hRun := schedulerLocalTransport (lo := 3274) (len := 9) hStraight
    (fun hl hh => hCore _ hl hh) hu ht.1.ge (by rw [ht.1])
  have hSaved := holdsSchedulerFrame hF
    (fun _ hr => schedulerLocalFrame hWrites hStraight hu ht.1.ge (by rw [ht.1]) hr)
    (fun _ hr => List.mem_map_of_mem hr)
  have hAt : At u 3283 F := hU.mono hSaved
  have hGate : Seg kernel Assumptions.all l g 2 3283 F 3285
      ((480,.pred true) :: (7258,b32 1) :: idleCarry l warp) := by
    intro s hs
    simp only [F,idleCarry] at hs ⊢
    seg_fp hs using rfl
  obtain ⟨v,hv,hV⟩ := hGate u hAt
  obtain ⟨w,hw,hW⟩ := run_bra (A := []) (K := kernel) (L := l) (g := g)
    Flow.code_3285 true hV hV.2.2.2.2.1 (by simp)
  have hEq : tauStep kernel Assumptions.all l g v = tauStep kernel [] l g v :=
    Assumptions.tauStep_all_eq_nil (by rw [hV.1]; decide) (hV.1.symm ▸ Flow.code_3285) rfl
  have hw' : run kernel Assumptions.all l g 1 v = some w := by simpa only [run,hEq] using hw
  exact ⟨w, run_rtg (run_comp (run_comp hRun hv) hw'), hW.mono hW.2.2.2.2.2⟩

private theorem terminalAddressBits {l : Launch} (flag : Bool)
    (hBase : l.sharedBase + 232448 ≤ 2 ^ 18) :
    let offset := if flag then 8 else 0
    let scale := truncBits 32 (BitVec.ofNat 64
      ((truncBits 16 (truncBits 16 (if flag then 1#64 else 0#64))).toNat *
        (truncBits 16 8#64).toNat))
    truncBits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase + scale))
      + truncBits 32 192#64) = BitVec.ofNat 64 (l.sharedBase + (192 + offset)) := by
  dsimp only
  have hImm : truncBits 32 192#64 = BitVec.ofNat 64 192 := rfl
  have h32 : l.sharedBase < 2 ^ 32 := by omega
  have hLow32 : l.sharedBase + 8 < 2 ^ 32 := by omega
  have hH192 : l.sharedBase + 192 < 2 ^ 32 := by omega
  have hH200 : l.sharedBase + 200 < 2 ^ 32 := by omega
  cases flag
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    have hZero : truncBits 32 (BitVec.ofNat 64
        ((truncBits 16 (truncBits 16 0#64)).toNat * (truncBits 16 8#64).toNat)) = 0#64 := rfl
    rw [hZero, BitVec.add_zero, truncBits_ofNat h32 (by decide), truncBits_ofNat h32 (by decide),
      hImm, ← BitVec.ofNat_add, truncBits_ofNat hH192 (by decide)]
  · simp only [↓reduceIte]
    have hEight : truncBits 32 (BitVec.ofNat 64
        ((truncBits 16 (truncBits 16 1#64)).toNat * (truncBits 16 8#64).toNat)) =
          BitVec.ofNat 64 8 := rfl
    rw [hEight, ← BitVec.ofNat_add,
      truncBits_ofNat hLow32 (by decide), truncBits_ofNat hLow32 (by decide), hImm,
      ← BitVec.ofNat_add, show l.sharedBase + 8 + 192 = l.sharedBase + 200 by omega,
      truncBits_ofNat hH200 (by decide)]

private theorem terminalStageCompare (l : Launch) (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 1 7733 ((7258,b32 1) :: idleCarry l warp) 7734
      ((680,.pred (decide (3 < warp.val))) :: (7258,b32 1) :: idleCarry l warp) := by
  have hWarp31 : warp.val < 2 ^ 31 := by have := warp.isLt; omega
  have hWarp32 : warp.val < 2 ^ 32 := by omega
  have hThree : toSigned 32 (truncBits 32 3#64) = (3 : Int) := by decide
  intro t ht
  simp only [idleCarry] at ht ⊢
  seg_fp ht using
    simp [truncBits_ofNat hWarp32 (by decide), compare, signedIdleWord hWarp31,
      hThree, Option.getD_some]

private theorem terminalAddressLow (l : Launch) (g : Nat) (warp : Fin 8)
    (hBase : l.sharedBase + 232448 ≤ 2 ^ 18) :
    Seg kernel [] l g 4 7734
      ((680,.pred false) :: (7258,b32 1) :: idleCarry l warp)
      7738 ((5864,b32 (l.sharedBase+192)) :: (7258,b32 1) :: idleCarry l warp) := by
  intro t ht
  simp only [idleCarry] at ht ⊢
  have hh := congrArg (Value.bits 32) (terminalAddressBits false hBase)
  have hWord : truncBits 32 (BitVec.ofNat 64 l.sharedBase) = BitVec.ofNat 64 l.sharedBase :=
    truncBits_ofNat (by omega) (by decide)
  seg_fp ht using
    (simp only [show (some IType.u == some IType.s) = false by decide,
      Bool.false_eq_true, ↓reduceIte, hWord]; exact hh)

private theorem terminalAddressHigh (l : Launch) (g : Nat) (warp : Fin 8)
    (hBase : l.sharedBase + 232448 ≤ 2 ^ 18) :
    Seg kernel [] l g 4 7734
      ((680,.pred true) :: (7258,b32 1) :: idleCarry l warp)
      7738 ((5864,b32 (l.sharedBase+200)) :: (7258,b32 1) :: idleCarry l warp) := by
  intro t ht
  simp only [idleCarry] at ht ⊢
  have hh := congrArg (Value.bits 32) (terminalAddressBits true hBase)
  have hWord : truncBits 32 (BitVec.ofNat 64 l.sharedBase) = BitVec.ofNat 64 l.sharedBase :=
    truncBits_ofNat (by omega) (by decide)
  seg_fp ht using
    (simp only [show (some IType.u == some IType.s) = false by decide,
      Bool.false_eq_true, ↓reduceIte, hWord]; exact hh)

set_option maxRecDepth 100000 in
private theorem terminalTransport {l : Launch} {g : Nat} {t u : TState} (hPc : t.pc = 7734)
    (hr : run kernel [] l g 4 t = some u) : run kernel Assumptions.all l g 4 t = some u := by
  apply schedulerLocalTransport (lo := 7734) (len := 4) (by kernel_rfl) _ hr hPc.ge
    (by rw [hPc])
  intro s hLo hHi
  cases hGet : kernel.code[s.pc]? with
  | none => simp [out,hGet]
  | some ins =>
    have hAll : ((kernel.code.drop 7734).take 4).all (fun i => Assumptions.coreOp i.op) =
        true := by kernel_rfl
    have hm : ins ∈ (kernel.code.drop 7734).take 4 := by
      apply List.mem_of_getElem? (i := s.pc - 7734)
      rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    apply Assumptions.out_all_eq_nil _ _ _ hGet (List.all_eq_true.mp hAll ins hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

private theorem terminalAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 5 7733 ((7258,b32 1) :: idleCarry l warp) 7738
      ((5864,b32 (waitLoc l g (stageOf warp) 9).addr) :: (7258,b32 1) :: idleCarry l warp) := by
  intro t ht
  obtain ⟨u,hu,hU⟩ := terminalStageCompare l g warp t ht
  have hB := warp.isLt
  by_cases hStage : 3 < warp.val
  · have hStageVal : (stageOf warp).val = 1 := by change warp.val / 4 = 1; omega
    rw [decide_eq_true hStage] at hU
    obtain ⟨v,hv,hV⟩ := terminalAddressHigh l g warp hp.shared.2.1 u hU
    exact ⟨v,run_comp hu (terminalTransport hU.1 hv),
      by simpa only [waitLoc,waitSite,hStageVal] using hV⟩
  · have hStageVal : (stageOf warp).val = 0 := by change warp.val / 4 = 0; omega
    rw [decide_eq_false hStage] at hU
    obtain ⟨v,hv,hV⟩ := terminalAddressLow l g warp hp.shared.2.1 u hU
    exact ⟨v,run_comp hu (terminalTransport hU.1 hv),
      by simpa only [waitLoc,waitSite,hStageVal] using hV⟩

/-- At the exhausted scan boundary, the no-work path jumps to the terminal poll. -/
theorem idleTerminalAtFromExhausted {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first shuffles : Nat} (hg : g < l.threads) {warp : Fin 8}
    {ends : Nat → Option TState} (hDone : p.batch ≤ first + 31)
    (exhausted : SchedulerWarpAt l X g 3209 (fun lane =>
      fallbackAdvanceFacts p l (warpLane l g lane) warp first
        (tilePrefix p (min p.batch (first + 31)) * p.heads)) shuffles 0 ends) :
    ∃ cur : SchedulerWarpAt l X g 7738
      (fun lane => (5864,b32 (waitLoc l (warpLane l g lane) (stageOf warp) 9).addr) ::
        (7258,b32 1) :: idleCarry l warp) shuffles 0 ends,
      cur.pos = exhausted.pos ∧ cur.before = exhausted.before := by
  exact exhausted.advanceLocalPreserving (pc' := 7738) (by
    intro lane hl
    let thread := warpLane l g lane
    let cta := thread/l.block
    have hThread := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.1
    have hCta : cta + 1 < 2 ^ 31 := by
      have hGrid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hThread
      have hLimit := hp.grid.2.2
      change cta < l.grid at hGrid
      omega
    have ht := exhausted.checkpoint lane hl
    have hRegs : Holds (exhausted.state lane).regs
        (fallbackAdvanceFacts p l thread warp first
          (tilePrefix p (min p.batch (first + 31)) * p.heads)) :=
      ht.2.2.2.2
    have hInput : At (exhausted.state lane) 3209
      ([(7244,b32 (cta+1)),(1072,b32 cta),(7243,b32 p.batch),(7247,b32 p.batch)] ++
        idleCarry l warp) := by
      apply ht.mono
      refine ⟨holds_mem hRegs ?_, holds_mem hRegs ?_, holds_mem hRegs ?_,
        holds_mem hRegs ?_, holds_mem hRegs ?_, holds_mem hRegs ?_, trivial⟩ <;>
        simp [fallbackAdvanceFacts, fallbackBaseFrame, schedulerEntry, dispatchOutput,
          dispatchInput, Nat.min_eq_right hDone, Mma.groupScanFacts, Mma.scanSite, cta]
    obtain ⟨a,ha,hA⟩ := (exhaustedComparison warp hCta).apply hInput
    obtain ⟨b,hb,hB⟩ := exhaustedFallsThrough warp hA
    obtain ⟨c,hc,hC⟩ := (noWorkPredicate warp hp.shape.2.1).apply hB
    obtain ⟨d,hd,hD⟩ := exhaustedGoesToSetup warp hC
    obtain ⟨e,he,hE⟩ := idleSetupBranch warp hD
    obtain ⟨f,hf,hF⟩ := (terminalAddress hp thread warp).rtg hE
    exact ⟨f,(run_rtg (run_comp (run_comp (run_comp ha hb) hc) hd)).trans (he.trans hf),hF⟩)

private theorem idleTerminalFromExhausted {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first shuffles : Nat} (hg : g < l.threads) {warp : Fin 8}
    {ends : Nat → Option TState} (hDone : p.batch ≤ first + 31)
    (exhausted : SchedulerWarpReached l X g 3209 (fun lane =>
      fallbackAdvanceFacts p l (warpLane l g lane) warp first
        (tilePrefix p (min p.batch (first + 31)) * p.heads)) shuffles 0 ends) :
    Nonempty (SchedulerWarpReached l X g 7738
      (fun lane => (5864,b32 (waitLoc l (warpLane l g lane) (stageOf warp) 9).addr) ::
        (7258,b32 1) :: idleCarry l warp) shuffles 0 ends) := by
  obtain ⟨done,hPos,hBefore⟩ := idleTerminalAtFromExhausted hp hg hDone exhausted.toSchedulerWarpAt
  exact ⟨exhausted.reframe done hPos hBefore⟩

/-- Any idle softmax warp reaches its terminal statistics poll after the real group scans. -/
theorem idleTerminalPollCursorOfAllGroups {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8)
    (hProtected : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block) :
    let warp : Fin 8 := ⟨warpIndex l g,hw⟩
    ∃ count ends, Nonempty (SchedulerWarpReached l X g 7738
      (fun lane => (5864,b32 (waitLoc l (warpLane l g lane) (stageOf warp) 9).addr) ::
        (7258,b32 1) :: idleCarry l warp) count 0 ends) := by
  obtain ⟨_, count, ends, hDone, ⟨exhausted⟩⟩ :=
    idleSoftmaxSearchExhaustedOfMaximal hp hMax hg hw hProtected hIdle
  exact ⟨count,ends,idleTerminalFromExhausted hp hg hDone exhausted⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
