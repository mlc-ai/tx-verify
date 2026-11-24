-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedRescaleLoadOrigin
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasUnpackShape
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleBiasedScoreInputs
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleAbiScale
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRecordedEntry
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxProbabilityRegisters
import Kernels.TmlFa4Fwd.Proof.Thread.AllScoreLoadWords
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasRendezvous

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

/-- The realized Bias affine inputs leading to a recorded rescale store. -/
structure ObservedBiasedRescaleInputs (p : Params) (l : Launch) (X : Execution)
    (g pos : Nat) where
  firstLoad : Nat
  biasWait : Nat
  enter : Nat
  firstBefore : firstLoad+4 ≤ biasWait
  waitBefore : biasWait < enter
  enterBefore : enter ≤ pos
  noneBefore : ∀ k, firstLoad ≤ k → k < pos → ∀ e, X.get (g,k) = some e →
    e.pc ≠ (statsStore (rescaleStore true)).pc
  before : TState
  warp : Fin 8
  warpIndex : warp.val = Prologue.warpIndex l g
  roleEntry : Nat
  roleSeed : TState
  roleBefore : roleEntry ≤ biasWait
  roleAt : At roleSeed 3103 [(1062,b32 warp.val),(2535,b32 l.sharedBase)]
  rolePrefix : TraceReach kernel Assumptions.all l g {} ((X.tr g).take roleEntry) roleSeed
  beforePath : TraceReach kernel Assumptions.all l g roleSeed
    (((X.tr g).drop roleEntry).take (biasWait-roleEntry)) before
  waitEvent : ∃ phase, X.get (g,biasWait) =
    some ⟨5181,.wait (waitLoc l g (stageOf warp) 5) phase true true .cta⟩
  beforeStops : Stops kernel Assumptions.all l g before
  ready : TState
  ending : Option TState
  bias : Nat → Option ℝ
  dot : Nat → ℝ
  roleRun : Run kernel Assumptions.all l g roleSeed ((X.tr g).drop roleEntry) ending
  checkpoint : At ready (biasBodyStart true) []
  geometry : Holds ready.regs [(1062,b32 warp.val),(2535,b32 l.sharedBase),(5127,b32 (3+warp.val))]
  oldMass : ∃ value, ready.regs 7257 = some value
  statisticsPhase : ∃ value, ready.regs 7258 = some value
  readyPath : TraceReach kernel Assumptions.all l g before
    (((X.tr g).drop biasWait).take (enter-biasWait)) ready
  continuation : Run kernel Assumptions.all l g ready ((X.tr g).drop enter) ending
  inverseScale : readERealPair l g ready (.reg 7896) =
    some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal)))
  scale : ready.regs 7132 = some (b32 p.scaleLog2Bits)
  negativeScale : ready.regs 1230 = some (fl (-abiFloat p.scaleLog2Bits))
  prior : ready.regs 7251 = before.regs 7251
  unpacked : ∀ i : Fin 16, BiasUnpacked true i ready (fun k =>
    biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1)))
  packed : ∀ pair < 64, readERealPair l g ready (.reg (7367+pair)) =
    some (.ok ((dot (2*pair) : EReal),(dot (2*pair+1) : EReal)))

/-- Replay from the actual same-window score load and Bias acquire to the affine
entry. A recorded later write guarantees the Bias reads and rendezvous on the prefix. -/
theorem observedBiasedRescaleInputs {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g pos : Nat} {a : Acc} {bytes : List Byte}
    (he : StatisticsStore X (g,pos) (rescaleStore true) a bytes) :
    Nonempty (ObservedBiasedRescaleInputs p l X g pos) := by
  obtain ⟨start,address,vals,hStart,hLoad,hPrevious⟩ := biasedRescaleScoreOrigin hp hX he
  obtain ⟨w',hw',_⟩ :=
    softmaxBodySuffix hp hX hLoad (by decide : 3420 ≤ 5112) (by decide : 5112 < 7742)
  obtain ⟨w,hw,entry,s,ending,hEntry,hs,hOrigin,hRun⟩ :=
    softmaxRoleEntryRecorded hp hX hLoad (by decide : 173 < 5112) (by decide : 5112 ≠ 3102)
      (hw' ▸ w'.isLt)
  let stage := stageOf w
  let target : Event := ⟨(statsStore (rescaleStore true)).pc,.wr a bytes⟩
  have hGet : X.get (g,pos) = some target := he
  have hTarget : target ∈ (X.tr g).drop (start+4) := by
    apply List.mem_of_getElem? (i := pos-(start+4))
    rwa [List.getElem?_drop,Nat.add_sub_of_le hStart]
  have hRead (q : Fin 4) {xs : List Value}
      (h : X.get (g,start+q.val) =
        some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g stage q) xs .s32x32b)⟩)
      (k : Fin 32) : ∃ v, xs[k.val]? = some (.float .f32 v) := by
    obtain ⟨_,_,_,_,_,_,hWords⟩ := scoreLoadWordsOfLaunch hp hX hFrame .biased q h
    exact ⟨_,hWords k⟩
  have hKind : target.pc ≠ 5181 := by change 5682 ≠ 5181; decide
  obtain ⟨wait,phase,pre,words,hWait,hWaitGet,hLoads,hPairs,hReach,hStop,_,hOrder⟩ :=
    biasedScoreWaitPackedInPrefix hp w hs hRun hLoad hEntry (fun q xs h k hk => by
      obtain ⟨_,hw⟩ := hRead q h ⟨k,hk⟩
      simp [List.getD_eq_getElem?_getD,hw,Value.bytes,FloatFmt.bytes])
      (.inr ⟨target,hTarget,hKind⟩)
  have hBefore := hOrder pos target hStart hGet hKind
  have hMore : (X.tr g).drop (wait+1) ≠ [] :=
    fun h => (Nat.not_le_of_lt (len_of_get hGet)) ((List.drop_eq_nil_iff.mp h).trans (by omega))
  obtain ⟨s0,t,hs0,_,hScoreKeeps,ht,hInv,hBases,hBiasRun,hWaitPath,hWaitStop,hBaseKeeps,
    hVectorPath⟩ :=
    repeatedBiasVectorStartWithPath hp w hs hRun (by omega) hWaitGet hMore
  have hSame := reachedEventSourceUnique hReach hWaitPath hStop hWaitStop
  subst s0
  obtain ⟨scaled,_,hPc,_,_,_,_,hScales,hScaleEvent,_,hScalePath⟩ :=
    softmaxRoleEventFromEntryWithScratch hp w hs hRun hWaitGet (by omega)
      (by decide : 5181 < 7742) (initialShiftScaleFrame p hs.1)
      (fun hLo hHi hSub _ _ _ hPerm hStep =>
        shiftScaleFrameStep hp hLo hHi hSub hPerm hStep)
  have hSame := reachedEventSourceUnique hReach hScalePath hStop (stops_of_estep hScaleEvent)
  subst scaled
  have hAbi := shiftScaleAbiAtBiasWait hScales hPc
  have hNeg := (shiftScalesOfFrame hScales
    (hPc.symm ▸ (by decide : 4399 ≤ 5181)) (hPc.symm ▸ (by decide : 5181 ≤ 7604))).1
  obtain ⟨f,bias,hf,hBias,hReadKeep,hFenceRun,hFenceBefore,hReadPath⟩ :=
    repeatedBiasUnpackShapePathBeforeWrite hp hX hFrame stage (ht.mono trivial)
      hBases hBiasRun (by omega) he
  have hKeep (r : Nat) (hSafe : ∀ i, biasVectorKeeps true i r) :
      f.regs r = t.regs r := hReadKeep r hSafe
  have hFence : At f (biasFencePc true) (biasFenceFacts l g w true) := by
    apply hf.mono
    refine Epilogue.holdsSchedulerFrame ht.2.2.2.2 (fun r hR => ?_)
      (fun _ hx => List.mem_map_of_mem hx)
    obtain ⟨⟨r',v⟩,hPair,heq⟩ := List.mem_map.mp hR
    change r' = r at heq
    subst r'
    apply hKeep
    intro i
    simp only [biasFenceFacts,biasStageReg,biasKeep,ite_true,List.mem_cons,List.not_mem_nil,
      or_false,Prod.mk.injEq] at hPair
    rcases hPair with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ <;>
      unfold biasVectorKeeps <;> fin_cases i <;> decide
  let enter := if laneOf l g = 0 then wait+1+64+3 else wait+1+64+2
  obtain ⟨u,_,_,_,hu,hr,hRendezvousKeep,hEnter,hRendezvousPath⟩ :=
    biasFinishTraceWithPathGuarded hp w true
    hFence hFenceRun (cursor := (· ≤ pos)) hFenceBefore
    (fun _ h => .inr (h.trans_lt (len_of_get he)))
    (fun k e hk hNoWrite hLe => by
      rcases Nat.eq_or_lt_of_le hLe with rfl | hLt
      · exact (hNoWrite _ _ (congrArg Event.kind (Option.some.inj (hk.symm.trans hGet)))).elim
      · omega)
  have hReadyPath : TraceReach kernel Assumptions.all l g pre
      (((X.tr g).drop wait).take (enter-wait)) u := by
    have hLength : enter-wait = 1+(64+(if laneOf l g = 0 then 3 else 2)) := by
      dsimp [enter]
      split <;> omega
    rw [hLength,List.take_add,List.drop_drop,List.take_add,List.drop_drop]
    exact hVectorPath.append (hReadPath.append hRendezvousPath)
  have preserve {r : Nat} (hV : ∀ i, biasVectorKeeps true i r)
      (hF : r ∉ biasFenceWritten true) (hB : r ∉ [9755,4166,4167,4168,4169,4170]) :
      u.regs r = pre.regs r :=
    (hRendezvousKeep _ hF).trans ((hReadKeep _ hV).trans (hBaseKeeps _ hB))
  have hEntryWait : entry ≤ wait := by omega
  obtain ⟨z,_,hZ,hZPath,hWarp,hBase,hBar⟩ :=
    statisticsBarrierFromEntry hp w hs hRun hWaitGet hEntryWait
      (by change 3283 ≤ 5181; decide) (by change 5181 ≤ 7604; decide)
  have hSame := reachedEventSourceUnique hReach hZPath hStop (stops_of_estep hZ)
  subst z
  obtain ⟨z,_,hZ,hZPath,⟨mass,hMass⟩,⟨statPhase,hStatPhase⟩⟩ :=
    probabilityCarryRegistersFromEntry hp w hs hRun hWaitGet hEntryWait
      (by change 5005 < 5181; decide) (by change 5181 ≤ 7604; decide)
  have hSame := reachedEventSourceUnique hReach hZPath hStop (stops_of_estep hZ)
  subst z
  have resident {r : Nat} {value : Value}
      (hReg : r ∈ [1062,2535,5127,7257,7258])
      (hv : pre.regs r = some value) : u.regs r = some value := by
    have hCase : r = 1062 ∨ r = 2535 ∨ r = 5127 ∨ r = 7257 ∨ r = 7258 := by
      simpa using hReg
    rcases hCase with rfl | rfl | rfl | rfl | rfl <;>
      exact (preserve (by unfold biasVectorKeeps; decide) (by decide) (by decide)).trans hv
  have hIn : u.regs 7896 = some (joinValue (b32 p.invScaleBits) (b32 p.invScaleBits)) :=
    (hRendezvousKeep _ (by decide)).trans
      ((hReadKeep _ (by unfold biasVectorKeeps; decide)).trans hInv)
  obtain ⟨_,inv,_,hDecode,_,_⟩ := hp.scales
  have hBits := (hp.values (14,p.invScaleBits) (by simp [Params.scalarWords])).1
  have hVal := valFloat_b32 (by omega) hDecode
  have hSplit : splitValue 64 (joinValue (b32 p.invScaleBits) (b32 p.invScaleBits)) =
      (b32 p.invScaleBits,b32 p.invScaleBits) :=
    split_join_bits (by rw [toNat_ofNat_lt (by omega)]; exact hBits)
  have hReadInv := readERealPair_reg (L := l) (g := g) hIn
    (by rw [hSplit]; exact hVal) (by rw [hSplit]; exact hVal)
  have hAbiInv : abiFloat p.invScaleBits = (inv : ℝ) := by simp [abiFloat,hDecode]
  have hTyped (q : Fin 4) (k : Fin 32) : ∃ v, (words q)[k.val]? = some (.float .f32 v) :=
    hRead q (hLoads q).2 k
  choose values hValues using hTyped
  let dot := fun n => values ⟨n/32%4,Nat.mod_lt _ (by decide)⟩ ⟨n%32,Nat.mod_lt _ (by decide)⟩
  refine ⟨⟨start,wait,enter,hWait,?_,hEnter,hPrevious,
    pre,w,hw,entry,s,hEntryWait,hs,hOrigin,hReach,⟨phase,hWaitGet⟩,hStop,u,ending,bias,dot,hRun,
    hu.mono trivial,⟨resident (by decide) hWarp,resident (by decide) hBase,
      resident (by decide) hBar,trivial⟩,
    ⟨mass,resident (by decide) hMass⟩,⟨statPhase,resident (by decide) hStatPhase⟩,hReadyPath,hr,
    by rw [hAbiInv]; exact hReadInv,
    (preserve (by unfold biasVectorKeeps; decide) (by decide) (by decide)).trans hAbi,
    (preserve (by unfold biasVectorKeeps; decide) (by decide) (by decide)).trans hNeg,
    preserve (by unfold biasVectorKeeps; decide) (by decide) (by decide),?_,?_⟩⟩
  · dsimp [enter]
    split <;> omega
  · intro i k hk
    have hSafe : (biasUnpackRegs true i k).1 ∉ biasFenceWritten true ∧
        (biasUnpackRegs true i k).2 ∉ biasFenceWritten true := by
      fin_cases i <;> interval_cases k <;> decide
    exact ⟨(hRendezvousKeep _ hSafe.1).trans (hBias i k hk).1,
      (hRendezvousKeep _ hSafe.2).trans (hBias i k hk).2⟩
  · intro pair hPair
    let q : Fin 4 := ⟨pair/16,by omega⟩
    let k : Fin 16 := ⟨pair%16,Nat.mod_lt _ (by decide)⟩
    let low : Fin 32 := ⟨2*k.val,by have := k.isLt; omega⟩
    let high : Fin 32 := ⟨2*k.val+1,by have := k.isLt; omega⟩
    have hReg : repeatedScorePairReg .biased q k.val = 7367+pair := by
      change 7367+16*(pair/16)+pair%16 = _
      omega
    have hN (n : Fin 32) : dot (32*q.val+n.val) = values q n := by
      have hQ := q.isLt
      have hn := n.isLt
      have hOrd : (32*q.val+n.val)/32%4 = q.val := by omega
      have hIndex : (32*q.val+n.val)%32 = n.val := by omega
      simp only [dot,hOrd,hIndex,Fin.eta]
    have hLow : 32*q.val+low.val = 2*pair := by dsimp [q,k,low]; omega
    have hHigh : 32*q.val+high.val = 2*pair+1 := by dsimp [q,k,high]; omega
    have hPacked : u.regs (repeatedScorePairReg .biased q k.val) =
        pre.regs (repeatedScorePairReg .biased q k.val) := by
      rw [hReg]
      apply preserve
      · intro i
        have hReads := (by decide : ∀ i : Fin 16,
          (biasReadRegs true i).all (fun r => decide (r < 7367)) = true) i
        have hUnpack := (by decide : ∀ i : Fin 16, (biasUnpackRegs true i 0).1 < 7367) i
        exact ⟨fun hm => by
          have hBound := of_decide_eq_true (List.all_eq_true.mp hReads _ hm)
          omega, .inr (by omega)⟩
      · intro hm
        have hAudit : (biasFenceWritten true).all (fun r => decide (r < 7367 ∨ 7431 ≤ r)) = true :=
          by decide
        have hBound := of_decide_eq_true (List.all_eq_true.mp hAudit _ hm)
        omega
      · simp only [List.mem_cons,List.not_mem_nil,or_false]
        omega
    have hPairWord := repeatedPackedScoreValues (l := l) (g := g) .biased q k (values q)
      (hValues q) (hPacked.trans (hPairs q k))
    dsimp only at hPairWord
    rw [hReg] at hPairWord
    have hlo : dot (2*pair) = values q low := hLow ▸ hN low
    have hhi : dot (2*pair+1) = values q high := hHigh ▸ hN high
    rw [hlo,hhi]
    exact hPairWord

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
