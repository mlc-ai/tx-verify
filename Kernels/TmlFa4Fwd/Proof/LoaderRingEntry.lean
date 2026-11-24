-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRingVisits
public import Kernels.TmlFa4Fwd.Flow.Code.Part014
public import Kernels.TmlFa4Fwd.Flow.Code.Part021

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

private theorem entrySigned {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

/-- After the warm-path predicate, the decoded initializer seeds the warm ring counter at zero. -/
theorem loaderWarmCounterInit {l : Launch} {g trips : Nat} (phase : Bool) :
    Seg kernel Assumptions.all l g 4 913 [(7177, loaderPhaseWord phase), (1091, b32 trips)]
      917 [(7174, b32 0), (1091, b32 trips)] := by
  intro s hs
  have hseg : Seg kernel [] l g 4 913 [(7177, loaderPhaseWord phase), (1091, b32 trips)]
      917 [(7174, b32 0), (1091, b32 trips)] := by
    intro t ht
    seg_fp ht using rfl
  obtain ⟨u, hu, hU⟩ := hseg s hs
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by set_option maxRecDepth 100000 in kernel_rfl) hu
  exact ⟨u, huA, hU⟩

/-- The steady counter seed as an ordinary local segment for caller-selected frame replay. -/
theorem loaderSteadyCounterInitCore {l : Launch} {g trips : Nat} (hTrip : trips < 2^31) :
    Seg kernel [] l g 2 1353 [(1091, b32 trips)]
    1355 [(7181, b32 (min trips 9)), (1091, b32 trips)] := by
  have h32 : trips < 2 ^ 32 := by omega
  have hZero : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := rfl
  have hNine : toSigned 32 9#64 = 9 := rfl
  have hNineWord : truncBits 32 (BitVec.ofInt 64 9) = 9#64 := rfl
  have hMin : (IntOp.min false == IntOp.max false) = false := rfl
  have hMax : (IntOp.max false == IntOp.max false) = true := rfl
  have hMaxWord : (if 0 < (trips : Int) then BitVec.ofNat 64 trips
      else truncBits 32 (BitVec.ofInt 64 0)) = BitVec.ofNat 64 trips := by
    by_cases h : trips = 0
    · subst trips
      decide
    · simp [h]
  have hv : (if (trips : Int) < 9 then BitVec.ofNat 64 trips else 9#64) =
      BitVec.ofNat 64 (min trips 9) := by
    by_cases h : trips < 9
    · have hc : (trips : Int) < 9 := by exact_mod_cast h
      simp [hc, min_eq_left h.le]
    · have hc : ¬(trips : Int) < 9 := by exact_mod_cast h
      simp [hc, min_eq_right (Nat.le_of_not_gt h)]
  intro t ht
  seg_fp ht using simp only [hMin, hMax, b32, truncBits_ofNat h32 (by decide), compare,
    kind_s_beq_s, Bool.false_eq_true, entrySigned hTrip, hZero, hNine, hNineWord,
    ↓reduceIte, decide_eq_true_eq, gt_iff_lt, hMaxWord, hv]

/-- The steady counter is seeded at the smaller of the remaining trip count and nine. -/
theorem loaderSteadyCounterInit {l : Launch} {g trips : Nat} (hTrip : trips < 2 ^ 31) :
    Seg kernel Assumptions.all l g 2 1353 [(1091, b32 trips)]
      1355 [(7181, b32 (min trips 9)), (1091, b32 trips)] := by
  intro s hs
  obtain ⟨u, hu, hU⟩ := (loaderSteadyCounterInitCore (l := l) (g := g) hTrip).apply hs
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by simp) (by set_option maxRecDepth 100000 in kernel_rfl) hu
  exact ⟨u, huA, hU⟩

/-- The steady entry branch preserves a checked frame whether it enters or skips the ring. -/
theorem loaderSteadyCounterGateWithFrame {l : Launch} {g k trips : Nat} (hTrip : trips < 2 ^ 31)
    (hk : k < 2 ^ 31) {F : List (Nat × Value)}
    (hCompare : ((kernel.code.drop 1384).take 1).all
      (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true)
    (hBranch : ((kernel.code.drop 1385).take 1).all
      (fun ins => (F.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) = true) :
    Seg kernel Assumptions.all l g 2 1384 ([(7181, b32 k), (1091, b32 trips)] ++ F)
      (if k < trips then 1386 else 1744) ([(7181, b32 k), (1091, b32 trips)] ++ F) := by
  intro s hs
  obtain ⟨hInputs, hF⟩ := (holds_append ..).mp hs.2.2.2.2
  let pick := decide (trips ≤ k)
  have hCalc : Seg kernel [] l g 1 1384 [(7181, b32 k), (1091, b32 trips)] 1385
      [(209, .pred pick), (7181, b32 k), (1091, b32 trips)] := by
    intro t ht
    dsimp only [pick]
    seg_fp ht using simp only [truncBits_ofNat (show k < 2 ^ 32 by omega) (by decide),
      truncBits_ofNat (show trips < 2 ^ 32 by omega) (by decide), compare, Option.getD_some,
      entrySigned hk, entrySigned hTrip, ge_iff_le, Int.ofNat_le]
  obtain ⟨v, hv, hV⟩ := hCalc s (hs.mono hInputs)
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    hCompare rfl hv
  have hV' : At v 1385 ([(7181, b32 k), (1091, b32 trips)] ++ F) := hV.mono
    ((holds_append ..).mpr ⟨hV.2.2.2.2.2, Epilogue.holdsSchedulerFrame hF hvFrame
      (fun _ h => List.mem_map_of_mem h)⟩)
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1385 pick hV' hV.2.2.2.2.1 (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hV.1
    hBranch rfl hu
  have hAt := hU
  refine ⟨u, run_comp hvA huA, ?_⟩
  by_cases h : k < trips
  · simpa [pick, h, Nat.not_le_of_gt h] using hAt
  · have hn : trips ≤ k := by omega
    simpa [pick, h, hn] using hAt

/-- The steady region is skipped precisely when the warm-up counter has exhausted the trips. -/
theorem loaderSteadyCounterGate {l : Launch} {g k trips : Nat} (hTrip : trips < 2 ^ 31)
    (hk : k < 2 ^ 31) :
    Seg kernel Assumptions.all l g 2 1384 [(7181, b32 k), (1091, b32 trips)]
      (if k < trips then 1386 else 1744) [(7181, b32 k), (1091, b32 trips)] := by
  simpa using loaderSteadyCounterGateWithFrame (F := []) (l := l) (g := g) hTrip hk (by simp)
    (by simp)

private def steadyPrepareCode (ins : Instr) : Bool :=
  ins.op.isLocal && Epilogue.schedulerFallsThrough ins.op &&
    !((writesRegs ins.op).contains 7181) && !((writesRegs ins.op).contains 1091)

private theorem steadyPrepareSlice :
    ((kernel.code.drop 1386).take 10).all steadyPrepareCode = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem steadyPreparePc {op : Op} {pc : Nat}
    (h : Epilogue.schedulerFallsThrough op = true) :
    nextPc op pc = pc + 1 ∧ ∀ n, ¬ BrxTarget op n := by
  cases op <;> simp_all [Epilogue.schedulerFallsThrough, nextPc, BrxTarget]

private def SteadyPrepared (s : TState) (k trips : Nat) : Prop :=
  1386 ≤ s.pc ∧ At s s.pc [(7181, b32 k), (1091, b32 trips)]

private theorem preserveSteadyPrepared {l : Launch} {g k trips : Nat}
    {s u : TState} {ev : Option Event} (hLo : 1386 ≤ s.pc) (hHi : s.pc < 1396)
    (h : WStep kernel Assumptions.all l g s ev u) (hs : SteadyPrepared s k trips) :
    SteadyPrepared u k trips := by
  have hCode {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
      ins.op.isLocal = true ∧
        Epilogue.schedulerFallsThrough ins.op = true ∧
        7181 ∉ writesRegs ins.op ∧ 1091 ∉ writesRegs ins.op := by
    have hGet : ((kernel.code.drop 1386).take 10)[s.pc - 1386]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    have hc' := List.all_eq_true.mp steadyPrepareSlice ins (List.mem_of_getElem? hGet)
    simpa [steadyPrepareCode, and_assoc] using hc'
  rcases h with ⟨-, ht⟩ | ⟨_, -, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore (by omega) (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    obtain ⟨_, hFall, hKeep, hTrips⟩ := hCode hc
    have hN := steadyPreparePc (pc := s.pc) hFall
    rcases tau_core_frame hc ht' with rfl | hFrame
    · exact ⟨by change 1386 ≤ s.pc + 1; omega,
        rfl, rfl, rfl, hs.2.2.2.2.1, hs.2.2.2.2.2⟩
    · have hPc := (hFrame.pc.resolve_right (hN.2 _)).trans hN.1
      exact ⟨by omega, rfl, hFrame.sub.trans hs.2.2.1, hFrame.acc.trans hs.2.2.2.1,
        hFrame.fault.trans hs.2.2.2.2.1, (hFrame.regs 7181 hKeep).trans hs.2.2.2.2.2.1,
        (hFrame.regs 1091 hTrips).trans hs.2.2.2.2.2.2.1, trivial⟩
  · obtain ⟨_, hc, hL, _⟩ := PTX.EventFrame.estep_event_source he
    rw [(hCode hc).1] at hL
    cases hL

/-- At the decoded steady-loop guard, the count either skips the loop or bounds
every finite prefix through the whole loader suffix. -/
theorem loaderSteadyPrefixFromGate {l : Launch} {g k trips : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hTrip : trips < 2 ^ 31) (hk : k < 2 ^ 31)
    (hs : At s 1384 [(7181, b32 k), (1091, b32 trips)]) :
    loaderVisitsAt 1743 vs ≤ 5 * (trips - k + 1) + 2 := by
  obtain ⟨u, hu, hU⟩ := loaderSteadyCounterGate (g := g) hTrip hk s hs
  rcases loaderLocalWalkCut hu hw with hShort | ⟨pre, tail, hTrace, hLen, hTail⟩
  · have h := loaderVisitsAt_le_length 1743 vs
    omega
  · rw [hTrace]
    have hPrefix := loaderVisitsAt_le_append 1743 pre tail
    by_cases he : k < trips
    · have hAt : At u 1386 [(7181, b32 k), (1091, b32 trips)] := by simpa [he] using hU
      have hPc := hAt.1
      have hp : SteadyPrepared u k trips := ⟨hPc.ge, hPc.symm ▸ hAt⟩
      have hIn : 174 ≤ u.pc ∧ u.pc ≤ (ringCounterSite 1).head := by
        rw [hPc]
        decide
      have h := loaderRingPrefixWithEntry 1 hTail hIn hp (budget := trips - k)
        (fun _ hhi step hReady => preserveSteadyPrepared hReady.1 hhi step hReady)
        (fun t hpc hReady => ⟨k, trips, hTrip, he, le_rfl, hpc ▸ hReady.2⟩)
      change loaderVisitsAt 1743 tail ≤ 5 * (trips - k + 1) at h
      omega
    · have hPc : (ringCounterSite 1).branch < u.pc := by
        rw [show u.pc = 1744 from by simpa [he] using hU.1]
        decide
      have h := noLaterRingBranchVisits 1 hTail hPc
      change loaderVisitsAt 1743 tail = 0 at h
      omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
