-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRingEntry
public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
public import Kernels.TmlFa4Fwd.Proof.LoaderTripStart

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private def warmPrepare (s : TState) (trips : Nat) : Prop :=
  912 ≤ s.pc ∧ At s s.pc [(1091, b32 trips)] ∧
    (914 ≤ s.pc → s.regs 7174 = some (b32 0))

private def warmCode (ins : Instr) (pc : Nat) : Bool :=
  ins.op.isLocal && Epilogue.schedulerFallsThrough ins.op &&
    !(writesRegs ins.op).contains 1091 && (pc == 913 || !(writesRegs ins.op).contains 7174)

private theorem warmCodeChecked :
    (((kernel.code.drop 912).take 5).zipIdx 912).all (fun (ins, pc) => warmCode ins pc) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem warmStepLanding {op : Op} {pc : Nat}
    (h : Epilogue.schedulerFallsThrough op = true) :
    nextPc op pc = pc + 1 ∧ ∀ n, ¬ BrxTarget op n := by
  cases op <;> simp_all [Epilogue.schedulerFallsThrough, nextPc, BrxTarget]

/-- The warm ring initializes its iteration word immediately before its first entry. -/
theorem warmCounterSeedCore {l : Launch} {g : Nat} :
    Seg kernel [] l g 1 913 [] 914 [(7174, b32 0)] := by
  intro s hs
  seg_fp hs using rfl

private theorem preserveWarmPrepare {l : Launch} {g trips : Nat}
    {s u : TState} {ev : Option Event} (hLo : 912 ≤ s.pc) (hHi : s.pc < 917)
    (hw : WStep kernel Assumptions.all l g s ev u) (hs : warmPrepare s trips) :
    warmPrepare u trips := by
  have hCode {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
      ins.op.isLocal = true ∧ Epilogue.schedulerFallsThrough ins.op = true ∧
        1091 ∉ writesRegs ins.op ∧ (s.pc = 913 ∨ 7174 ∉ writesRegs ins.op) := by
    have hGet : (((kernel.code.drop 912).take 5).zipIdx 912)[s.pc - 912]? =
        some (ins, s.pc) := by
      rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        Nat.add_sub_of_le hLo, hc]
      rfl
    simpa [warmCode, and_assoc] using
      List.all_eq_true.mp warmCodeChecked _ (List.mem_of_getElem? hGet)
  rcases hw with ⟨-, ht⟩ | ⟨_, -, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← loaderOutCore (by omega) (by omega)]
    obtain ⟨ins, hc⟩ := tau_core_has_code ht'
    obtain ⟨_, hFall, hTrips, hSeed⟩ := hCode hc
    have hN := warmStepLanding (pc := s.pc) hFall
    have hPc : u.pc = s.pc + 1 := by
      rcases tau_core_frame hc ht' with rfl | hFrame
      · rfl
      · exact (hFrame.pc.resolve_right (hN.2 _)).trans hN.1
    have hAt : At u u.pc [(1091, b32 trips)] := by
      rcases tau_core_frame hc ht' with rfl | hFrame
      · exact ⟨rfl, rfl, rfl, hs.2.1.2.2.2.1, hs.2.1.2.2.2.2⟩
      · exact ⟨rfl, hFrame.sub.trans hs.2.1.2.1, hFrame.acc.trans hs.2.1.2.2.1,
          hFrame.fault.trans hs.2.1.2.2.2.1,
          (hFrame.regs 1091 hTrips).trans hs.2.1.2.2.2.2.1, trivial⟩
    refine ⟨by omega, hAt, ?_⟩
    intro hu
    by_cases hInit : s.pc = 913
    · have hh : At s 913 [] := hInit ▸ hs.2.1.mono trivial
      obtain ⟨v, hv, hV⟩ := warmCounterSeedCore (l := l) (g := g) s hh
      have hv' : tauStep kernel [] l g s = some v := by simpa [run] using hv
      obtain rfl : v = u := Option.some.inj (hv'.symm.trans (tauStep_iff.mpr ht'))
      exact hV.2.2.2.2.1
    · exact (tau_core_regs hc ht' (hSeed.resolve_left hInit)).trans (hs.2.2 (by omega))
  · obtain ⟨_, hc, hL, _⟩ := estep_event_source he
    rw [(hCode hc).1] at hL
    cases hL

private theorem warmGateCore {l : Launch} {g n : Nat} (hn : n < 2 ^ 31) :
    Seg kernel [] l g 3 908 [(1088, b32 n), (1091, b32 (n - 1))] 911
      [(166, .pred (decide (n < 2))), (1091, b32 (n - 1))] := by
  have hSigned : toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left hn]
  have hTwo : toSigned 32 (truncBits 32 (BitVec.ofInt 64 2)) = 2 := rfl
  have hCmp : (n : Int) < 2 ↔ n < 2 := by omega
  intro s hs
  seg_fp hs using simp only [truncBits_ofNat (show n < 2 ^ 32 by omega) (by decide),
    compare, Option.getD_some, hSigned, hTwo, hCmp]

/-- The warm-path branch retains an audited register frame on either arm. -/
theorem loaderWarmGateWithFrame {l : Launch} {g n : Nat} (hn : n < 2 ^ 31)
    {s : TState} {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop 908).take 3).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 908 ([(1088, b32 n), (1091, b32 (n - 1))] ++ F)) :
    ∃ u, run kernel Assumptions.all l g 4 s = some u ∧
      At u (if n < 2 then 1353 else 912) ((1091, b32 (n - 1)) :: F) := by
  have ⟨hTrip, hF⟩ := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨v, hv, hV⟩ := warmGateCore (g := g) hn s (hs.mono hTrip)
  obtain ⟨hvA, hVFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
    hKeep (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hAt : At v 911 ((1091, b32 (n - 1)) :: F) := hV.mono
    ⟨hV.2.2.2.2.2.1, Epilogue.holdsSchedulerFrame hF hVFrame (fun _ hm => List.mem_map_of_mem hm)⟩
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_911 (decide (n < 2)) hAt hV.2.2.2.2.1 (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hV.1 (by simp) rfl hu
  exact ⟨u, run_comp hvA huA, by simpa using hU⟩

/-- The actual priming branch either skips the warm ring or reaches its live gate. -/
theorem loaderWarmGate {l : Launch} {g n : Nat} (hn : n < 2 ^ 31) {s : TState}
    (hs : At s 908 [(1088, b32 n), (1091, b32 (n - 1))]) :
    ∃ u, run kernel Assumptions.all l g 4 s = some u ∧
      At u (if n < 2 then 1353 else 912) [(1091, b32 (n - 1))] :=
  loaderWarmGateWithFrame hn (F := []) (by simp) hs

/-- At the real warm-path guard, any finite trace either bypasses the ring or pays
for at most nine iterations after the initializer. -/
theorem loaderWarmPrefixFromGate {l : Launch} {g n : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hn : n < 2 ^ 31) (hs : At s 908 [(1088, b32 n), (1091, b32 (n - 1))]) :
    loaderVisitsAt 1352 vs ≤ 54 := by
  obtain ⟨t, ht, hT⟩ := loaderWarmGate (g := g) hn hs
  rcases loaderLocalWalkCut ht hw with hShort | ⟨pre, tail, hTrace, hLen, hTail⟩
  · have h := loaderVisitsAt_le_length 1352 vs
    omega
  rw [hTrace]
  have h := loaderVisitsAt_le_append 1352 pre tail
  by_cases hsmall : n < 2
  · have hp : (ringCounterSite 0).branch < t.pc := by
      rw [show t.pc = 1353 by simpa [hsmall] using hT.1]
      decide
    have hd := noLaterRingBranchVisits 0 hTail hp
    change loaderVisitsAt 1352 tail = 0 at hd
    omega
  · have hAt : At t 912 [(1091, b32 (n - 1))] := by simpa [hsmall] using hT
    have hPc := hAt.1
    have hPrep : warmPrepare t (n - 1) :=
      ⟨hPc.ge, hPc.symm ▸ hAt, fun h => by omega⟩
    have hValid : 0 < counterLimit (0 : Fin 2) (n - 1) := by
      change 0 < min (n - 1) 9
      omega
    have hLoc : 174 ≤ t.pc ∧ t.pc ≤ (ringCounterSite 0).head := by rw [hPc]; decide
    have hRing := loaderRingPrefixWithEntry 0 hTail hLoc hPrep (budget := 9)
      (fun _ hi he hp => preserveWarmPrepare hp.1 hi he hp)
      (fun s hStart hS => ⟨0, n - 1, by omega, hValid, by
        change min (n - 1) 9 - 0 ≤ 9
        omega, by
          have hpc : s.pc = 917 := hStart
          have hArgs := hS.2.1
          exact ⟨hpc, hArgs.2.1, hArgs.2.2.1, hArgs.2.2.2.1,
            hS.2.2 (by omega), hArgs.2.2.2.2⟩⟩)
    change loaderVisitsAt 1352 tail ≤ 50 at hRing
    omega

private theorem beforeWarmCode :
    ((kernel.code.drop 481).take (908 - 481)).all
      (fun i => loaderPipelineCutOp 481 908 1352 [1088, 1091] i.op) = true := by
  set_option maxRecDepth 100000 in decide +kernel

/-- From the actual trip-count setup, the first K/V packet and the warm region
contribute at most 54 visits to the warm branch in any finite prefix. -/
theorem loaderWarmPrefixFromPriming {l : Launch} {g n : Nat} {s : TState} {es : List Event}
    {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hn : n < 2 ^ 31) (hs : At s 481 [(1088, b32 n), (1091, b32 (n - 1))]) :
    loaderVisitsAt 1352 vs ≤ 54 :=
  loaderPrefixThroughCheckpoint 0 (F := [(1088, b32 n), (1091, b32 (n - 1))])
    (lower := 481) (cut := 908) (by decide) (by decide) (by decide)
    ⟨_, Flow.code_908, rfl⟩ beforeWarmCode
    (fun ht hw => loaderWarmPrefixFromGate hw hn ht) hw
    (by rw [hs.1]; decide) (ringShapeOfAt hs) hs.2.2.2.2

end
end PTX.Kernels.TmlFa4Fwd.Loader
