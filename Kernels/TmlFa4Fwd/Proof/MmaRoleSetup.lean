-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaRoleCut
public import Kernels.TmlFa4Fwd.Proof.MmaScanCounter
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Kernels.TmlFa4Fwd.Proof.MmaStartup
public import Kernels.TmlFa4Fwd.Flow.Code.Part041

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue

noncomputable section

private theorem silentRegionCode (region : Fin 12) (hSilent : 8 ≤ region.val)
    {pc : Nat} {ins : Instr} (hLo : (roleRegion region).lo ≤ pc)
    (hHi : pc < (roleRegion region).hi) (hc : kernel.code[pc]? = some ins) :
    ins.op.isLocal = true ∧ schedulerFallsThrough ins.op = true := by
  let site := roleRegion region
  have hAll : ((kernel.code.drop site.lo).take (site.hi - site.lo)).all
      (fun i => i.op.isLocal && schedulerFallsThrough i.op) = true := by
    fin_cases region <;> (try norm_num at hSilent) <;>
      set_option maxRecDepth 100000 in kernel_rfl
  have hh : ((kernel.code.drop site.lo).take (site.hi - site.lo))[pc - site.lo]? = some ins := by
    have hLo' : site.lo ≤ pc := hLo
    have hHi' : pc < site.hi := hHi
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo']
    exact hc
  simpa only [Bool.and_eq_true] using List.all_eq_true.mp hAll ins (List.mem_of_getElem? hh)

private theorem silentRegionStep (region : Fin 12) (hSilent : 8 ≤ region.val)
    {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : (roleRegion region).lo ≤ s.pc) (hHi : s.pc < (roleRegion region).hi)
    (h : WStep kernel Assumptions.all l g s ev u) :
    Tau kernel Assumptions.all l g s u ∧ u.pc = s.pc + 1 := by
  rcases h with ⟨-, ht⟩ | ⟨e, -, he⟩
  · have hL : 1904 ≤ s.pc := by fin_cases region <;> simp [roleRegion] at hLo <;> omega
    have hH : s.pc < 2768 := by fin_cases region <;> simp [roleRegion] at hHi <;> omega
    have ht' : Tau kernel [] l g s u := by unfold Tau at ht ⊢; rwa [← out_eq_core hL hH]
    obtain ⟨i, hc⟩ := tau_core_has_code ht'
    have hCode := silentRegionCode region hSilent hLo hHi hc
    refine ⟨ht, ?_⟩
    rcases tau_core_frame hc ht' with rfl | hT
    · rfl
    · have hPc := hT.pc
      cases he : i.op <;> simp_all [schedulerFallsThrough, nextPc, BrxTarget]
  · obtain ⟨i, hc, hLoc, -⟩ := estep_event_source he
    rw [(silentRegionCode region hSilent hLo hHi hc).1] at hLoc
    cases hLoc

private theorem silentRegionCount (region : Fin 12) (hSilent : 8 ≤ region.val)
    {l : Launch} {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits) (hLo : (roleRegion region).lo ≤ s.pc) :
    countedUntil (roleRegion region).hi visits ≤ 1 := by
  induction hw with
  | stop => simp [countedUntil]
  | @tau s u es vs ht hw ih =>
    by_cases hHi : s.pc < (roleRegion region).hi
    · have hp := (silentRegionStep region hSilent hLo hHi (.inl ⟨rfl, ht⟩)).2
      have hCount := ih (by omega)
      simpa [countedUntil, visit_pc, visit_ev, List.filterMap_cons, hHi] using hCount
    · simp [countedUntil, visit_pc, hHi]
  | @ev s u e es vs he hw ih =>
    by_cases hHi : s.pc < (roleRegion region).hi
    · obtain ⟨i, hc, hLoc, -⟩ := estep_event_source he
      rw [(silentRegionCode region hSilent hLo hHi hc).1] at hLoc
      cases hLoc
    · simp [countedUntil, visit_pc, hHi]
  | @last s e he =>
    by_cases hHi : s.pc < (roleRegion region).hi
    · simpa [countedUntil, visit_pc, visit_ev, hHi] using
        (List.countP_le_length (p := Event.counts) (l := [e]))
    · simp [countedUntil, visit_pc, hHi]

/-- A silent role prefix either stops with at most one terminal event or executes
the whole known instruction span and yields its actual continuation. -/
theorem cutMmaSilent (region : Fin 12) (hSilent : 8 ≤ region.val)
    {l : Launch} {g : Nat} {s : TState} {events : List Event} {visits : List Visit}
    {P : TState → Prop} (hw : Walk kernel Assumptions.all l g s events visits)
    (hp : s.pc = (roleRegion region).lo) (hs : RoleShape s) (hInit : P s)
    (hStable : ∀ {v u : TState} {e : Option Event},
      (roleRegion region).lo ≤ v.pc → v.pc < (roleRegion region).hi →
      WStep kernel Assumptions.all l g v e u → P v → P u) :
    countedUntil 2768 visits ≤ 1 ∨
      ∃ u rest tail,
        run kernel Assumptions.all l g ((roleRegion region).hi - (roleRegion region).lo) s =
          some u ∧ u.pc = (roleRegion region).hi ∧ u.fault = none ∧ RoleShape u ∧ P u ∧
          Walk kernel Assumptions.all l g u rest tail ∧
          countedUntil 2768 visits ≤ 1 + countedUntil 2768 tail := by
  have hCount := silentRegionCount region hSilent hw hp.ge
  have hHi : (roleRegion region).lo < (roleRegion region).hi := by fin_cases region <;> decide
  let Q := fun u => run kernel Assumptions.all l g (u.pc - s.pc) s = some u ∧ s.pc ≤ u.pc ∧ P u
  have hStart : Q s := by simp [Q, run, hInit]
  have hKeep {v u : TState} {e : Option Event} (hLv : (roleRegion region).lo ≤ v.pc)
      (hHv : v.pc < (roleRegion region).hi) (hv : WStep kernel Assumptions.all l g v e u)
      (hvP : Q v) : Q u := by
    obtain ⟨hTau, hpc⟩ := silentRegionStep region hSilent hLv hHv hv
    have hRun : run kernel Assumptions.all l g 1 v = some u := by
      have hStep := tauStep_iff.mpr hTau
      simp [run, hStep]
    refine ⟨?_, by have := hvP.2.1; omega, hStable hLv hHv hv hvP.2.2⟩
    have hLen : u.pc - s.pc = (v.pc - s.pc) + 1 := by have := hvP.2.1; omega
    rw [hLen]
    exact run_comp hvP.1 hRun
  rcases cutMmaRegion region hw hp.ge (hp.symm ▸ hHi) hs hStart hKeep with h | h
  · exact .inl (h.trans hCount)
  · obtain ⟨u, rest, tail, he, hF, hS, huP, hW, hCut⟩ := h
    have hu : u.pc = (roleRegion region).hi := by
      fin_cases region <;> (try norm_num at hSilent) <;> simp [roleRegion] at he ⊢ <;> exact he
    exact .inr ⟨u, rest, tail, by simpa only [hp, hu] using huP.1,
      hu, hF, hS, huP.2.2, hW, by omega⟩

private theorem scanSetupCode (scan : GroupScan) :
    ∃ move, kernel.code[(scanSite scan).head - 1]? = some ⟨none, .move move⟩ ∧
      ∀ pair ∈ groupScanFacts scan 0 0 0, pair.1 ∉ writesRegs (.move move) := by
  cases scan
  · refine ⟨_, Flow.code_1987, ?_⟩
    decide
  · refine ⟨_, Flow.code_2695, ?_⟩
    decide
  · refine ⟨_, Flow.code_2823, ?_⟩
    decide
  · refine ⟨_, Flow.code_3031, ?_⟩
    decide
  · refine ⟨_, Flow.code_3157, ?_⟩
    decide
  · refine ⟨_, Flow.code_7665, ?_⟩
    decide
  · refine ⟨_, Flow.code_7809, ?_⟩
    decide
  · refine ⟨_, Flow.code_9132, ?_⟩
    decide
  · refine ⟨_, Flow.code_233, ?_⟩
    decide
  · refine ⟨_, Flow.code_1793, ?_⟩
    decide

/-- A successfully traversed group setup has initialized the clipped index and CTA sentinel.
The work accumulator loaded by the setup may be any valid word. -/
theorem groupInitFromRun {l : Launch} {g batch cta : Nat} (scan : GroupScan) {s u : TState}
    (hCta : cta + 1 < 2 ^ 31)
    (hs : At s ((scanSite scan).head - 3)
      [((scanSite scan).cta, b32 cta), ((scanSite scan).batch, b32 batch)])
    (hr : run kernel Assumptions.all l g 3 s = some u) :
    At u (scanSite scan).head (groupScanFacts scan 0 batch cta) := by
  let site := scanSite scan
  have hSeg : Seg kernel [] l g 2 (site.head - 3) [(site.cta, b32 cta), (site.batch, b32 batch)]
      (site.head - 1) (groupScanFacts scan 0 batch cta) := by
    cases scan <;> dsimp only [site, scanSite, groupScanFacts] <;> intro t ht <;>
      seg_fp ht using norm_bits
  obtain ⟨v, hv, hV⟩ := hSeg s hs
  have hStraight : ((kernel.code.drop (site.head - 3)).take 1).all
      (fun i => schedulerFallsThrough i.op) = true := by
    cases scan <;> set_option maxRecDepth 100000 in kernel_rfl
  have hv' := groupScanLocalRun scan (by cases scan <;> decide) (by cases scan <;> decide)
    hs.1 hStraight hv
  have hu : run kernel Assumptions.all l g 1 v = some u := by
    rw [show 3 = 2 + 1 by decide, run_add, hv', Option.bind_some] at hr
    exact hr
  have ht : Tau kernel [] l g v u := by
    unfold Tau
    have hLo : site.head - 3 ≤ v.pc := by rw [hV.1]; cases scan <;> decide
    have hHi : v.pc < site.compare + 3 := by rw [hV.1]; cases scan <;> decide
    rw [← groupScanOut scan hLo hHi, ← Tau]
    apply tauStep_iff.mp
    unfold run at hu
    cases h : tauStep kernel Assumptions.all l g v <;> simp_all [run]
  obtain ⟨move, hc, hKeep⟩ := scanSetupCode scan
  have hc' : kernel.code[v.pc]? = some ⟨none, .move move⟩ := by rw [hV.1]; exact hc
  have hRegs : Holds u.regs (groupScanFacts scan 0 batch cta) := by
    apply holdsSchedulerFrame (regs := (groupScanFacts scan 0 0 0).map Prod.fst) hV.2.2.2.2
    · intro r hr
      obtain ⟨pair, hPair, rfl⟩ := List.mem_map.mp hr
      exact tau_core_regs hc' ht (hKeep pair hPair)
    · intro pair hm
      have h := List.mem_map_of_mem (f := Prod.fst) hm
      simpa only [groupScanFacts, List.map_cons, List.map_nil] using h
  have hvpc : v.pc + 1 = site.head := by rw [hV.1]; cases scan <;> decide
  rcases tau_core_frame hc' ht with rfl | hT
  · exact ⟨hvpc, rfl, rfl, hV.2.2.2.1, hRegs⟩
  · exact ⟨(hT.pc.resolve_right id).trans hvpc, hT.sub.trans hV.2.1,
      hT.acc.trans hV.2.2.1, hT.fault.trans hV.2.2.2.1, hRegs⟩

/-- The drain reads the same batch ABI word as the initial request search. -/
theorem drainBatchFromRun {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g cta : Nat} {s u : TState} (hs : At s 2647 [(1072, b32 cta)])
    (hr : run kernel Assumptions.all l g 1 s = some u) :
    At u 2648 [(7149, b32 p.batch), (1072, b32 cta)] := by
  let r := next (setReg s 7149 (b32 p.batch))
  obtain ⟨hBound, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [param19_name] at hParam
  have hRun : run kernel [] l g 1 s = some r := by
    apply run_local Flow.code_2647 rfl hs
    rw [execLocalA_nil, execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hParam,
      DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hBound (by decide)]
    rfl
  have hActual := localRun (by decide) (by decide) hs.1 rfl hRun
  rw [hr] at hActual
  obtain rfl := Option.some.inj hActual
  exact hs.set (by
    intro pair h
    rcases List.mem_singleton.mp h with rfl
    exact of_decide_eq_true rfl)

end
end PTX.Kernels.TmlFa4Fwd.Mma
