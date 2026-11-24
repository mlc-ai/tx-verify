-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseAddress
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

theorem lseTailLinear {l : Launch} {g pc n : Nat} {t u : TState} {regs : List Nat}
    (hLo : 9057 ≤ pc) (ht : t.pc = pc)
    (hCore : ((kernel.code.drop pc).take n).all (fun ins => Assumptions.coreOp ins.op) = true)
    (hWrites : ((kernel.code.drop pc).take n).all
      (fun ins => regs.all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hStraight : ((kernel.code.drop pc).take (n - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true)
    (hRun : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧
      ∀ r ∈ regs, u.regs r = t.regs r := by
  refine ⟨schedulerLocalTransport hStraight ?_ hRun ht.ge (by rw [ht]),
    fun _ hm => schedulerLocalFrame hWrites hStraight hRun ht.ge (by rw [ht]) hm⟩
  intro s hlo hhi
  cases hc : kernel.code[s.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop pc).take n := by
      apply List.mem_of_getElem? (i := s.pc - pc)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp hCore _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

variable {p : Params} {l : Launch} {m : Mem0}

/-- The local instructions prepare the packed address and signed guard. -/
theorem prepareFirstLseTail {g tile batch head : Nat} {t : TState} {F : List (Nat × Value)}
    (hp : Pre p l m) (hBatch : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    (value : Value)
    (ht : At t 9065
      ([(1635, b32 (p.qLength batch)), (5967, b32 (256 * tile)), (1613, b32 (rowOf l g)),
       (9525, b64 (p.lseLoc (p.qOffset batch) head).addr), (1655, value)] ++ F))
    (hKeep0 : ((kernel.code.drop 9065).take 2).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true)
    (hKeep1 : ((kernel.code.drop 9067).take 5).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true) :
    ∃ u, At u (lseGuardPc 0)
      ((lseOutReg 0, value) ::
        (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr) ::
        ([(7077, b32 (p.qLength batch - 256 * tile)), (1613, b32 (rowOf l g)),
        (7491, b64 (p.lseLoc (p.qOffset batch + 256 * tile + rowOf l g) head).addr)] ++ F)) ∧
      u.regs (lseTailPred 0) = some
        (.pred (decide (p.qLength batch ≤ stageRow tile 0 + rowOf l g))) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  have hLength : p.qLength batch < 2 ^ 31 := by
    have h := hp.qLength_fits hBatch
    omega
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  obtain ⟨s, hs, hS⟩ := lseFirstTail (l := l) (g := g) hLength hTile hRow t
    (ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, trivial⟩)
  obtain ⟨hsAll, hFrame⟩ := lseTailLinear (regs := [9525, 1655]) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hs
  have hBase : s.regs 9525 = some (b64 (p.lseLoc (p.qOffset batch) head).addr) :=
    (hFrame _ (by simp)).trans ht.2.2.2.2.2.2.2.1
  have hVal : s.regs 1655 = some value :=
    (hFrame _ (by simp)).trans ht.2.2.2.2.2.2.2.2.1
  obtain ⟨v, hv, hV⟩ := lseRowAddress (by omega) hRow s
    (hS.mono ⟨hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, hBase, trivial⟩)
  obtain ⟨hvAll, hCarry⟩ := lseTailLinear (regs := [741, 7077, 1613, 1655]) (by decide) hS.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hTest : v.regs 741 = some (.pred (decide (p.qLength batch ≤ 256 * tile + rowOf l g))) :=
    (hCarry _ (by simp)).trans hS.2.2.2.2.1
  have hRemain : v.regs 7077 = some (b32 (p.qLength batch - 256 * tile)) :=
    (hCarry _ (by simp)).trans hS.2.2.2.2.2.1
  have hRowReg : v.regs 1613 = some (b32 (rowOf l g)) :=
    (hCarry _ (by simp)).trans hS.2.2.2.2.2.2.2.1
  have hStart : Holds t.regs F := ht.2.2.2.2.2.2.2.2.2
  have hFall0 : ((kernel.code.drop 9065).take 1).all
      (fun i => schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hFall1 : ((kernel.code.drop 9067).take 4).all
      (fun i => schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSave : Holds v.regs F := by
    apply holdsSchedulerFrame hStart
    · intro r hm
      exact (schedulerLocalFrame (lo := 9067) (len := 5) hKeep1 hFall1 hv hS.1.ge
        (by rw [hS.1]) hm).trans
        (schedulerLocalFrame (lo := 9065) (len := 2) hKeep0 hFall0 hs ht.1.ge (by rw [ht.1]) hm)
    · exact fun _ hm => List.mem_map_of_mem hm
  have hAt : At v (lseGuardPc 0)
      ([(1655, value),
       (7491, b64 (p.lseLoc (p.qOffset batch + 256 * tile + rowOf l g) head).addr),
       (7077, b32 (p.qLength batch - 256 * tile)), (1613, b32 (rowOf l g)),
       (7491, b64 (p.lseLoc (p.qOffset batch + 256 * tile + rowOf l g) head).addr)] ++ F) :=
    hV.mono ⟨(hCarry _ (by simp)).trans hVal, hV.2.2.2.2.1, hRemain, hRowReg,
      hV.2.2.2.2.1, hSave⟩
  exact ⟨v,hAt,by simpa [stageRow,lseTailPred] using hTest,run_rtg (run_comp hsAll hvAll)⟩

/-- The local instructions prepare the packed address and signed guard. -/
theorem prepareSecondLseTail {g tile batch head : Nat} {t : TState} {F : List (Nat × Value)}
    (hp : Pre p l m) (hBatch : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    (value : Value)
    (ht : At t 9079
      ([(7077, b32 (p.qLength batch - 256 * tile)), (1613, b32 (rowOf l g)),
       (7491, b64 (p.lseLoc (p.qOffset batch + 256 * tile + rowOf l g) head).addr),
       (1656, value)] ++ F))
    (hKeep : ((kernel.code.drop 9079).take 2).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true) :
    ∃ u, At u (lseGuardPc 1)
      ((lseOutReg 1, value) ::
        (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr) ::
        (F)) ∧
      u.regs (lseTailPred 1) = some
        (.pred (decide (p.qLength batch ≤ stageRow tile 1 + rowOf l g))) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  have hLength : p.qLength batch < 2 ^ 31 := by
    have h := hp.qLength_fits hBatch
    omega
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  obtain ⟨s, hs, hS⟩ := lseSecondTail (l := l) (g := g) hLength hTile hRow t
    (ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩)
  obtain ⟨hsAll, hFrame⟩ := lseTailLinear (regs := [7491, 1656]) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hs
  have hBase : s.regs 7491 = some (b64
      (p.lseLoc (p.qOffset batch + 256 * tile + rowOf l g) head).addr) :=
    (hFrame _ (by simp)).trans ht.2.2.2.2.2.2.1
  have hVal : s.regs 1656 = some value :=
    (hFrame _ (by simp)).trans ht.2.2.2.2.2.2.2.1
  have hFall : ((kernel.code.drop 9079).take 1).all
      (fun i => schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSave : Holds s.regs F := holdsSchedulerFrame ht.2.2.2.2.2.2.2.2
    (fun _ hm => schedulerLocalFrame (lo := 9079) (len := 2) hKeep hFall hs ht.1.ge
      (by rw [ht.1]) hm) (fun _ hm => List.mem_map_of_mem hm)
  have hAt : At s (lseGuardPc 1)
      ((lseOutReg 1, value) ::
        (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr) :: F) :=
    hS.mono ⟨hVal, hBase, hSave⟩
  exact ⟨s,hAt,by simpa [stageRow,lseTailPred] using hS.2.2.2.2.1,run_rtg hsAll⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
