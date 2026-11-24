-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaCommit
public import Kernels.TmlFa4Fwd.Proof.MmaElect

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

def commitElection : Fin 12 → Fin 20
  | 0 => 1
  | 1 => 3
  | 2 => 4
  | 3 => 7
  | 4 => 9
  | 5 => 11
  | 6 => 12
  | 7 => 13
  | 8 => 14
  | 9 => 17
  | 10 => 18
  | 11 => 19

private theorem gateSites (i : Fin 12) :
    (electSite (commitElection i)).pc + 3 = (commitSite i).pc ∧
      1904 ≤ (electSite (commitElection i)).pc + 1 ∧
      (electSite (commitElection i)).pc + 1 + 2 ≤ 2768 := by
  fin_cases i <;> decide

/-- The two decoded local instructions select the elected commit issuer. -/
theorem gateCode (i : Fin 12) :
    let es := electSite (commitElection i)
    let cs := commitSite i
    kernel.code[es.pc + 1]? = some ⟨none, .int {
      op := .not, ty := .pred, sat := false, dsts := [some (es.pred + 1)],
      srcs := [.reg es.pred] }⟩ ∧
    kernel.code[es.pc + 2]? = some ⟨some (es.pred + 1, false), .bra (cs.pc + 1) false⟩ := by
  fin_cases i
  · exact ⟨Flow.code_2206, Flow.code_2207⟩
  · exact ⟨Flow.code_2268, Flow.code_2269⟩
  · exact ⟨Flow.code_2272, Flow.code_2273⟩
  · exact ⟨Flow.code_2416, Flow.code_2417⟩
  · exact ⟨Flow.code_2460, Flow.code_2461⟩
  · exact ⟨Flow.code_2517, Flow.code_2518⟩
  · exact ⟨Flow.code_2521, Flow.code_2522⟩
  · exact ⟨Flow.code_2535, Flow.code_2536⟩
  · exact ⟨Flow.code_2539, Flow.code_2540⟩
  · exact ⟨Flow.code_2636, Flow.code_2637⟩
  · exact ⟨Flow.code_2640, Flow.code_2641⟩
  · exact ⟨Flow.code_2644, Flow.code_2645⟩

private theorem gateSegment (l : Launch) (g : Nat) (i : Fin 12) (lead : Bool) :
    let es := electSite (commitElection i)
    let cs := commitSite i
    Seg kernel [] l g 2 (es.pc + 1) [(es.pred, .pred lead)]
      (if lead then cs.pc else cs.pc + 1) [] := by
  dsimp only
  let es := electSite (commitElection i)
  let cs := commitSite i
  intro t ht
  let v := next (setReg t (es.pred + 1) (.pred (!lead)))
  have hAt : At t (es.pc + 1) [] := ht.mono trivial
  have hv : At v (es.pc + 2) [(es.pred + 1, .pred (!lead))] := hAt.set (by simp)
  have hReg : t.regs es.pred = some (.pred lead) := ht.2.2.2.2.1
  have hLocal : run kernel [] l g 1 t = some v := by
    apply run_local (gateCode i).1 rfl ht
    rw [execLocalA_nil, execLocal_int rfl]
    change execInt l g t ⟨.not, .pred, false, [some (es.pred + 1)], [.reg es.pred]⟩ = _
    simp [execInt, DType.width, readPred, readReg, hReg, v, bind, Except.bind, pure, Except.pure]
  obtain ⟨u, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    (gateCode i).2 (!lead) hv hv.2.2.2.2.1 (by simp)
  have hPc : es.pc + 2 + 1 = cs.pc := (gateSites i).1
  refine ⟨u, run_comp hLocal hw, ?_⟩
  have hEnd := hW.1
  change u.pc = (if !lead then cs.pc + 1 else es.pc + 2 + 1) at hEnd
  rw [hPc] at hEnd
  cases lead <;> exact ⟨hEnd, hW.2.1, hW.2.2.1, hW.2.2.2.1, trivial⟩

private theorem gateWrites (i : Fin 12) :
    let es := electSite (commitElection i)
    ((kernel.code.drop (es.pc + 1)).take 2).all
      (fun ins => (writesRegs ins.op).all (fun r => r == es.pred + 1)) = true := by
  set_option maxRecDepth 100000 in
  fin_cases i <;> kernel_rfl

private theorem gateStraight (i : Fin 12) :
    ((kernel.code.drop ((electSite (commitElection i)).pc + 1)).take 1).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
  fin_cases i <;> kernel_rfl

/-- The actual two-instruction post-election gate sends the leader to the commit and sends
all other lanes one instruction further, preserving its argument frame. -/
theorem commitGate {l : Launch} {g : Nat} (i : Fin 12) (lead : Bool)
    {t : TState} {F : List (Nat × Value)}
    (ht : At t ((electSite (commitElection i)).pc + 1)
      (((electSite (commitElection i)).pred, .pred lead) :: F))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (electSite (commitElection i)).pred + 1) :
    ∃ u, run kernel Assumptions.all l g 2 t = some u ∧
      At u (if lead then (commitSite i).pc else (commitSite i).pc + 1) F := by
  let es := electSite (commitElection i)
  have hPc : t.pc = es.pc + 1 := ht.1
  have ht' : At t (es.pc + 1) [(es.pred, .pred lead)] := ht.mono ⟨ht.2.2.2.2.1, trivial⟩
  obtain ⟨u, hLocal, hu⟩ := gateSegment l g i lead t ht'
  have hWrites : ((kernel.code.drop (es.pc + 1)).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    apply List.all_eq_true.mpr
    intro ins hi
    have hw := List.all_eq_true.mp (gateWrites i) ins hi
    apply List.all_eq_true.mpr
    intro r hr
    obtain ⟨pair, hm, rfl⟩ := List.mem_map.mp hr
    cases h : (writesRegs ins.op).contains pair.1
    · rfl
    · have he := List.all_eq_true.mp hw pair.1 (List.contains_iff_mem.mp h)
      exact (hFresh pair hm (beq_iff_eq.mp he)).elim
  have hFrame : ∀ r ∈ F.map Prod.fst, u.regs r = t.regs r := fun r hr =>
    schedulerLocalFrame (lo := es.pc + 1) (len := 2) hWrites (gateStraight i)
      hLocal hPc.ge (by rw [hPc]) hr
  have hHeld := holdsSchedulerFrame ht.2.2.2.2.2 hFrame (fun _ hm => List.mem_map_of_mem hm)
  have hRange := gateSites i
  exact ⟨u, localRun hRange.2.1 hRange.2.2 hPc (gateStraight i) hLocal, hu.mono hHeld⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
