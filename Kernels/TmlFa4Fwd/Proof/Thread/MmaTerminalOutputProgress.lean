-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalPvProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.TerminalProbabilityGate
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCommitProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow PTX.Assumption Epilogue Prologue

private def terminalSite (n : Fin 3) : Fin 12 := ⟨n.val+9,by omega⟩

private def terminalBase (l : Launch) (n : Fin 3) : Nat :=
  if n = 0 then l.sharedBase+8 else if n = 1 then l.sharedBase+144 else l.sharedBase

private theorem terminalCommitStep {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (n : Fin 3)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (electSite (commitElection (terminalSite n))).pc
      (fun _ => terminalPvFrame l) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g ((commitSite (terminalSite n)).pc+1)
      (fun _ => terminalPvFrame l) shuffles votes ends) ∧
    ∃ issuer index, SameWarp l g issuer ∧ X.get (issuer,index) =
      some ⟨(commitSite (terminalSite n)).pc,.tc (.commit
        (commitSpec l issuer (terminalBase l n+(commitSite (terminalSite n)).off)))⟩ := by
  let site := terminalSite n
  let e := electSite (commitElection site)
  have hCode : kernel.code[e.pc]? = some
      ⟨none,.warp ⟨.elect,none,[e.result,some e.pred],[],some (.imm (-1))⟩⟩ := by
    fin_cases n
    · exact Flow.code_2635
    · exact Flow.code_2639
    · exact Flow.code_2643
  have hTail : (kernel.code.drop (e.pc+1)).all
      (fun ins => Thread.staysPastEvent (e.pc+1) ins.op) = true := by
    set_option maxRecDepth 100000 in
    fin_cases n <;> kernel_rfl
  have hSegments : Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some seg => decide (e.pc+1 ≤ seg.stop)
      | none => false) = true := by
    fin_cases n <;> kernel_rfl
  have hRegs : ∀ r ∈ (terminalPvFrame l).map Prod.fst,
      r ≠ e.pred ∧ r ≠ e.pred+1 ∧ r ∉ e.result.toList := by
    simp only [terminalPvFrame,List.map]
    fin_cases n <;> decide
  apply commitWarpFromFreshElection hp hMax hg site cur (base := terminalBase l n)
    (fun lane hl _ hj _ _ _ he => noEarlierMmaElection (commitElection site) hCode hTail
      hSegments (cur.checkpoint lane hl) (cur.recorded lane hl) (cur.localSteps lane hl) hj he)
    (fun pair h => (hRegs _ (List.mem_map_of_mem (f := Prod.fst) h)).1)
    (fun pair h => (hRegs _ (List.mem_map_of_mem (f := Prod.fst) h)).2.1)
    (fun pair h => (hRegs _ (List.mem_map_of_mem (f := Prod.fst) h)).2.2)
  · fin_cases n <;> simp [site,terminalSite,terminalBase,commitSite,terminalPvFrame]
  · have hBound := hp.shared.2.1
    fin_cases n <;> simp only [site,terminalSite,terminalBase,commitSite] <;>
      first | exact (by change l.sharedBase+8+56 < 2^32; omega)
            | exact (by change l.sharedBase+144+0 < 2^32; omega)
            | exact (by change l.sharedBase+152 < 2^32; omega)
  · have hAligned := hp.shared.1
    fin_cases n <;> simp only [site,terminalSite,terminalBase,commitSite] <;>
      first | exact (by change (l.sharedBase+8+56)%8 = 0; omega)
            | exact (by change (l.sharedBase+144+0)%8 = 0; omega)
            | exact (by change (l.sharedBase+152)%8 = 0; omega)

/-- Both output commits were issued by the selected MMA warp to their completion objects. -/
def TerminalOutputIssues (l : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ stage : Fin 2, ∃ issuer index, SameWarp l g issuer ∧
    Thread.Scores.TerminalOutputCommit X stage (issuer,index)
      (commitSpec l issuer (l.sharedBase+(144+8*stage.val)))

/-- The final V-empty release and the two stage output commits follow the terminal PV packets. -/
theorem terminalOutputCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2635 (fun _ => terminalPvFrame l) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 2647 (fun _ => terminalPvFrame l)
      shuffles votes ends) ∧ TerminalOutputIssues l X g := by
  obtain ⟨⟨a⟩,_⟩ := terminalCommitStep hp hMax hg 0 cur
  obtain ⟨⟨b⟩,i₀,j₀,hw₀,h₀⟩ := terminalCommitStep hp hMax hg 1 a
  obtain ⟨last,i₁,j₁,hw₁,h₁⟩ := terminalCommitStep hp hMax hg 2 b
  refine ⟨last,?_⟩
  intro stage
  fin_cases stage
  · exact ⟨i₀,j₀,hw₀,h₀⟩
  · let s := commitSpec l i₁ (l.sharedBase+152)
    have hs : TcCommit.target s 0 = some (Thread.outputCompletionObject l (i₁/l.block) 1) :=
      by simp [s,TcCommit.target,commitSpec,Thread.outputCompletionObject]
    rcases Thread.outputCommitOfTarget hp hMax.1 1 (⟨2646,h₁⟩ : X.Commit (i₁,j₁) s) hs
      with wrong | right
    · change X.get (i₁,j₁) = some ⟨2642,.tc (.commit s)⟩ at wrong
      rw [h₁] at wrong
      cases wrong
    · exact ⟨i₁,j₁,hw₁,right⟩

/-- Both actual terminal output commits issue from the returned PV cursor. -/
theorem terminalOutputIssuesOfCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2635 (fun _ => terminalPvFrame l) shuffles votes ends) :
    TerminalOutputIssues l X g :=
  (terminalOutputCursor hp hMax hg cur).2

end PTX.Kernels.TmlFa4Fwd.Mma
