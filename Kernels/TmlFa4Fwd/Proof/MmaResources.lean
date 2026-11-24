-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Lemmas.Flow.Resource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

noncomputable section

private def countPc (alloc : Bool) : Nat := if alloc then 1909 else 2766

private def countReg (alloc : Bool) : Nat := if alloc then 2451 else 2682

private def countMove (alloc : Bool) : Op :=
  .move ⟨.scalar, .int .b 32, [some (countReg alloc)], [.imm 512]⟩

private def countOp (alloc : Bool) : Op :=
  if alloc then .tcAlloc .one 2535 312 (.reg (countReg alloc))
  else .tcDealloc .one (.reg 1179) (.reg (countReg alloc))

private theorem countMoveCode (alloc : Bool) :
    kernel.code[countPc alloc - 1]? = some ⟨none, countMove alloc⟩ := by
  cases alloc
  · exact Flow.code_2765
  · exact Flow.code_1908

private theorem countOpCode (alloc : Bool) :
    kernel.code[countPc alloc]? = some ⟨none, countOp alloc⟩ := by
  cases alloc
  · exact Flow.code_2766
  · exact Flow.code_1909

private theorem columnNoTarget (alloc : Bool) : kernel.branchTarget (countPc alloc) = false := by
  cases alloc <;> decide +kernel

private theorem columnNoSegment (alloc : Bool) :
    Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | none => false | some s => s.stop != countPc alloc) = true := by
  cases alloc <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem returningEventsCode :
    kernel.code.all (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) = true := by
  decide +kernel

private def ColumnFact (alloc : Bool) (s : TState) : Prop :=
  s.pc = countPc alloc → s.regs (countReg alloc) = some (b32 512)

private theorem tauColumnFact {l : Launch} {g : Nat} {s u : TState} (alloc : Bool)
    (ht : Tau kernel Assumptions.all l g s u) : ColumnFact alloc u := by
  intro hu
  obtain ⟨i, hc, _, hSource⟩ := Softmax.tauScoreSource ht
  rcases hSource with ⟨rfl, hGuard⟩ | ⟨_, _, hExec⟩
  · have hPre : s.pc = countPc alloc - 1 := by change s.pc + 1 = _ at hu; omega
    rw [hPre, countMoveCode alloc] at hc
    obtain rfl := Option.some.inj hc.symm
    cases hGuard
  · rcases Softmax.scoreExecLocal hExec with hCore | ⟨m, hSite, hm, hRun⟩
    · have hNext := LocalFrame.pc_succ hc hCore (hu.symm ▸ columnNoTarget alloc)
      have hPre : s.pc = countPc alloc - 1 := by omega
      rw [hPre, countMoveCode alloc] at hc
      obtain rfl := Option.some.inj hc.symm
      have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPre]; cases alloc <;> decide
      rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl,
        execLocalA_nil] at hExec
      have hModel : execLocal l g s (countMove alloc) =
          .ok (next (setReg s (countReg alloc) (b32 512))) := by cases alloc <;> rfl
      rw [hModel] at hExec
      obtain rfl := Except.ok.inj hExec
      simp [next, setReg]
    · have hNo := List.all_eq_true.mp (columnNoSegment alloc) _ hSite
      rw [hm] at hNo
      have hP := (Softmax.scoreSegmentFrame hRun).1
      simp [hP.symm.trans hu] at hNo

private theorem eventColumnFact {l : Launch} {g : Nat} {s u : TState} {e : Event} (alloc : Bool)
    (hs : ColumnFact alloc s) (he : EStep kernel Assumptions.all l g s e (some u)) :
    ColumnFact alloc u := by
  intro hu
  obtain ⟨i, hc, hLocal, hF⟩ := estep_event_source he
  have hOp := List.all_eq_true.mp returningEventsCode _ (List.mem_of_getElem? hc)
  have hFrame := Epilogue.ordinaryEventFrame (by simpa only [hLocal, Bool.false_or] using hOp)
    (A := Assumptions.all) (l := l) (g := g) (s := s)
  rcases callbackFrame_fires hFrame hF with hh | hh
  · have hP : s.pc = countPc alloc := hh.symm.trans hu
    have hc' := hc
    rw [hP, countOpCode alloc] at hc'
    have hI := congrArg Instr.op (Option.some.inj hc').symm
    have hRegs : u.regs (countReg alloc) = s.regs (countReg alloc) := by
      apply mmaEventRegs hc
      · rw [hI]
        cases alloc <;> rfl
      · rw [hI]
        cases alloc <;> decide
      · exact he
    exact hRegs.trans (hs hP)
  · have hP : s.pc = countPc alloc - 1 := by omega
    rw [hP, countMoveCode alloc] at hc
    obtain rfl := Option.some.inj hc.symm
    cases alloc <;> contradiction

private theorem localColumnFacts {l : Launch} {g : Nat} {s u : TState} (alloc : Bool)
    (hs : ColumnFact alloc s) (ht : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) :
    ColumnFact alloc u := by
  induction ht with
  | refl => exact hs
  | tail _ ht _ => exact tauColumnFact alloc ht

private theorem resourceCountRun {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {o : Option TState} (alloc : Bool) (hs : ColumnFact alloc s)
    (hr : Run kernel Assumptions.all l g s es o) :
    ∀ e ∈ es, (∀ fault, e.kind ≠ .ub fault) → e.pc = countPc alloc →
      ∃ (t : TState) (ins : Instr) (next : Option TState),
      t.regs (countReg alloc) = some (b32 512) ∧ ins.op = countOp alloc ∧
        Fires e.pc (eventTmpl Assumptions.all l g t ins.op) e next := by
  have hHere {t : TState} {e : Event} {next : Option TState}
      (ht : ColumnFact alloc t) (hc : e.pc = countPc alloc)
      (he : EStep kernel Assumptions.all l g t e next)
      (hE : ∃ i, kernel.code[t.pc]? = some i ∧
        Fires t.pc (eventTmpl Assumptions.all l g t i.op) e next) :
      ∃ (z : TState) (i : Instr) (u : Option TState),
        z.regs (countReg alloc) = some (b32 512) ∧ i.op = countOp alloc ∧
          Fires e.pc (eventTmpl Assumptions.all l g z i.op) e u := by
    have hPc := (estep_source_pc he).symm.trans hc
    obtain ⟨i, hi, hf⟩ := hE
    rw [hPc, countOpCode alloc] at hi
    exact ⟨t, i, next, ht hPc, congrArg Instr.op (Option.some.inj hi).symm, by
      rwa [estep_source_pc he]⟩
  -- A non-UB resource event must come from the decoded instruction, even at the end of a prefix.
  have hRead {t : TState} {e : Event} {next : Option TState}
      (he : EStep kernel Assumptions.all l g t e next)
      (hNo : ∀ fault, e.kind ≠ .ub fault) :
      ∃ i, kernel.code[t.pc]? = some i ∧
        Fires t.pc (eventTmpl Assumptions.all l g t i.op) e next := by
    obtain ⟨tmpl, hout, hf⟩ := he
    rcases out_ev hout with ⟨f, rfl⟩ | ⟨i, hi, rfl⟩
    · exact (hNo f (congrArg Event.kind hf.1)).elim
    · exact ⟨i, hi, hf⟩
  induction hr with
  | nil => simp
  | step hl he hTail ih =>
    intro e hMem hNo hPc
    rcases List.mem_cons.mp hMem with rfl | hMem
    · exact hHere (localColumnFacts alloc hs hl) hPc he (hRead he hNo)
    · exact ih (eventColumnFact alloc (localColumnFacts alloc hs hl) he) e hMem hNo hPc
  | last hl he =>
    intro e hm hNo hp
    obtain rfl := List.mem_singleton.mp hm
    exact hHere (localColumnFacts alloc hs hl) hp he (hRead he hNo)

private def resourceSites : List Nat := [1909, 2763, 2766]

private theorem resourceSitesCode : OpPcsFast kernel.code tmemOp resourceSites = true := by
  decide +kernel

private theorem columnsAtRequest {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (alloc : Bool) {i : EvId}
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (h : X.get i = some ⟨countPc alloc, .tc (.resource grp dst act)⟩) :
    ∃ t out, readBits l i.1 t 32 (.reg (countReg alloc)) = .ok 512#64 ∧
      Fires (countPc alloc) (eventTmpl Assumptions.all l i.1 t (countOp alloc))
        ⟨countPc alloc, .tc (.resource grp dst act)⟩ out := by
  have hg := event_thread_lt hX h
  obtain ⟨_, hr⟩ := hX.thr i.1 hg
  obtain ⟨t, ins, o, hReg, hOp, hf⟩ := resourceCountRun alloc (s := ({} : TState))
    (by intro h; cases alloc <;> cases h) hr _ (List.mem_of_getElem? h) (by intro _ h; cases h) rfl
  rw [hOp] at hf
  exact ⟨t, o, by rw [readBits_b32' hReg]; rfl, hf⟩

/-- Exact site, qualifier and size of every allocator request in a consistent prefix. -/
theorem actualResourceRequest {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {pc : Nat}
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (h : X.get i = some ⟨pc, .tc (.resource grp dst act)⟩) :
    grp = .one ∧ ((pc = 1909 ∧ act = .alloc 512) ∨
      (pc = 2763 ∧ act = .relinquish) ∨ (pc = 2766 ∧ ∃ base, act = .dealloc base 512)) := by
  rcases get_source hX h with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hf
  have hSite := OpPcsFast.mem resourceSitesCode hc (fires_resource_op hf rfl)
  simp only [resourceSites, List.mem_cons, List.not_mem_nil, or_false] at hSite
  rcases hSite with hP | hP | hP <;> subst pc
  · obtain ⟨t, o, hCount, hFire⟩ := columnsAtRequest hX true h
    obtain ⟨_, hGroup, n, hRead, hAct⟩ := fires_tcAlloc_resource hFire rfl
    rw [hCount] at hRead
    obtain rfl := Except.ok.inj hRead.symm
    exact ⟨hGroup, .inl ⟨rfl, hAct⟩⟩
  · rw [Flow.code_2763] at hc
    obtain rfl := Option.some.inj hc.symm
    obtain ⟨hGroup, _, hAct⟩ := fires_tcRelinquish_resource hf rfl
    exact ⟨hGroup, .inr (.inl ⟨rfl, hAct⟩)⟩
  · obtain ⟨t, o, hCount, hFire⟩ := columnsAtRequest hX false h
    obtain ⟨hGroup, _, n, a, hRead, hAct⟩ := fires_tcDealloc_resource hFire rfl
    rw [hCount] at hRead
    obtain rfl := Except.ok.inj hRead.symm
    exact ⟨hGroup, .inr (.inr ⟨rfl, a, hAct⟩)⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
