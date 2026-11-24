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
public import Lemmas.Flow.MarkedCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

/-- Indicator for a decoded barrier site that must still fire before the next cut. -/
def barrierRemaining (pc : Nat) (s : TState) : Nat := if s.pc ≤ pc then 1 else 0

/-- A decoded event marker for a particular barrier instruction. -/
def barrierMark (pc : Nat) (e : Event) : Bool := e.pc == pc

private theorem barNotLocal {op : Op} (h : barOp op = true) : op.isLocal = false := by
  cases op <;> simp only [barOp, Bool.false_eq_true] at h
  all_goals rfl

/-- A named-barrier return fires a barrier event and advances past its instruction. -/
theorem markedBarrierContinues {l : Launch} {g pc : Nat} {s u : TState} {e : Event}
    {ins : Instr} (hs : s.pc = pc) (hc : kernel.code[pc]? = some ins)
    (hOp : barOp ins.op = true) (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc+1 ∧ ∃ id count mode, e.kind = .bar id count mode := by
  obtain ⟨i, hCode, _, hFire⟩ := estep_event_source he
  rw [hs, hc] at hCode
  obtain rfl := Option.some.inj hCode
  cases ho : ins.op <;> simp only [ho, barOp, Bool.false_eq_true] at hOp
  all_goals
    simp only [ho, eventTmpl] at hFire
    unfold barTmpl at hFire
    repeat' split at hFire
    all_goals first
      | exact ⟨congrArg TState.pc (Option.some.inj hFire.2),
          _, _, _, congrArg Event.kind hFire.1⟩
      | cases hFire.2

/-- A named-barrier return advances past its decoded instruction. -/
theorem followsMarkedBarrier {l : Launch} {g pc : Nat} {s u : TState} {e : Event}
    {ins : Instr} (hs : s.pc = pc) (hc : kernel.code[pc]? = some ins)
    (hOp : barOp ins.op = true) (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.pc = s.pc+1 :=
  (markedBarrierContinues hs hc hOp he).1

private theorem ordinaryEvents :
    kernel.code.all (fun ins => ins.op.isLocal || Epilogue.ordinaryEvent ins.op) = true := by
  decide +kernel

variable {l : Launch}

/-- The local control certificates establish that the dispatch at this marked PC is the
only step that crosses its instruction address. This turns actual events into an exact count. -/
theorem markedEventTransition {g pc : Nat} {s u : TState} {ev : Option Event}
    (hMark : ∃ ins, kernel.code[pc]? = some ins ∧ ins.guard = none ∧ ins.op.isLocal = false)
    (hReturn : s.pc = pc → ∀ {e}, EStep kernel Assumptions.all l g s e (some u) → u.pc = s.pc+1)
    (hBranch : ∀ {ins dest uni}, kernel.code[s.pc]? = some ins → ins.op = .bra dest uni →
      (s.pc ≤ pc ↔ dest ≤ pc))
    (hIndirect : ∀ {ins index ds uni}, kernel.code[s.pc]? = some ins → ins.op ≠ .brx index ds uni)
    (hSeg : ∀ m, s.pc ∈ Assumptions.swExp2Sites → cuteExp2.matchAt kernel s.pc = some m →
      (s.pc ≤ pc ↔ m.stop ≤ pc)) (hStep : WStep kernel Assumptions.all l g s ev u) :
    barrierRemaining pc s = ev.toList.countP (barrierMark pc) + barrierRemaining pc u := by
  obtain ⟨ins', hi, hGuard, hNonlocal⟩ := hMark
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · obtain ⟨ins, hc, _, hExec⟩ := Softmax.tauScoreSource ht
    have hNe : s.pc ≠ pc := by
      intro h
      rw [h, hi] at hc
      obtain rfl := Option.some.inj hc.symm
      rcases hExec with ⟨_, hG⟩ | ⟨_, hL, _⟩
      · rw [hGuard] at hG
        cases hG
      · rw [hNonlocal] at hL
        cases hL
    have hKeep (hPc : u.pc = s.pc+1) :
        barrierRemaining pc s = barrierRemaining pc u := by
      have hEq : s.pc ≤ pc ↔ u.pc ≤ pc := by omega
      simp only [barrierRemaining, hEq]
    simp only [Option.toList_none, List.countP_nil, Nat.zero_add]
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hL⟩
    · exact hKeep rfl
    · rcases Softmax.scoreExecLocal hL with hF | ⟨m, hSite, hm, hRun⟩
      · have hp := hF.pc
        cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hp
        case bra dst uni => simp only [barrierRemaining, hp, hBranch hc ho]
        case brx => exact (hIndirect hc ho).elim
        all_goals exact hKeep hp
      · have hp := (Softmax.scoreSegmentFrame hRun).1
        simp only [barrierRemaining, hp, hSeg m hSite hm]
  · have hp := estep_source_pc he
    by_cases h : s.pc = pc
    · have hNext := hReturn h he
      simp [barrierRemaining, barrierMark, h, hp, hNext]
    · have hFalse : barrierMark pc e = false := by simp [barrierMark, hp, h]
      obtain ⟨ins, hc, ht, hf⟩ := estep_event_source he
      have hOp := List.all_eq_true.mp ordinaryEvents _ (List.mem_of_getElem? hc)
      have hF := Epilogue.ordinaryEventFrame
        (A := Assumptions.all) (l := l) (g := g) (s := s)
        (by simpa only [ht, Bool.false_or] using hOp)
      have hProgress := callbackFrame_fires hF hf
      have hEq : s.pc ≤ pc ↔ u.pc ≤ pc := by rcases hProgress with h | h <;> omega
      simp [barrierRemaining, hEq, hFalse]

/-- Count a marked barrier when only firing it can cross its station. -/
theorem markedBarrierTransition {g pc : Nat} {s u : TState} {ev : Option Event}
    (hMark : ∃ ins, kernel.code[pc]? = some ins ∧ ins.guard = none ∧ barOp ins.op = true)
    (hBranch : ∀ {ins dest uni}, kernel.code[s.pc]? = some ins → ins.op = .bra dest uni →
      (s.pc ≤ pc ↔ dest ≤ pc))
    (hIndirect : ∀ {ins index ds uni}, kernel.code[s.pc]? = some ins → ins.op ≠ .brx index ds uni)
    (hSeg : ∀ m, s.pc ∈ Assumptions.swExp2Sites → cuteExp2.matchAt kernel s.pc = some m →
      (s.pc ≤ pc ↔ m.stop ≤ pc)) (hStep : WStep kernel Assumptions.all l g s ev u) :
    barrierRemaining pc s = ev.toList.countP (barrierMark pc) + barrierRemaining pc u := by
  obtain ⟨ins, hc, hg, ho⟩ := hMark
  exact markedEventTransition ⟨ins, hc, hg, barNotLocal ho⟩
    (fun hs {_} he => followsMarkedBarrier hs hc ho he) hBranch hIndirect hSeg hStep

end PTX.Kernels.TmlFa4Fwd
