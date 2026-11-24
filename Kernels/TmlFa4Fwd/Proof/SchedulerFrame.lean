-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerCoordinates
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Lemmas.Register.RegisterFrame
public import Lemmas.Flow.Scalars
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegChain
public import Lemmas.Kernel.ReadValue
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionReads

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Decoded operations with a fallthrough successor, including a skipped instruction. -/
def schedulerFallsThrough (op : Op) : Bool :=
  match op with
  | .bra .. | .brx .. => false
  | _ => true

private theorem insideSlice {lo len pc : Nat} {ins : Instr}
    (hlo : lo ≤ pc) (hhi : pc < lo + len) (hc : kernel.code[pc]? = some ins) :
    ins ∈ (kernel.code.drop lo).take len := by
  have hi : ((kernel.code.drop lo).take len)[pc - lo]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo]
    exact hc
  exact List.mem_of_getElem? hi

private theorem tauWrites {l : Launch} {g : Nat} {t u : TState}
    (h : tauStep kernel [] l g t = some u) :
    ∃ ins, kernel.code[t.pc]? = some ins ∧
      (u.pc = t.pc + 1 ∨ u.pc = nextPc ins.op t.pc ∨ BrxTarget ins.op u.pc) ∧
      ∀ r ∉ writesRegs ins.op, u.regs r = t.regs r := by
  rw [tauStep_iff] at h
  unfold Tau out at h
  cases hf : t.fault with
  | some f => simp [hf] at h
  | none =>
    simp only [hf] at h
    cases hc : kernel.code[t.pc]? with
    | none => simp [hc] at h
    | some ins =>
      simp only [hc] at h
      cases hg : guardHolds t ins.guard with
      | error f => simp [hg] at h
      | ok b =>
        cases b
        · simp only [hg, Out.tau.injEq] at h
          subst u
          exact ⟨ins, rfl, .inl rfl, fun _ _ => rfl⟩
        · simp only [hg] at h
          split at h
          · split at h
            · rename_i t' ht'
              obtain rfl := Out.tau.inj h
              rw [execLocalA_nil] at ht'
              have hf' := execLocal_frame ht'
              exact ⟨ins, rfl, .inr hf'.pc, hf'.regs⟩
            · cases h
          · cases h

private theorem straightPc {op : Op} (h : schedulerFallsThrough op = true) {pc next : Nat}
    (he : next = pc + 1 ∨ next = nextPc op pc ∨ BrxTarget op next) : next = pc + 1 := by
  cases op <;> simp_all [schedulerFallsThrough, nextPc, BrxTarget]

/-- A local scheduler segment preserves the listed registers when its decoded instructions
write elsewhere and it can branch only on its final step. -/
theorem schedulerLocalFrame {l : Launch} {g n lo len : Nat} {t u : TState} {regs : List Nat}
    (hWrites : ((kernel.code.drop lo).take len).all
      (fun ins => regs.all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hFallthrough : ((kernel.code.drop lo).take (len - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true)
    (hRun : run kernel [] l g n t = some u) (hLo : lo ≤ t.pc)
    (hHi : t.pc + n ≤ lo + len) {r : Nat} (hr : r ∈ regs) : u.regs r = t.regs r := by
  induction n generalizing t with
  | zero =>
    obtain rfl := Option.some.inj hRun
    rfl
  | succ n ih =>
    simp only [run] at hRun
    cases hStep : tauStep kernel [] l g t with
    | none => simp [hStep] at hRun
    | some v =>
      rw [hStep, Option.bind_some] at hRun
      obtain ⟨ins, hc, hp, hw⟩ := tauWrites hStep
      have hCode := List.all_eq_true.mp hWrites ins (insideSlice hLo (by omega) hc)
      have hFree := List.all_eq_true.mp hCode r hr
      have hWrite : r ∉ writesRegs ins.op := by simpa using hFree
      have hKeep := hw r hWrite
      cases n with
      | zero =>
        obtain rfl := Option.some.inj hRun
        exact hKeep
      | succ n =>
        have hStraight := List.all_eq_true.mp hFallthrough ins (insideSlice hLo (by omega) hc)
        have hv := straightPc hStraight hp
        exact (ih hRun (by omega) (by omega)).trans hKeep

/-- A decoded local segment can be replayed under assumptions that agree with Core on its PCs. -/
theorem schedulerLocalTransport {A : List Assumption} {l : Launch} {g n lo len : Nat}
    {t u : TState}
    (hFallthrough : ((kernel.code.drop lo).take (len - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true)
    (hModel : ∀ {s : TState}, lo ≤ s.pc → s.pc < lo + len →
      out kernel A l g s = out kernel [] l g s)
    (hRun : run kernel [] l g n t = some u) (hLo : lo ≤ t.pc)
    (hHi : t.pc + n ≤ lo + len) : run kernel A l g n t = some u := by
  induction n generalizing t with
  | zero => exact hRun
  | succ n ih =>
    have hEq : tauStep kernel A l g t = tauStep kernel [] l g t := by
      rw [tauStep, hModel hLo (by omega), ← tauStep]
    simp only [run, hEq] at hRun ⊢
    cases hStep : tauStep kernel [] l g t with
    | none => simp [hStep] at hRun
    | some v =>
      simp only [hStep, Option.bind_some] at hRun ⊢
      cases n with
      | zero => exact hRun
      | succ n =>
        obtain ⟨ins, hc, hp, _⟩ := tauWrites hStep
        have hs := List.all_eq_true.mp hFallthrough ins (insideSlice hLo (by omega) hc)
        have hv := straightPc hs hp
        exact ih hRun (by omega) (by omega)

/-- Frame a list of register facts using the preserved register lookups. -/
theorem holdsSchedulerFrame {R S : Nat → Option Value} {F : List (Nat × Value)} {regs : List Nat}
    (h : Holds R F) (heq : ∀ i ∈ regs, S i = R i)
    (hF : ∀ pair ∈ F, pair.1 ∈ regs) : Holds S F := by
  induction F with
  | nil => trivial
  | cons pair F ih =>
    obtain ⟨hr, hrest⟩ := h
    exact ⟨(heq pair.1 (hF pair (by simp))).trans hr,
      ih hrest (fun pair hm => hF pair (List.mem_cons_of_mem _ hm))⟩

theorem assignedCoordinates_valid {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {batch item : Nat} (hLo : tilePrefix p batch * p.heads ≤ item)
    (hHi : item < tilePrefix p (batch + 1) * p.heads) :
    256 * (assignedCoordinates p batch item).1 < p.qLength batch ∧
      (assignedCoordinates p batch item).2 < p.heads := by
  have hHeads : 0 < p.heads := by
    unfold Params.heads
    have := hp.shape.2.2.1
    omega
  have hIn : item - tilePrefix p batch * p.heads < requestTiles p batch * p.heads := by
    rw [tilePrefix_succ, Nat.add_mul] at hHi
    omega
  have hPos := sectionItem_coords (sectionWidth_pos (tiles := requestTiles p batch) hHeads) hIn
  exact ⟨Nat.mul_comm _ _ ▸ requestTile_has_row hPos.1, hPos.2.1⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
