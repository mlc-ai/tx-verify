-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Lemmas.Flow.Next
public import Lemmas.Flow.Tc
public import Lemmas.Flow.Vector
public import Lemmas.Flow.EventCont

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

def allocationOp : Op → Bool
  | .tcAlloc .. => true
  | _ => false

def linearWarpOp : WarpInstr → Bool
  | ⟨.shfl _, _, [some _], [_, _, _], some _⟩
  | ⟨.elect, _, [_, some _], [], some _⟩
  | ⟨.vote .ballot _, _, [some _], [.reg _], some _⟩ => true
  | _ => false

/-- The returning event instructions in the MMA role can only advance, take the allocation
store sub-step, or record a pending scalar load fault. -/
def linearEventOp : Op → Bool
  | .warp w => linearWarpOp w
  | .barSync .. | .barSyncN .. | .setMaxReg .. | .mbarWait ..
  | .tcAlloc .. | .tcMma .. | .tcCommit .. | .tcDealloc .. | .tcRelinquish .. => true
  | .mem m => m.kind == .load && !m.nc && m.ext == .same && m.regs.length == 1
  | _ => false

private def Advances (t u : TState) : Prop :=
  u.pc = t.pc + 1 ∧ u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault

variable {l : Launch} {g : Nat}

private theorem voteAdvances {s : TState} {d a : Nat} {neg : Bool} {mask : Opnd} :
    CallbackFrame (Advances s) (voteTmpl l g s d a neg mask) := by
  unfold voteTmpl
  split <;> (try split_ifs) <;> simp [Advances, CallbackFrame, next, setReg]

private theorem warpAdvances {s u : TState} {w : WarpInstr} {e : Event} (hw : linearWarpOp w = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.warp w)) e (some u)) :
    Advances s u := by
  unfold linearWarpOp at hw
  split at hw
  · obtain ⟨_, _, _, _, _, _, rfl⟩ := fires_shfl (p := none) hf
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rename_i _ ty dst pred mask
    obtain ⟨_, _, _, _, rfl⟩ := fires_elect hf
    cases dst <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [eventTmpl, warpTmpl_vote] at hf
    exact callbackFrame_fires voteAdvances hf
  · cases hw

/-- The audited shuffle, elect and ballot templates preserve the current sub-step
while advancing to the following instruction. -/
theorem linearWarpAdvances {s u : TState} {w : WarpInstr} {e : Event} (hw : linearWarpOp w = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.warp w)) e (some u)) :
    u.pc = s.pc + 1 ∧ u.sub = s.sub := by
  have h := warpAdvances hw hf
  exact ⟨h.1, h.2.1⟩

theorem linearWarpAccumulator {s u : TState} {w : WarpInstr} {e : Event}
    (hw : linearWarpOp w = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.warp w)) e (some u)) :
    u.acc = s.acc := (warpAdvances hw hf).2.2.1

private theorem barAdvances {s : TState} {a : Opnd} {n : Option Opnd} :
    CallbackFrame (Advances s) (barTmpl l g s a n .sync) := by
  unfold barTmpl
  repeat' split
  all_goals simp [Advances, CallbackFrame, next]

private theorem mmaAdvances {s : TState} {i : TcMmaInstr} :
    CallbackFrame (Advances s) (mmaTmpl l g s i) := by
  unfold mmaTmpl
  split
  · apply ofExec_frame
    repeat' first | trivial | (apply allOk_bind; intro v) | split
  · apply ofExec_frame
    repeat' first | trivial | (apply allOk_bind; intro v) | split
  · trivial

private theorem resourceAdvances {s : TState} {op : Op}
    (hop : (∃ group base nc, op = .tcDealloc group base nc) ∨ ∃ group, op = .tcRelinquish group) :
    CallbackFrame (Advances s) (tcTmpl l g s op) := by
  rcases hop with ⟨group, base, nc, rfl⟩ | ⟨group, rfl⟩ <;> simp only [tcTmpl] <;>
    apply ofExec_frame
  all_goals repeat' first | trivial | (apply allOk_bind; intro v) | split

private theorem allocAdvances {s : TState} {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd} :
    CallbackFrame (fun u => (u.pc = s.pc + 1 ∧ u.sub = 0 ∨
      u.pc = s.pc ∧ s.sub = 0 ∧ u.sub = 1) ∧ u.acc = s.acc ∧ u.fault = s.fault)
      (tcTmpl l g s (.tcAlloc group base off nc)) := by
  simp only [tcTmpl]
  apply ofExec_frame
  repeat' first
    | exact True.intro
    | (apply allOk_bind; intro v)
    | split
  all_goals simp_all [AllOk, CallbackFrame, pure, Except.pure, next]

/-- An actual returning event either advances by one PC, advances within the allocation
instruction, or records a scalar load fault for the next event. -/
theorem linearEventProgressWithSub {s u : TState} {e : Event} {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) (hOp : linearEventOp ins.op = true) (hSub : s.sub ≤ 1)
    (hAcc : s.acc = []) (h : EStep kernel Assumptions.all l g s e (some u)) :
    u.sub ≤ 1 ∧ u.acc = [] ∧
      (u.pc = s.pc + 1 ∧ u.fault = s.fault ∧
        (u.sub = 0 ∨ u.sub = s.sub ∧ allocationOp ins.op = false) ∨
        u.pc = s.pc ∧ s.sub = 0 ∧ u.sub = 1 ∧ allocationOp ins.op ∨
        u.pc = s.pc ∧ u.sub = s.sub ∧ u.fault.isSome) := by
  obtain ⟨ins', hc', _, hf⟩ := estep_event_source h
  rw [hc] at hc'
  obtain rfl := Option.some.inj hc'
  have finish {alloc : Bool} (ha : Advances s u) (hNoAlloc : alloc = false) :
      u.sub ≤ 1 ∧ u.acc = [] ∧
        (u.pc = s.pc + 1 ∧ u.fault = s.fault ∧
          (u.sub = 0 ∨ u.sub = s.sub ∧ alloc = false) ∨
          u.pc = s.pc ∧ s.sub = 0 ∧ u.sub = 1 ∧ alloc ∨
          u.pc = s.pc ∧ u.sub = s.sub ∧ u.fault.isSome) := by
    exact ⟨ha.2.1 ▸ hSub, ha.2.2.1.trans hAcc, .inl ⟨ha.1, ha.2.2.2, .inr ⟨ha.2.1, hNoAlloc⟩⟩⟩
  generalize hop : ins.op = op at hOp hf
  cases op <;> try contradiction
  case warp => exact finish (warpAdvances hOp hf) rfl
  case barSync barrier aligned =>
    exact finish (callbackFrame_fires (barAdvances (a := barrier) (n := none)) hf) rfl
  case barSyncN barrier count aligned =>
    exact finish (callbackFrame_fires (barAdvances (a := barrier) (n := some count)) hf) rfl
  case setMaxReg inc n =>
    obtain rfl := fires_next (op := .setMaxReg inc n) trivial hf
    exact finish ⟨rfl, rfl, rfl, rfl⟩ rfl
  case mbarWait =>
    obtain ⟨_, _, _, _, _, rfl⟩ := fires_wait hf
    exact finish ⟨rfl, rfl, rfl, rfl⟩ rfl
  case tcAlloc =>
    obtain ⟨hAdvance | hStore, hRegs, hFault⟩ := callbackFrame_fires allocAdvances hf
    · exact ⟨by rw [hAdvance.2]; decide, hRegs.trans hAcc,
        .inl ⟨hAdvance.1, hFault, .inl hAdvance.2⟩⟩
    · exact ⟨by omega, hRegs.trans hAcc, .inr (.inl ⟨hStore.1, hStore.2.1, hStore.2.2, rfl⟩)⟩
  case tcMma => exact finish (callbackFrame_fires mmaAdvances hf) rfl
  case tcCommit =>
    obtain rfl := fires_tcCommit hf
    exact finish ⟨rfl, rfl, rfl, rfl⟩ rfl
  case tcDealloc =>
    exact finish (callbackFrame_fires (resourceAdvances (g := g) (.inl ⟨_, _, _, rfl⟩)) hf) rfl
  case tcRelinquish =>
    exact finish (callbackFrame_fires (resourceAdvances (g := g) (.inr ⟨_, rfl⟩)) hf) rfl
  case mem a =>
    have hMem : a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs.length = 1 := by
      simpa [linearEventOp, and_assoc] using hOp
    obtain ⟨_, bs, _, rfl⟩ := fires_load hMem.1 hMem.2.1 hf hMem.2.2.1
    cases hRead : rebuild 3 bs with
    | error f =>
      exact ⟨by simp [afterLoad, hRead, hSub], by simp [afterLoad, hRead, hAcc],
        .inr (.inr ⟨by simp [afterLoad, hRead], by simp [afterLoad, hRead],
          by simp [afterLoad, hRead]⟩)⟩
    | ok v =>
      rw [afterLoad_last hRead (by omega)]
      exact ⟨Nat.zero_le 1, rfl, .inl ⟨rfl, (setRegs_skel s a.regs (s.acc ++ [v])).2.2.2,
        .inl rfl⟩⟩

/-- An actual returning event either advances by one PC, advances within the allocation
instruction, or records a scalar load fault for the next event. -/
theorem linearEventProgress {s u : TState} {e : Event} {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) (hOp : linearEventOp ins.op = true) (hSub : s.sub ≤ 1)
    (hAcc : s.acc = []) (h : EStep kernel Assumptions.all l g s e (some u)) :
    u.sub ≤ 1 ∧ u.acc = [] ∧
      (u.pc = s.pc + 1 ∨ u.pc = s.pc ∧ s.sub = 0 ∧ u.sub = 1 ∧ allocationOp ins.op ∨
        u.pc = s.pc ∧ u.fault.isSome) := by
  obtain ⟨hs, ha, hu | hu | hu⟩ := linearEventProgressWithSub hc hOp hSub hAcc h
  · exact ⟨hs, ha, .inl hu.1⟩
  · exact ⟨hs, ha, .inr (.inl hu)⟩
  · exact ⟨hs, ha, .inr (.inr ⟨hu.1, hu.2.2⟩)⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
