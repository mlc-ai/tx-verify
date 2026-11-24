-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaLinearEvents
public import Lemmas.Flow.TauFrame
public import Lemmas.Flow.WarpUniform

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- Register destinations across both silent and returning event transitions in the MMA role. -/
def mmaWrites (op : Op) : List Nat :=
  match op with
  | .mbarWait dst .. => [dst]
  | _ => writesRegs op

private theorem linearLoadRegs {s : TState} {ds : List Nat} {bs : List (Option Byte)} {r : Nat}
    (h : ds.length = 1) (hr : r ∉ ds) : (afterLoad s ds bs).regs r = s.regs r := by
  cases hb : rebuild 3 bs with
  | error f => simp [afterLoad, hb]
  | ok v =>
    rw [afterLoad_last hb (by omega)]
    exact setRegs_other _ _ _ _ hr

private theorem voteFrame {l : Launch} {g dst src r : Nat} {s : TState} {neg : Bool}
    {mask : Opnd} (hr : r ≠ dst) :
    CallbackFrame (fun u => u.regs r = s.regs r) (voteTmpl l g s dst src neg mask) := by
  unfold voteTmpl
  split <;> (try split_ifs) <;>
    simp [CallbackFrame, next, setReg, Function.update_of_ne hr]

private theorem warpRegs {l : Launch} {g r : Nat} {s u : TState} {w : WarpInstr} {e : Event}
    (hW : linearWarpOp w = true) (hr : r ∉ writesRegs (.warp w))
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.warp w)) e (some u)) :
    u.regs r = s.regs r := by
  unfold linearWarpOp at hW
  split at hW
  · rename_i _ mode ty dst a b c mask
    obtain ⟨_, _, _, _, _, _, rfl⟩ := fires_shfl (p := none) hf
    have hr' : r ≠ dst := by simpa [writesRegs] using hr
    exact Function.update_of_ne hr' _ _
  · rename_i _ ty dst pred mask
    obtain ⟨_, _, _, _, rfl⟩ := fires_elect hf
    cases dst with
    | none =>
      have hP : r ≠ pred := by simpa [writesRegs] using hr
      exact Function.update_of_ne hP _ _
    | some dst =>
      have hKeep : r ≠ dst ∧ r ≠ pred := by simpa [writesRegs] using hr
      change Function.update (Function.update _ dst _) pred _ r = _
      rw [Function.update_of_ne hKeep.2, Function.update_of_ne hKeep.1]
  · rename_i _ neg ty dst src mask
    have hr' : r ≠ dst := by simpa [writesRegs] using hr
    simp only [eventTmpl, warpTmpl_vote] at hf
    exact callbackFrame_fires (voteFrame hr') hf
  · cases hW

private theorem barRegs {l : Launch} {g : Nat} {s : TState} {a : Opnd} {n : Option Opnd} :
    CallbackFrame (fun u => u.regs = s.regs) (barTmpl l g s a n .sync) := by
  unfold barTmpl
  repeat' split
  all_goals simp [CallbackFrame, next]

private theorem mmaRegs {l : Launch} {g : Nat} {s : TState} {i : TcMmaInstr} :
    CallbackFrame (fun u => u.regs = s.regs) (mmaTmpl l g s i) := by
  unfold mmaTmpl
  split
  · apply ofExec_frame
    repeat' first | rfl | trivial | (apply allOk_bind; intro v) | split
  · apply ofExec_frame
    repeat' first | rfl | trivial | (apply allOk_bind; intro v) | split
  · trivial

private theorem resourceRegs {l : Launch} {g : Nat} {s : TState} {op : Op}
    (hop : (∃ group base off nc, op = .tcAlloc group base off nc) ∨
      (∃ group base nc, op = .tcDealloc group base nc) ∨ ∃ group, op = .tcRelinquish group) :
    CallbackFrame (fun u => u.regs = s.regs) (tcTmpl l g s op) := by
  rcases hop with ⟨group, base, off, nc, rfl⟩ | ⟨group, base, nc, rfl⟩ | ⟨group, rfl⟩ <;>
    simp only [tcTmpl] <;> apply ofExec_frame
  all_goals repeat' first | rfl | trivial | (apply allOk_bind; intro v) | split

/-- An actual returning MMA-role event preserves every register outside the decoded writes. -/
theorem mmaEventRegs {l : Launch} {g r : Nat} {s u : TState} {e : Event} {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) (hOp : linearEventOp ins.op = true)
    (hr : r ∉ mmaWrites ins.op) (he : EStep kernel Assumptions.all l g s e (some u)) :
    u.regs r = s.regs r := by
  obtain ⟨i, hi, _, hf⟩ := estep_event_source he
  rw [hc] at hi
  obtain rfl := Option.some.inj hi
  generalize ho : ins.op = op at hOp hr hf
  cases op <;> try contradiction
  case warp => exact warpRegs hOp hr hf
  case barSync a aligned =>
    exact congrFun (callbackFrame_fires (barRegs (a := a) (n := none)) hf) r
  case barSyncN a n aligned =>
    exact congrFun (callbackFrame_fires (barRegs (a := a) (n := some n)) hf) r
  case setMaxReg inc n =>
    obtain rfl := fires_next (op := .setMaxReg inc n) trivial hf
    rfl
  case mbarWait dst b o p a sc =>
    obtain ⟨_, _, _, _, _, rfl⟩ := fires_wait hf
    have hr' : r ≠ dst := by simpa [mmaWrites] using hr
    exact Function.update_of_ne hr' _ _
  case tcAlloc =>
    exact congrFun (callbackFrame_fires (resourceRegs (g := g) (.inl ⟨_, _, _, _, rfl⟩)) hf) r
  case tcMma => exact congrFun (callbackFrame_fires mmaRegs hf) r
  case tcCommit =>
    obtain rfl := fires_tcCommit hf
    rfl
  case tcDealloc =>
    exact congrFun (callbackFrame_fires (resourceRegs (g := g) (.inr (.inl ⟨_, _, _, rfl⟩))) hf) r
  case tcRelinquish =>
    exact congrFun (callbackFrame_fires (resourceRegs (g := g) (.inr (.inr ⟨_, rfl⟩))) hf) r
  case mem a =>
    have hMem : a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs.length = 1 := by
      simpa [linearEventOp, and_assoc] using hOp
    obtain ⟨_, _, _, rfl⟩ := fires_load hMem.1 hMem.2.1 hf hMem.2.2.1
    exact linearLoadRegs hMem.2.2.2 hr

private theorem mmaRoleEventOp {pc : Nat} {ins : Instr} (hLo : 1904 ≤ pc) (hHi : pc < 2768)
    (hc : kernel.code[pc]? = some ins) (hLocal : ins.op.isLocal = false) :
    linearEventOp ins.op = true := by
  have hAll : ((kernel.code.drop 1904).take 864).all
      (fun i => i.op.isLocal || linearEventOp i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSlice : ((kernel.code.drop 1904).take 864)[pc - 1904]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  simpa only [hLocal, Bool.false_or] using
    List.all_eq_true.mp hAll ins (List.mem_of_getElem? hSlice)

/-- A transition inside the frozen MMA role preserves a register omitted by its instruction. -/
theorem mmaStepReg {l : Launch} {g r : Nat} {s u : TState} {ev : Option Event}
    (hLo : 1904 ≤ s.pc) (hHi : s.pc < 2768)
    (hFrame : ∀ i, kernel.code[s.pc]? = some i → r ∉ mmaWrites i.op)
    (h : WStep kernel Assumptions.all l g s ev u) : u.regs r = s.regs r := by
  rcases h with ⟨-, ht⟩ | ⟨e, -, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← out_eq_core hLo hHi]
    obtain ⟨i, hc⟩ := tau_core_has_code ht'
    have hRegs := hFrame i hc
    have hLocal : r ∉ writesRegs i.op := by
      cases hOp : i.op <;> simp_all [mmaWrites, writesRegs]
    exact tau_core_regs hc ht' hLocal
  · obtain ⟨i, hc, hLocal, _⟩ := estep_event_source he
    exact mmaEventRegs hc (mmaRoleEventOp hLo hHi hc hLocal) (hFrame i hc) he

/-- The role preserves the CTA id in every returning step, including polls and allocation. -/
theorem mmaStepCta {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 1904 ≤ s.pc) (hHi : s.pc < 2768)
    (h : WStep kernel Assumptions.all l g s ev u) : u.regs 1072 = s.regs 1072 := by
  apply mmaStepReg hLo hHi _ h
  intro ins hc
  have hAll : ((kernel.code.drop 1904).take 864).all
      (fun i => !(mmaWrites i.op).contains 1072) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSlice : ((kernel.code.drop 1904).take 864)[s.pc - 1904]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  simpa using List.all_eq_true.mp hAll ins (List.mem_of_getElem? hSlice)

end
end PTX.Kernels.TmlFa4Fwd.Mma
