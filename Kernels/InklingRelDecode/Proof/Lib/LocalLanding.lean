-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.RulesFrame
public import Kernels.InklingRelDecode.Proof.Lib.Segments
public import Lemmas.Flow.PollLands
public import Lemmas.Register.RegisterFrame

@[expose] public section

/-! # Local steps of the kernel land at the next position

The software `exp2` segment continues 11 positions after its first instruction, which is no
poll branch, and no other assumption takes a segment, so local steps land at the next position or
off the poll branches (`LocalLands`). A local step writes only the registers of its instruction
and, at a software `exp2` site, those of the instance (`localA_regs`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow PTX.Assumption

set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The slot-register assignment of the instance at `pc`. -/
def emuAsg (pc : Nat) : List (Assumptions.EmuSlot × Nat) :=
  (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop pc) []).getD []

/-- The registers an instance writes (the temporaries and the output). -/
def emuW (pc : Nat) : List Nat := Assumptions.emuWrites.map (Assumptions.emuReg (emuAsg pc))

/-- No software `exp2` instance ends at a poll branch. -/
private theorem emu_end_ok :
    Assumptions.emuSites.all (fun pc => !kernel.pollBranch (pc + 11)) = true := by
  decide +kernel

private theorem swExp2_spec {t : TState} {r : Exec TState}
    (h : (Assumptions.swExp2 kernel).segmentRule L g t = some r) :
    Assumptions.emuSites.contains t.pc = true ∧
      Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) [] =
        some (emuAsg t.pc) ∧ Assumptions.execEmu (emuAsg t.pc) t = some r := by
  change (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
    (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) []).bind
      (Assumptions.execEmu · t) else none) = some r at h
  split_ifs at h with hs
  obtain ⟨asg, hm, he⟩ := Option.bind_eq_some_iff.mp h
  have ha : emuAsg t.pc = asg := by simp [emuAsg, hm]
  rw [ha]
  exact ⟨hs.1, hm, he⟩

theorem execEmu_spec {t u : TState} {asg : List (Assumptions.EmuSlot × Nat)}
    (h : Assumptions.execEmu asg t = some (.ok u)) :
    u.pc = t.pc + 11 ∧ ∀ r, r ∉ Assumptions.emuWrites.map (Assumptions.emuReg asg) →
      u.regs r = t.regs r := by
  unfold Assumptions.execEmu bindRead at h
  split at h
  · cases h
  · cases h
  · simp only [Option.some.injEq] at h
    split_ifs at h
    all_goals cases h
    all_goals
      refine ⟨rfl, fun r hr => ?_⟩
      have hy : r ≠ Assumptions.emuReg asg .y := fun he => hr (List.mem_map.mpr
        ⟨.y, by simp [Assumptions.emuWrites], he.symm⟩)
      simp only
      rw [Function.update_of_ne hy]
      exact foldl_update_other (f := Assumptions.emuReg asg) (v := fun _ => none) _
        (fun s hs he => hr (List.mem_map.mpr ⟨s, hs, he⟩))

private theorem seg_swExp2 {t : TState} {r : Exec TState}
    (h : Assumptions.all.findSome? (fun a => a.segmentRule L g t) = some r) :
    (Assumptions.swExp2 kernel).segmentRule L g t = some r := by
  obtain ⟨a, ha, hr⟩ := List.exists_of_findSome?_eq_some h
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hr | cases hr

/-- Every segment of the kernel's assumptions lands off the poll branches. -/
private theorem segLands : SegLandsAll kernel Assumptions.all := by
  intro a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (exact SegLands.of_none fun _ _ _ => rfl)
    | (intro L g t t' h
       right
       obtain ⟨hs, -, he⟩ := swExp2_spec h
       rw [(execEmu_spec he).1]
       have := List.all_eq_true.mp emu_end_ok t.pc (by simpa using hs)
       simpa using this)

/-- **Local steps of the kernel land at the next position or off the poll branches.** -/
theorem localLands : LocalLands kernel Assumptions.all L :=
  LocalLands.of_rules rulesFrame segLands

/-- **A local step writes only the registers of its instruction**, and at a software `exp2`
site those of the instance. -/
theorem localA_regs {t u : TState} {op : Op}
    (h : execLocalA Assumptions.all L g t op = .ok u) :
    ∀ r, r ∉ writesRegs op → (Assumptions.emuSites.contains t.pc = true → r ∉ emuW t.pc) →
      u.regs r = t.regs r := by
  intro r hw he
  cases hf : Assumptions.all.findSome? (fun a => a.segmentRule L g t) with
  | some res =>
    unfold execLocalA at h
    rw [hf] at h
    subst h
    obtain ⟨hs, -, hx⟩ := swExp2_spec (seg_swExp2 hf)
    exact (execEmu_spec hx).2 r (he hs)
  | none =>
    rw [execLocalA_noSegment (List.findSome?_eq_none_iff.mp hf)] at h
    unfold execLocalRule at h
    cases hl : Assumptions.all.findSome? (fun a => a.localRule L g t op) with
    | none =>
      simp only [hl] at h
      exact (execLocal_frame h).regs r hw
    | some res =>
      simp only [hl] at h
      obtain ⟨a, ha, hr⟩ := List.exists_of_findSome?_eq_some hl
      rw [h] at hr
      exact (rulesFrame a ha L g t op u hr).regs r hw

/-- **A local step lands at the next position, at a target of a `brx.idx`, or after a software
`exp2` instance** (and then at one of its sites). -/
theorem localA_pc_emu {t u : TState} {op : Op}
    (h : execLocalA Assumptions.all L g t op = .ok u) :
    (u.pc = nextPc op t.pc ∨ BrxTarget op u.pc) ∨
      (u.pc = t.pc + 11 ∧ Assumptions.emuSites.contains t.pc = true) := by
  cases hf : Assumptions.all.findSome? (fun a => a.segmentRule L g t) with
  | some res =>
    unfold execLocalA at h
    rw [hf] at h
    subst h
    obtain ⟨hs, -, hx⟩ := swExp2_spec (seg_swExp2 hf)
    exact .inr ⟨(execEmu_spec hx).1, hs⟩
  | none =>
    rw [execLocalA_noSegment (List.findSome?_eq_none_iff.mp hf)] at h
    unfold execLocalRule at h
    cases hl : Assumptions.all.findSome? (fun a => a.localRule L g t op) with
    | none =>
      simp only [hl] at h
      exact .inl (execLocal_frame h).pc
    | some res =>
      simp only [hl] at h
      obtain ⟨a, ha, hr⟩ := List.exists_of_findSome?_eq_some hl
      rw [h] at hr
      exact .inl (rulesFrame a ha L g t op u hr).pc

/-- **A local step lands at the next position, at a target of a `brx.idx`, or after a software
`exp2` instance.** -/
theorem localA_pc {t u : TState} {op : Op}
    (h : execLocalA Assumptions.all L g t op = .ok u) :
    (u.pc = nextPc op t.pc ∨ BrxTarget op u.pc) ∨ u.pc = t.pc + 11 := by
  rcases localA_pc_emu h with h | ⟨h, -⟩
  · exact .inl h
  · exact .inr h

end PTX.Kernels.InklingRelDecode.Proof.Lib
