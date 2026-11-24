-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmFlt
public import Kernels.InklingRelDecode.Proof.Thread.EpiAsms
public import Lemmas.Flow.WarpUniformAt

@[expose] public section

/-! # The local rules and the segment of the kernel's assumptions

`rulesFrame`: every local rule of `Assumptions.all` writes only the destination registers of its
instruction (`RulesFrame`). The two generic readings (`idealArith`, `approx`) have it from
`RulesFrame.idealReal` and `RulesFrame.approxExact`; the four kernel-local readings (`lg2Exact`,
`divFullExact`, `negExact`, `bf16Exact`) write their one destination and continue at the next
position; the other assumptions have no local rule.

`segLands`: the software `exp2` segment (`swExp2`) continues 11 positions after its first
instruction, which is no poll branch (`SegLandsAll`), so local steps land (`localLands`,
`LocalLands.of_rules`).

`localA_regs`: a local step of `Assumptions.all` at a position writes only the registers of its
instruction (`writesRegs`) and, at a software `exp2` site, the registers of the instance
(`Sm.emuW`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Wq
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- A step that writes one destination of the instruction and continues at the next position
keeps the frame. -/
theorem frame_next_setReg {op : Op} {t : TState} {d : Nat} {v : Value}
    (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) :
    LocalFrame op t (next (setReg t d v)) :=
  ⟨.inl hpc.symm, rfl, rfl, rfl, fun r hr =>
    Function.update_of_ne (fun e => hr (by subst e; exact hd)) _ _⟩

/-- Closes the frame of a kernel-local reading: one destination of a floating instruction or a
conversion, continuing at the next position. -/
local macro "rule_frame" : tactic => `(tactic| (
  repeat' (first | split_ifs at * | split at * | (simp only [bindRead] at *))
  all_goals first
    | (cases ‹_ = _›; done)
    | (simp only [Option.some.injEq, Except.ok.injEq, pure, Except.pure] at *
       subst_vars
       exact frame_next_setReg rfl (by simp_all [writesRegs]))
    | (simp_all; done)))

theorem lg2_frame {t t' : TState} {op : Op}
    (h : Assumptions.lg2Exact.localRule L g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.lg2Exact] at h
  rule_frame

theorem divFull_frame {t t' : TState} {op : Op}
    (h : Assumptions.divFullExact.localRule L g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.divFullExact] at h
  rule_frame

theorem neg_frame {t t' : TState} {op : Op}
    (h : Assumptions.negExact.localRule L g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.negExact] at h
  rule_frame

theorem bf16_frame {t t' : TState} {op : Op}
    (h : Assumptions.bf16Exact.localRule L g t op = some (.ok t')) : LocalFrame op t t' := by
  simp only [Assumptions.bf16Exact] at h
  rule_frame

/-- **Every local rule of the kernel's assumptions writes only its instruction's registers.** -/
theorem rulesFrame : RulesFrame Assumptions.all := by
  intro a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · intro _ _ _ _ _ h; cases h
  · exact fun _ _ _ _ _ => idealReal_frame
  · exact fun _ _ _ _ _ => approxExact_frame
  · intro _ _ _ _ _ h; cases h
  · exact fun _ _ _ _ _ => lg2_frame
  · exact fun _ _ _ _ _ => divFull_frame
  · exact fun _ _ _ _ _ => neg_frame
  · exact fun _ _ _ _ _ => bf16_frame
  all_goals intro _ _ _ _ _ h; cases h

/-- No software `exp2` instance ends at a poll branch. -/
theorem emu_end_ok :
    Assumptions.emuSites.all (fun pc => !kernel.pollBranch (pc + 11)) = true := by
  decide +kernel

/-- The software `exp2` segment: an instance at an `exp2` site whose body matches, with its
result. -/
theorem swExp2_spec {t : TState} {r : Exec TState}
    (h : (Assumptions.swExp2 kernel).segmentRule L g t = some r) :
    Assumptions.emuSites.contains t.pc = true ∧
      Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) [] =
        some (Sm.emuAsg t.pc) ∧ Assumptions.execEmu (Sm.emuAsg t.pc) t = some r := by
  change (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
    (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) []).bind
      (Assumptions.execEmu · t) else none) = some r at h
  split_ifs at h with hs
  obtain ⟨asg, hm, he⟩ := Option.bind_eq_some_iff.mp h
  have ha : Sm.emuAsg t.pc = asg := by simp [Sm.emuAsg, hm]
  rw [ha]
  exact ⟨hs.1, hm, he⟩

/-- An instance continues 11 positions after its first instruction and writes only the
registers of the instance (`Sm.emuW`). -/
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

/-- Only `swExp2` takes a segment. -/
theorem seg_swExp2 {t : TState} {r : Exec TState}
    (h : Assumptions.all.findSome? (fun a => a.segmentRule L g t) = some r) :
    (Assumptions.swExp2 kernel).segmentRule L g t = some r := by
  obtain ⟨a, ha, hr⟩ := List.exists_of_findSome?_eq_some h
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hr | cases hr

/-- **Every segment of the kernel's assumptions lands off the poll branches.** -/
theorem segLands : SegLandsAll kernel Assumptions.all := by
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
    ∀ r, r ∉ writesRegs op → (Assumptions.emuSites.contains t.pc = true → r ∉ Sm.emuW t.pc) →
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

end
end PTX.Kernels.InklingRelDecode.Proof.Wq
