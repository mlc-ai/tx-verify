-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.RulesFrame
public import Lemmas.Flow.Havoc
import Lemmas.Flow.SegFree

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof PTX.Assumption

/-- The template assignment determines the clobber set even when the input faults. -/
def hooks (pc : Nat) : Option Havoc.Hook := do
  guard (Assumptions.emuSites.contains pc)
  let asg ← Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop pc) []
  return ⟨pc + 11, Assumptions.emuWrites.map (Assumptions.emuReg asg)⟩

private theorem execEmu_spec {t u : TState} {asg : List (Assumptions.EmuSlot × Nat)}
    (h : Assumptions.execEmu asg t = some (.ok u)) :
    u.pc = t.pc + 11 ∧ u.sub = 0 ∧ u.acc = [] ∧ u.fault = t.fault ∧
      ∀ r, r ∉ Assumptions.emuWrites.map (Assumptions.emuReg asg) →
      u.regs r = t.regs r := by
  unfold Assumptions.execEmu bindRead at h
  split at h
  · cases h
  · cases h
  · simp only [Option.some.injEq] at h
    split_ifs at h
    all_goals cases h
    all_goals
      refine ⟨rfl,rfl,rfl,rfl,fun r hr => ?_⟩
      have hy : r ≠ Assumptions.emuReg asg .y := fun he => hr (List.mem_map.mpr
        ⟨.y, by simp [Assumptions.emuWrites], he.symm⟩)
      simp only
      rw [Function.update_of_ne hy]
      exact foldl_update_other (f := Assumptions.emuReg asg) (v := fun _ => none) _
        (fun s hs he => hr (List.mem_map.mpr ⟨s, hs, he⟩))

theorem hooks_ok {L : Launch} {g : Nat} : Havoc.Hooks Assumptions.all L g hooks := by
  intro t a u hs ha hm h
  simp only [Assumptions.all,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try cases h
  change (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
    (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) []).bind
      (Assumptions.execEmu · t) else none) = some (.ok u) at h
  split at h
  · rename_i active
    obtain ⟨asg,hm,he⟩ := Option.bind_eq_some_iff.mp h
    have hin : t.pc ∈ Assumptions.emuSites := by simpa using active.1
    exact ⟨⟨t.pc+11,Assumptions.emuWrites.map (Assumptions.emuReg asg)⟩,
      by simp [hooks,guard,hin,hm],
      execEmu_spec he⟩
  · cases h

end PTX.Kernels.InklingRelDecode.Proof.Lib
