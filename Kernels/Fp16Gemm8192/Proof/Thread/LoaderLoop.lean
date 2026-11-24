-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Loader
public import Mathlib.Tactic.FinCases
public import Lemmas.Flow.Pointer

@[expose] public section

/-! # The loader's K loop: one step from each state

For every state of a trip except its last block, the event fires and local execution
reaches a concrete state of the successor (`next`). Each proof evaluates the actual
code of the segment; the per-block differences are three small tables. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


/-- The predicate each block's poll writes. -/
def waitPred : Fin 8 → Nat
  | 0 => 978 | 1 => 979 | 2 => 980 | 3 => 981
  | 4 => 982 | 5 => 983 | 6 => 984 | 7 => 985

/-- Local instructions from a successful poll to the block's first load. -/
def toLoads (b : Fin 8) : Nat := if b.val < 4 then 7 else 6

/-- Local instructions from load `j` to load `j + 1`. -/
def betweenLoads (b : Fin 8) (j : Nat) : Nat := if b.val = 0 ∧ j = 1 then 5 else 4

theorem waitPred_not_live : ∀ b : Fin 8, waitPred b ∉ Flow.live (Site.wait b).pc := by
  intro b
  fin_cases b <;> table_decide

theorem facts_fst {L : Launch} {g : Nat} {d : D} {p : Nat × Value} (hp : p ∈ facts L g d) :
    p.1 ∈ Flow.live d.site.pc := by
  simp only [facts, factsAt, Flow.factsFrom, List.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  exact hr

theorem not_live {L : Launch} {g : Nat} {d : D} {r : Nat} (h : r ∉ Flow.live d.site.pc) :
    ∀ p ∈ facts L g d, p.1 ≠ r := fun _ hp he => h (he ▸ facts_fst hp)

theorem code_wait : ∀ b : Fin 8, ∃ base par, kernel.code[(Site.wait b).pc]? =
    some ⟨none, .mbarWait (waitPred b) base 0 (.reg par) true .cta⟩
  | 0 => ⟨_, _, Flow.code_mbarWait_0⟩
  | 1 => ⟨_, _, Flow.code_mbarWait_1⟩
  | 2 => ⟨_, _, Flow.code_mbarWait_2⟩
  | 3 => ⟨_, _, Flow.code_mbarWait_3⟩
  | 4 => ⟨_, _, Flow.code_mbarWait_4⟩
  | 5 => ⟨_, _, Flow.code_mbarWait_5⟩
  | 6 => ⟨_, _, Flow.code_mbarWait_6⟩
  | 7 => ⟨_, _, Flow.code_mbarWait_7⟩

/-- Loads and arrivals continue at the next instruction. -/
theorem code_advances : ∀ s : {s : Site // ∃ b j, s = .load b j ∨ s = .arrive b},
    ∃ ins, kernel.code[s.1.pc]? = some ins ∧ ins.guard = none ∧ AdvancesOp ins.op ∧
      ins.op.isLocal = false
  | ⟨.load 0 0, _⟩ => ⟨_, Flow.code_tensorCopy_0, rfl, trivial, rfl⟩
  | ⟨.load 0 1, _⟩ => ⟨_, Flow.code_tensorCopy_1, rfl, trivial, rfl⟩
  | ⟨.load 0 2, _⟩ => ⟨_, Flow.code_tensorCopy_2, rfl, trivial, rfl⟩
  | ⟨.load 1 0, _⟩ => ⟨_, Flow.code_tensorCopy_3, rfl, trivial, rfl⟩
  | ⟨.load 1 1, _⟩ => ⟨_, Flow.code_tensorCopy_4, rfl, trivial, rfl⟩
  | ⟨.load 1 2, _⟩ => ⟨_, Flow.code_tensorCopy_5, rfl, trivial, rfl⟩
  | ⟨.load 2 0, _⟩ => ⟨_, Flow.code_tensorCopy_6, rfl, trivial, rfl⟩
  | ⟨.load 2 1, _⟩ => ⟨_, Flow.code_tensorCopy_7, rfl, trivial, rfl⟩
  | ⟨.load 2 2, _⟩ => ⟨_, Flow.code_tensorCopy_8, rfl, trivial, rfl⟩
  | ⟨.load 3 0, _⟩ => ⟨_, Flow.code_tensorCopy_9, rfl, trivial, rfl⟩
  | ⟨.load 3 1, _⟩ => ⟨_, Flow.code_tensorCopy_10, rfl, trivial, rfl⟩
  | ⟨.load 3 2, _⟩ => ⟨_, Flow.code_tensorCopy_11, rfl, trivial, rfl⟩
  | ⟨.load 4 0, _⟩ => ⟨_, Flow.code_tensorCopy_12, rfl, trivial, rfl⟩
  | ⟨.load 4 1, _⟩ => ⟨_, Flow.code_tensorCopy_13, rfl, trivial, rfl⟩
  | ⟨.load 4 2, _⟩ => ⟨_, Flow.code_tensorCopy_14, rfl, trivial, rfl⟩
  | ⟨.load 5 0, _⟩ => ⟨_, Flow.code_tensorCopy_15, rfl, trivial, rfl⟩
  | ⟨.load 5 1, _⟩ => ⟨_, Flow.code_tensorCopy_16, rfl, trivial, rfl⟩
  | ⟨.load 5 2, _⟩ => ⟨_, Flow.code_tensorCopy_17, rfl, trivial, rfl⟩
  | ⟨.load 6 0, _⟩ => ⟨_, Flow.code_tensorCopy_18, rfl, trivial, rfl⟩
  | ⟨.load 6 1, _⟩ => ⟨_, Flow.code_tensorCopy_19, rfl, trivial, rfl⟩
  | ⟨.load 6 2, _⟩ => ⟨_, Flow.code_tensorCopy_20, rfl, trivial, rfl⟩
  | ⟨.load 7 0, _⟩ => ⟨_, Flow.code_tensorCopy_21, rfl, trivial, rfl⟩
  | ⟨.load 7 1, _⟩ => ⟨_, Flow.code_tensorCopy_22, rfl, trivial, rfl⟩
  | ⟨.load 7 2, _⟩ => ⟨_, Flow.code_tensorCopy_23, rfl, trivial, rfl⟩
  | ⟨.arrive 0, _⟩ => ⟨_, Flow.code_mbarArrive_0, rfl, trivial, rfl⟩
  | ⟨.arrive 1, _⟩ => ⟨_, Flow.code_mbarArrive_1, rfl, trivial, rfl⟩
  | ⟨.arrive 2, _⟩ => ⟨_, Flow.code_mbarArrive_2, rfl, trivial, rfl⟩
  | ⟨.arrive 3, _⟩ => ⟨_, Flow.code_mbarArrive_3, rfl, trivial, rfl⟩
  | ⟨.arrive 4, _⟩ => ⟨_, Flow.code_mbarArrive_4, rfl, trivial, rfl⟩
  | ⟨.arrive 5, _⟩ => ⟨_, Flow.code_mbarArrive_5, rfl, trivial, rfl⟩
  | ⟨.arrive 6, _⟩ => ⟨_, Flow.code_mbarArrive_6, rfl, trivial, rfl⟩
  | ⟨.arrive 7, _⟩ => ⟨_, Flow.code_mbarArrive_7, rfl, trivial, rfl⟩
  | ⟨.wait _, h⟩ => by simp at h
  | ⟨.clcWait, h⟩ | ⟨.clcLoad, h⟩ | ⟨.clcStatus, h⟩ | ⟨.clcFirst, h⟩ | ⟨.clcFence, h⟩
  | ⟨.ack, h⟩ | ⟨.drain _, h⟩ | ⟨.exitArrive, h⟩ | ⟨.exitWait, h⟩ | ⟨.exit, h⟩ => by simp at h

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
