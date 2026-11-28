-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietAlloc
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Quiet
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.NextEnv

@[expose] public section

/-! # The startup's quiet row

Every pc of the startup (below 103) holds a quiet instruction, a warp collective (the shuffles 6
and 9, the elections 16 and 31), or the allocation at pc 91, which steps because every recorded
allocation is at column 0 (`Prog.allocZero`). The startup polls no mbarrier. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

private theorem st_code_all : (((kernel.code.drop 0).take 103).zipIdx).all
    (fun p => decide (p.2 + 0 ∈ [91]) || quietOk p.1.op || collInsB p.1) = true := by
  decide +kernel

private theorem st_alloc : kernel.code[91]?.all (fun i => Sched.allocOp i.op) = true := by
  decide +kernel

/-- **The startup's quiet row.** -/
theorem Prog.startupRow (hIn : Top.Inputs P L m) (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (X : Execution) : NextRow.Quiet P L m X fun _ pc => MbarRow.StartupAt pc := by
  intro hs hmax g e hpd hrel hn hub hat hf
  by_cases h91 : e.pc = 91
  · have hX := hmax.1
    have hFw := follow_of hp X hX
    refine alloc_quiet_steps hp (Prog.nextEnv hp hs hmax) hFw hpd hrel hn hub (fun ins hins => ?_)
      fun hr n col h => Prog.allocZero hIn hp hX hFw hr n col h
    rw [h91] at hins
    simpa [hins] using st_alloc
  · refine Prog.rowGen hIn hp hpub X (At := fun _ pc => MbarRow.StartupAt pc ∧ pc ≠ 91)
      (Wp := (· ∈ ([] : List Nat))) ?_ (fun hw => (List.not_mem_nil hw).elim)
      (fun _ hw => (List.not_mem_nil hw).elim) (fun _ hw => (List.not_mem_nil hw).elim) hs hmax
      hpd hrel hn hub ⟨hat, h91⟩ hf
    intro g pc hat ins hins
    obtain ⟨h103, h91'⟩ := hat
    rcases Prog.scanOf (a := 0) st_code_all pc (Nat.zero_le _)
      (by simp only [MbarRow.StartupAt] at h103; omega) ins hins with h | h | h
    · exact (h91' (by simpa using h)).elim
    · exact .inr (.inl h)
    · exact .inr (.inr h)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
