-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietColl
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.QuietWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollPcs

@[expose] public section

/-! # The MMA warp's quiet row

Every pc of the MMA code (1850-2161) holds a quiet instruction, the election (1853, a warp
collective with the full mask) or one of four waits, which cannot fail as a next event
(`Prog.rowGen`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

private theorem mma_code_all : (((kernel.code.drop 1850).take 312).zipIdx).all
    (fun p => decide (p.2 + 1850 ∈ [1931, 1983, 2012, 2107]) || quietOk p.1.op ||
      collInsB p.1) = true := by
  decide +kernel

private theorem mma_wait_ops : [1931, 1983, 2012, 2107].all
    (fun pc => kernel.code[pc]?.any fun i => Sched.waitOp i.op) = true := by
  decide +kernel

/-- **The MMA warp's quiet row.** -/
theorem Prog.mmaRow (hIn : Top.Inputs P L m) (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (X : Execution) : NextRow.Quiet P L m X (MbarRow.MmaAt L) :=
  Prog.rowGen hIn hp hpub X (Wp := (· ∈ [1931, 1983, 2012, 2107]))
    (fun {g pc} hat ins hins => by
      obtain ⟨-, hlo, hhi⟩ := hat
      exact Prog.scanOf mma_code_all pc hlo (by omega) ins hins)
    (fun {pc} hw => Prog.waitPcs mma_wait_ops pc hw)
    (fun {g pc l q ok sc} hat hw _ hFw hn => by
      obtain ⟨-, hlo, hhi⟩ := hat
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      have hr : 1853 ≤ pc ∧ pc ≤ 2160 := by omega
      rcases mma_next hp hFw hn (fun f h => by cases h) hr with
        ⟨-, _, hk⟩ | ⟨-, _, hk⟩ | ⟨-, _, _, _, hk⟩ | ⟨-, _, _, _, hk⟩ | ⟨hnw, -⟩
      all_goals first
        | exact (hnw _ _ _ _ _ rfl).elim
        | (simp only [Kind.wait.injEq] at hk; obtain ⟨rfl, -⟩ := hk; exact ⟨_, rfl, by omega⟩))
    (fun {g pc l q ok sc} hat _ hFw hmax hnu hpd hrel hn hf hfin => by
      obtain ⟨-, hlo, hhi⟩ := hat
      exact mma_quietWait hp hFw hmax hnu hpd hrel ⟨hlo, hhi⟩ hn hf hfin)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
