-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietColl
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.QuietWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollPcs

@[expose] public section

/-! # The TMA warp's quiet row

Every pc of the TMA code (2162-2331) holds a quiet instruction, the election (2165, a warp
collective with the full mask) or one of four waits, which cannot fail as a next event
(`Prog.rowGen`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

private theorem tma_code_all : (((kernel.code.drop 2162).take 170).zipIdx).all
    (fun p => decide (p.2 + 2162 ∈ [2205, 2209, 2234, 2245]) || quietOk p.1.op ||
      collInsB p.1) = true := by
  decide +kernel

private theorem tma_wait_ops : [2205, 2209, 2234, 2245].all
    (fun pc => kernel.code[pc]?.any fun i => Sched.waitOp i.op) = true := by
  decide +kernel

/-- **The TMA warp's quiet row.** -/
theorem Prog.tmaRow (hIn : Top.Inputs P L m) (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (X : Execution) : NextRow.Quiet P L m X (MbarRow.TmaAt L) :=
  Prog.rowGen hIn hp hpub X (Wp := (· ∈ [2205, 2209, 2234, 2245]))
    (fun {g pc} hat ins hins => by
      obtain ⟨-, hlo, hhi⟩ := hat
      exact Prog.scanOf tma_code_all pc hlo (by omega) ins hins)
    (fun {pc} hw => Prog.waitPcs tma_wait_ops pc hw)
    (fun {g pc l q ok sc} hat _ _ hFw hn => by
      obtain ⟨-, hlo, hhi⟩ := hat
      rcases tma_next hp hFw hn (fun f h => by cases h) ⟨hlo, hhi⟩ with
        ⟨-, _, hk⟩ | ⟨-, _, hk⟩ | ⟨-, _, _, _, hk⟩ | ⟨-, _, _, _, hk⟩ | ⟨hnw, -⟩
      all_goals first
        | exact (hnw _ _ _ _ _ rfl).elim
        | (simp only [Kind.wait.injEq] at hk; obtain ⟨rfl, -⟩ := hk; exact ⟨_, rfl, by omega⟩))
    (fun {g pc l q ok sc} hat _ hFw hmax hnu hpd hrel hn hf hfin => by
      obtain ⟨-, hlo, hhi⟩ := hat
      exact tma_quietWait hp hFw hmax hnu hpd hrel ⟨hlo, hhi⟩ hn hf hfin)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
