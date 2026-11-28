-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietColl
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.QuietWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.VoteRel
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollPcs
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Group
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.NextEnv
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Store

@[expose] public section

/-! # Warpgroup 0's quiet row

Every pc of warpgroup 0's code (103-1841) holds a quiet instruction, a warp collective with a
static part (the elections), one of three waits (264, 272, 1184), or the mode vote at 578. The
waits cannot fail as a next event (`Prog.rowGen`), the vote steps with the other lanes of its
warp (`vote_quiet_steps`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

private theorem wg0_code_all : (((kernel.code.drop 103).take 1739).zipIdx).all
    (fun p => decide (p.2 + 103 ∈ [264, 272, 1184, 578]) || quietOk p.1.op ||
      collInsB p.1) = true := by
  decide +kernel

private theorem wg0_wait_ops : [264, 272, 1184].all
    (fun pc => kernel.code[pc]?.any fun i => Sched.waitOp i.op) = true := by
  decide +kernel

/-- **Warpgroup 0's quiet row.** -/
theorem Prog.wg0Row (hIn : Top.Inputs P L m) (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (X : Execution) : NextRow.Quiet P L m X (MbarRow.Wg0At L) := by
  intro hs hmax g e hpd hrel hn hub hat hf
  by_cases hv : e.pc = 578
  · have hX := hmax.1
    have hFw := follow_of hp X hX
    have hnu := Sched.safe_noUb (hs.2 X hX)
    have hR := hIn.bar hp X hX hFw
    exact vote_quiet_steps hp (Prog.nextEnv hp hs hmax) hs hFw
      (fun h => Prog.drained hp hpub hs hmax h)
      (vote_rel hp hX hFw hnu fun hg he => by
        obtain ⟨q, h1, h2, -⟩ := bar_group hp hR hg he
        exact ⟨q, h1, h2⟩) hpd hn hub hv
  · refine Prog.rowGen hIn hp hpub X (At := fun g pc => MbarRow.Wg0At L g pc ∧ pc ≠ 578)
      (Wp := (· ∈ [264, 272, 1184])) ?_ (fun {pc} hw => Prog.waitPcs wg0_wait_ops pc hw)
      ?_ ?_ hs hmax hpd hrel hn hub ⟨hat, hv⟩ hf
    · intro g pc hat ins hins
      obtain ⟨⟨-, hlo, hhi⟩, h578⟩ := hat
      rcases Prog.scanOf wg0_code_all pc hlo (by omega) ins hins with h | h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h | h
        · exact .inl (by simp [h])
        · exact .inl (by simp [h])
        · exact .inl (by simp [h])
        · exact (h578 h).elim
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · intro g pc l q ok sc hat hw hX hFw hn
      obtain ⟨⟨-, hlo, hhi⟩, -⟩ := hat
      rcases wg0_next hp hX hFw hn (fun f h => by cases h) ⟨hlo, hhi⟩ with
        ⟨-, _, hk⟩ | ⟨-, _, hk⟩ | ⟨-, _, hk⟩ | ⟨hnw, -⟩
      all_goals first
        | exact (hnw _ _ _ _ _ rfl).elim
        | (simp only [Kind.wait.injEq] at hk
           obtain ⟨rfl, -⟩ := hk
           exact ⟨_, rfl, by omega⟩)
    · intro g pc l q ok sc hat hw hFw hmax hnu hpd hrel hn hf hfin
      obtain ⟨⟨-, hlo, hhi⟩, -⟩ := hat
      exact wg0_quietWait hp hFw hmax hnu hpd hrel ⟨hlo, hhi⟩ hn hf hfin

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
