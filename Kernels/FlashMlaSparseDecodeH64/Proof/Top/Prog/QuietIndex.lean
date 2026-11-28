-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietColl
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.QuietWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollPcs

@[expose] public section

/-! # The index warp's quiet row

Every pc of the index code (2332-2586) holds a quiet instruction, a warp collective with a static
part (the four shuffles 2464, 2467, 2553, 2556), or one of the two waits (2446, 2534), which
cannot fail as a next event and whose polled slot has a final state. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

private theorem ix_code_all : (((kernel.code.drop 2332).take 255).zipIdx).all
    (fun p => p.2 + 2332 == 2446 || p.2 + 2332 == 2534 || quietOk p.1.op || collInsB p.1) =
      true := by
  decide +kernel

/-- **The index warp's quiet row.** -/
theorem Prog.indexRow (hIn : Top.Inputs P L m) (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (X : Execution) : NextRow.Quiet P L m X (MbarRow.IndexAt L) := by
  intro hs hmax g e hpd hrel hn hub hat hf
  obtain ⟨-, hlo, hhi⟩ := hat
  have hX := hmax.1
  have hFw := follow_of hp X hX
  have hnu := Sched.safe_noUb (hs.2 X hX)
  by_cases hw : e.pc = 2446 ∨ e.pc = 2534
  · obtain ⟨ins, hins⟩ : ∃ ins, kernel.code[e.pc]? = some ins :=
      Option.isSome_iff_exists.mp (by rcases hw with h | h <;> rw [h] <;> decide +kernel)
    have hwo : Sched.waitOp ins.op = true := by
      have : [2446, 2534].all (fun pc => kernel.code[pc]?.all fun i => Sched.waitOp i.op) =
          true := by decide +kernel
      have h := List.all_eq_true.mp this e.pc (by rcases hw with h | h <;> simp [h])
      rw [hins] at h
      simpa using h
    obtain ⟨l, q, ok, sc, hkd⟩ := next_wait hn hub hins hwo
    obtain ⟨pc, kd⟩ := e
    simp only at hkd hlo hhi hw hf hins
    subst hkd
    have hfin := Prog.objFinal hIn hp hX hrel hn hub (by show 97 < pc; omega) hpd.1
    rcases index_next hp hFw hn hub ⟨hlo, hhi⟩ with ⟨-, b, q', ok', hk⟩ | ⟨-, b, q', ok', hk⟩ |
        ⟨h2585, -⟩ | ⟨hnw, -⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact index_quietWait hp hFw hmax hnu hpd hrel ⟨hlo, hhi⟩ hn hf (hfin _)
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact index_quietWait hp hFw hmax hnu hpd hrel ⟨hlo, hhi⟩ hn hf (hfin _)
    · simp only at h2585
      omega
    · exact (hnw l q ok true sc rfl).elim
  · refine Prog.quietColl hIn hp hpub hs hmax hpd hrel hn hub fun ins hins => ?_
    have h := code_scan (a := 2332) (n := 255) (F := fun pc i =>
      pc == 2446 || pc == 2534 || quietOk i.op || collInsB i) ix_code_all e.pc hlo
      (by omega) ins hins
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ((h | h) | h) | h
    · exact (hw (.inl (by omega))).elim
    · exact (hw (.inr (by omega))).elim
    · exact .inl h
    · exact .inr (by simpa [collInsB, CollIns] using h)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
