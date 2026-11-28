-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QuietColl
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollPcs

@[expose] public section

/-! # Warpgroup 1's head and idle code: the quiet row

Pcs 1842-1849 (the register request, the shuffle at 1843 that reads the warp index, and the
dispatch) and 2587-2605 (the idle code) hold a quiet instruction or the shuffle, a warp collective
with an immediate static part. The code polls no mbarrier. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0}

private theorem wg1_head_all : (((kernel.code.drop 1842).take 8).zipIdx).all
    (fun p => quietOk p.1.op || collInsB p.1) = true := by
  decide +kernel

private theorem wg1_idle_all : (((kernel.code.drop 2587).take 19).zipIdx).all
    (fun p => quietOk p.1.op || collInsB p.1) = true := by
  decide +kernel

/-- **Warpgroup 1's quiet row.** -/
theorem Prog.wg1Row (hIn : Top.Inputs P L m) (hp : Pre P L m) (hpub : Prog.StorePub P L m)
    (X : Execution) : NextRow.Quiet P L m X (MbarRow.Wg1At L) := by
  intro hs hmax g e hpd hrel hn hub hat hf
  obtain ⟨-, -, hpc⟩ := hat
  refine Prog.quietColl hIn hp hpub hs hmax hpd hrel hn hub fun ins hins => ?_
  have h : quietOk ins.op || collInsB ins = true := by
    rcases hpc with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact code_scan (a := 1842) (n := 8) (F := fun _ i => quietOk i.op || collInsB i)
        wg1_head_all e.pc hlo (by omega) ins hins
    · exact code_scan (a := 2587) (n := 19) (F := fun _ i => quietOk i.op || collInsB i)
        wg1_idle_all e.pc hlo (by omega) ins hins
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact .inl h
  · exact .inr (by simpa [collInsB, CollIns] using h)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
