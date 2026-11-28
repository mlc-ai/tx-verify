-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Window
import Kernels.InklingRelDecode.Proof.Common.Where

@[expose] public section

/-! # A state of the value machine at position 574 is the first softmax state

The prologue's exit site has position 574 too, but it is no state of the thread machine (the
hand-off enters the softmax at once). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {g : Nat}

private theorem site_574 (s : Prologue.Site) (h : s.pc = 574) : s = .exit := by
  revert h
  cases s <;> try (intro _; rfl)
  all_goals (repeat' (rename_i j; revert j))
  all_goals decide +kernel

/-- **A state of the value machine at position 574 is a softmax state.** -/
theorem soft_574 {d : (lateThread Q L g).D} (hinv : (lateThread Q L g).inv d)
    (hpc : (lateThread Q L g).pc d = 574) : ∃ w ent s n, d = softSt w ent s n := by
  obtain ⟨s, n⟩ := d
  rcases s with ⟨s, tm, x, w⟩ | ⟨r, s⟩
  · exfalso
    change s.pc = 574 at hpc
    revert hpc
    cases s <;> first | decide | (rename_i r; cases r <;> decide)
  · rcases r with r | r
    · cases r with
      | prologue w =>
        rcases s with s | ⟨e, s | ⟨⟨⟩, s⟩⟩
        · exfalso
          have no : dataExit Q L g w (prologueErase Q L g w s) = none := hinv.2
          have hs : s.c.site = .exit := site_574 _ hpc
          simp [dataExit, prologueErase, hs] at no
        · exact ⟨w, e, s, n, rfl⟩
        · exfalso
          have := (Epilogue.Site.pc_range s.site).1
          change s.site.pc = 574 at hpc
          omega
      | dispatch w x =>
        exfalso
        rcases s with ⟨s, i⟩ | ⟨r, s⟩
        · change s.pc = 574 at hpc
          revert hpc
          cases s <;> decide
        · have bounds : 2337 ≤ (workerFrag Q L g w x r).pc s := by
            cases r with
            | mma =>
              change 2337 ≤ s.site.pc
              generalize s.site = site
              cases site <;> first | decide | (rename_i j; fin_cases j <;> decide)
            | loader =>
              change 2337 ≤ s.site.pc
              generalize s.site = site
              cases site <;> first | decide | (rename_i j; fin_cases j <;> decide) |
                (rename_i j b; fin_cases j <;> cases b <;> decide)
          have : (workerFrag Q L g w x r).pc s = 574 := hpc
          omega
    · exfalso
      cases r <;> first | (change (27 : Nat) = 574 at hpc; omega) |
        (change (2337 : Nat) = 574 at hpc; omega)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
