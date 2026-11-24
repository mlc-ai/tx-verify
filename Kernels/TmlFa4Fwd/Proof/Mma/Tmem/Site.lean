-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
import Kernels.TmlFa4Fwd.Proof.Common.Roles

@[expose] public section

/-! # The MMA warp's resource operations by site

`Mma.tsite`: the resource operations before a site of the MMA warp's role (one, the allocation,
until the relinquishment; two after it; three after the deallocation), and `Mma.succ_tsite`: the
role reaches its last sites only in the order relinquish, barrier, deallocate, exit. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {g : Nat}

/-- A site of the MMA warp that issues a resource operation. -/
def Mma.isRD : Mma.Site → Bool
  | .relinq _ | .dealloc _ => true
  | _ => false

/-- The resource operations before a site of the MMA warp's role. -/
def Mma.tsite : Mma.Site → Nat
  | .bar2 _ | .dealloc _ => 2
  | .exit _ => 3
  | _ => 1

theorem Mma.tsite_wtNext : ∀ k, Mma.tsite (Mma.wtNext k) = 1 := by decide
theorem Mma.tsite_shNext : ∀ k, Mma.tsite (Mma.shNext k) = 1 := by decide
theorem Mma.tsite_qkDone : ∀ k, Mma.tsite (Mma.qkDone k) = 1 := by decide
theorem Mma.tsite_pvDone : ∀ k, Mma.tsite (Mma.pvDone k) = 1 := by decide

theorem Mma.tsite_passStart (late : Bool) (d : Mma.D) :
    Mma.tsite (Mma.passStart p L g late d).site = 1 := by
  cases late <;> simp only [Mma.passStart] <;> split_ifs <;> rfl

theorem Mma.tsite_ceNext (d : Mma.D) (c : Fin 12) : Mma.tsite (Mma.ceNext p L g d c).site = 1 := by
  fin_cases c <;> simp only [Mma.ceNext, Mma.enterLoop, Mma.loopEnd, Mma.tsite_passStart] <;>
    (try split) <;> rfl

theorem Mma.tsite_afterTotal (k : Epilogue.Scan) (d : Mma.D) (x : BitVec 64) :
    Mma.tsite (Mma.afterTotal p L g k d x).site = 1 := by
  cases k <;> simp only [Mma.afterTotal, Mma.scanExit, Mma.loopHead] <;> split_ifs <;> rfl

theorem Mma.tsite_afterTiles {d d' : Mma.D} {x : BitVec 64}
    (h : Mma.afterTiles p L g d x = some d') : Mma.tsite d'.site = 1 := by
  dsimp only [Mma.afterTiles] at h
  split_ifs at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

set_option maxHeartbeats 8000000 in
/-- **The MMA warp's role counts its resource operations by site.** -/
theorem Mma.succ_tsite {d d' : Mma.D} {e : Event} (h : Mma.succ p L g d e = some (some d')) :
    Mma.tsite d'.site = Mma.tsite d.site + (if Mma.isRD d.site then 1 else 0) := by
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Mma.succ, Mma.word32] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h; rfl)
    | (simp only [Option.some.injEq] at h; subst h; rw [Mma.tsite_afterTotal]; rfl)
    | (simp only [Option.map_eq_some_iff, Option.some.injEq] at h
       obtain ⟨d0, h0, rfl⟩ := h
       rw [Mma.tsite_afterTiles h0]; rfl)
    | (simp only [Option.some.injEq, reduceCtorEq] at h; subst h
       simp only [Mma.scAt, Mma.afterTiles, Mma.afterTotal,
         Mma.tsite_wtNext, Mma.tsite_shNext, Mma.tsite_qkDone, Mma.tsite_pvDone, Mma.tsite_ceNext,
         Mma.tsite_passStart, Mma.isRD]
       try simp only [Mma.tsite]
       repeat' split
       all_goals first | rfl | (simp_all; done))

end
end PTX.Kernels.TmlFa4Fwd.Proof
