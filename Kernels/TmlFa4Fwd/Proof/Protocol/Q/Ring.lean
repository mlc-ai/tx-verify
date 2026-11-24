-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TmaArr
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Obj
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepTma
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Top.Table
import Lemmas.Kernel.ElectSource
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The Q stages' ring: the electing lanes and the barrier objects

Every election of the code has the full mask, so the lanes of a warp that win elections are one
lane (`won_unique`, from `elect_winner`): the elected lane of warp 14 that arrives on and copies
into a Q stage, and the electing lane of warp 12 that reads it and commits its release. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The lanes of a warp that win elections are one lane**: two lanes of one warp that each won
an election of the full mask (at any two instances) are the same thread. -/
theorem won_unique (hX : Consistent L kernel Assumptions.all m X) {x y jx jy pcx pcy ix iy : Nat}
    (hw : SameWarp L x y)
    (hx : X.get (x, jx) = some ⟨pcx, .elect (2 ^ 32 - 1) ix (laneOf L x)⟩)
    (hy : X.get (y, jy) = some ⟨pcy, .elect (2 ^ 32 - 1) iy (laneOf L y)⟩) : x = y := by
  have hl := elect_winner hX (e := (x, jx)) (f := (y, jy)) hx hy hw
  simp only [laneOf] at hl
  obtain ⟨⟨-, -, hcta⟩, hww⟩ := hw
  have h1 := Nat.div_add_mod x L.block
  have h2 := Nat.div_add_mod y L.block
  have h3 := Nat.div_add_mod (x % L.block) 32
  have h4 := Nat.div_add_mod (y % L.block) 32
  rw [hcta] at h1
  rw [hww] at h3
  omega

/-- The won elections a loader lane's arrivals on a Q stage stand for are one at least. -/
theorem won_pos {n : Loader.Cnt → Nat} {o : Nat} (ho : QOff o)
    (h : 1 ≤ ((Loader.tmaArrPts o).map fun pc => n (.won pc)).sum) :
    ∃ pc ∈ Loader.tmaArrPts o, 1 ≤ n (.won pc) := by
  rcases ho with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, by simpa [Loader.tmaArrPts] using h⟩
  · simp only [Loader.tmaArrPts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero] at h
    by_cases h1 : 1 ≤ n (.won (Loader.tePc 2 0))
    · exact ⟨_, by simp [Loader.tmaArrPts], h1⟩
    · exact ⟨1896, by simp [Loader.tmaArrPts], by omega⟩

set_option maxHeartbeats 8000000 in
/-- **A loader lane that arrives on a Q stage has won an election before.** -/
theorem ld_arr_won (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {o : Nat} (ho : QOff o)
    {y k pc tx : Nat} {sc : MbarScope}
    (hw : Prologue.warpIndex L y = 14 ∨ Prologue.warpIndex L y = 15)
    (he : X.get (y, k) = some ⟨pc, .arrive (obj L y o) tx 1 true sc⟩) :
    ∃ j pc' inst, j < k ∧
      X.get (y, j) = some ⟨pc', .elect (2 ^ 32 - 1) inst (laneOf L y)⟩ := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  have hy := Frame.lt_of_get hX he
  obtain ⟨⟨σ1, n⟩, hσ, hJ, -, hev⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
    (S := fun g => g < L.threads) (fun g hg => thread_sound hp hg) hX hT hF hy he
    (fun f h => by cases h)
  have hR := (LdWarp.good hp hX hw hy rfl _).2 _ hσ
  rcases σ1 with s | ⟨i, d⟩
  · exfalso
    have h1 := hR.1
    obtain ⟨site, x1, x2, x3⟩ := s
    have hEv : Startup.Ev L y ⟨site, x1, x2, x3⟩ ⟨pc, .arrive (obj L y o) tx 1 true sc⟩ := hev
    cases site with
    | sh jj =>
      fin_cases jj <;> simp only [Startup.Ev] at hEv <;> obtain ⟨_, _, hk⟩ := hEv <;> cases hk
    | fence => simp only [Startup.Ev] at hEv; cases hEv
    | bar => simp only [Startup.Ev] at hEv; cases hEv
    | _ => simp only [StartAt] at h1
  cases i with
  | loader b =>
    obtain ⟨hbw, hR'⟩ := hR
    have hEv : Loader.Ev p L y (Loader.wOf b) d ⟨pc, .arrive (obj L y o) tx 1 true sc⟩ := hev
    -- the site is an expect-tx arrival of the stage
    have hpend : Loader.pendingArr d.site = some o := by
      obtain ⟨site, v, k2⟩ := d
      cases site <;> simp only [Loader.Ev] at hEv
      case ta t =>
        simp only [Kind.arrive.injEq] at hEv
        have hl := hEv.1.trans (Loader.ta_loc hp t)
        have := obj_inj (L := L) (g := y) hl
        simp only [Loader.pendingArr]
        rw [this]
      case da =>
        simp only [Kind.arrive.injEq] at hEv
        have hl := hEv.1.trans ((Loader.smLoc_sb hp 8 (by norm_num)).trans rfl)
        have := obj_inj (L := L) (g := y) hl
        simp only [Loader.pendingArr, this]
      all_goals (try simp only [Epilogue.Ev, Loader.Site.toE] at hEv)
      all_goals (try split at hEv)
      all_goals (try shape_destruct hEv)
      all_goals (simp only [reduceCtorEq, Kind.tc.injEq, TcKind.commit.injEq] at *)
    have hc := Loader.tma_arr hp hX hy hw hσ (ub_zero hX he hσ) o
      (by rcases ho with rfl | rfl <;> simp)
    simp only [Loader.pendAt, hpend, ite_true] at hc
    obtain ⟨pcw, -, hpos⟩ := won_pos ho (n := LdWarp.lcn n)
      (by simp only [LdWarp.lcn] at hc ⊢; omega)
    obtain ⟨j, hj, ⟨pcf, kd⟩, hf, hcl⟩ := exists_of_count hσ (c := .load (.won pcw)) hpos
    cases kd <;> simp [cls, Loader.cls] at hcl
    rename_i mask inst ld
    obtain ⟨-, rfl⟩ := hcl
    have hm := elect_full hX (show X.Elect (y, j) pcf mask inst (laneOf L y) from hf)
    subst hm
    exact ⟨j, pcf, inst, hj, hf⟩
  | _ => exact hR.elim

end
end PTX.Kernels.TmlFa4Fwd.Proof
