-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Table
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The object a lane's wait polls, from the lane's state

At a state of a role at one of the sixteen waits, an acquiring poll event fired from it polls an
object of the lane's CTA (`MbarRow.loc L g f` for a family `f`): the roles' event classes
(`<role>.ev_class`, as the next-event rows of `Common/Export.lean`), with no undefined behaviour
in the lane's trace taken from the execution (`¬ HasUb X`) and no next event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {e : Event}

/-- **A class of undefined behaviour counts none along a trace without it.** -/
theorem take_noUb_of_noUb {c : Event → Bool} (hc : ∀ f, c f = true → ∃ fl, f.kind = .ub fl)
    (hnu : ¬ HasUb X) (k : Nat) : ((X.tr g).take k).countP c = 0 := by
  refine List.countP_eq_zero.mpr fun f hf hcl => ?_
  obtain ⟨j, hget⟩ : ∃ j, X.get (g, j) = some f :=
    List.mem_iff_getElem?.mp (List.mem_of_mem_take hf)
  obtain ⟨fl, hfl⟩ := hc f hcl
  obtain ⟨pc, kd⟩ := f
  simp only at hfl
  subst hfl
  exact hnu ⟨_, _, _, hget⟩

/-- **A state of an execution without undefined behaviour has counted none.** -/
theorem state_ub0 (hnu : ¬ HasUb X) {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ)) : σ.2 .ub = 0 := by
  rw [state_count hσ .ub]
  exact take_noUb_of_noUb (fun f h => by
    obtain ⟨pc, kd⟩ := f
    cases kd with
    | ub fl => exact ⟨fl, rfl⟩
    | _ => simp [cls] at h) hnu _

variable {σ : (thread P L g).D} {l : Loc} {q : Nat} {ok : Bool} {sc : MbarScope}

/-- **The TMA warp's poll** at pc 2205, 2209, 2234 or 2245 is of an object of the lane's CTA. -/
theorem tma_loc (hp : Pre P L m) (hnu : ¬ HasUb X)
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ))
    (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hpc0 : 2162 ≤ e.pc ∧ e.pc < 2332) (hk : e.kind = .wait l q ok true sc) :
    ∃ f, l = MbarRow.loc L g f := by
  obtain ⟨d, n, rfl, hR, -, hE, hl, -⟩ := tma_state hJ hi hev hpc hpc0
  have hu : n (.tma .ub) = 0 := (state_count hσ (.tma .ub)).trans (take_noUb_of_noUb
    (X := X) (g := g) (c := Tma.cls .ub) (fun f h => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | ub fl => exact ⟨fl, rfl⟩
      | wait l q ok a sc => cases ok <;> simp [Tma.cls, Tma.kindOf] at h
      | _ => simp [Tma.cls, Tma.kindOf] at h) hnu _)
  rcases Tma.ev_class hp (hR (state_ub0 hnu hσ)) hu hl hE (fun f h => by rw [hk] at h; cases h)
    hpc0.2 with ⟨-, _, hk'⟩ | ⟨-, _, hk'⟩ | ⟨-, _, _, _, hk'⟩ | ⟨-, _, _, _, hk'⟩ | ⟨hnw, -⟩
  all_goals first
    | exact (hnw _ _ _ _ _ hk).elim
    | (rw [hk] at hk'; simp only [Kind.wait.injEq] at hk'; obtain ⟨rfl, -⟩ := hk'; exact ⟨_, rfl⟩)

/-- **The index warp's poll** at pc 2446 or 2534 is of an object of the lane's CTA. -/
theorem index_loc (hp : Pre P L m) (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hpc0 : 2332 ≤ e.pc ∧ e.pc < 2587) (hk : e.kind = .wait l q ok true sc) :
    ∃ f, l = MbarRow.loc L g f := by
  obtain ⟨d, n, rfl, -, hE, -⟩ := index_state hJ hi hev hpc hpc0
  rcases Index.ev_class hp hE (fun f h => by rw [hk] at h; cases h) hpc0.2 with
    ⟨-, _, _, _, hk'⟩ | ⟨-, _, _, _, hk'⟩ | ⟨-, hk'⟩ | ⟨hnw, -⟩
  all_goals first
    | exact (hnw _ _ _ _ _ hk).elim
    | (rw [hk] at hk'; simp only [Kind.wait.injEq] at hk'; obtain ⟨rfl, -⟩ := hk'; exact ⟨_, rfl⟩)
    | (rw [hk] at hk'; cases hk')

/-- **Warpgroup 2's poll** at pc 2644, 2677 or 2684 is of an object of the lane's CTA. -/
theorem dequant_loc (hp : Pre P L m) (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hpc0 : 2606 ≤ e.pc ∧ e.pc ≤ 3610) (hk : e.kind = .wait l q ok true sc) :
    ∃ f, l = MbarRow.loc L g f := by
  obtain ⟨d, n, rfl, -, hE, -⟩ := dequant_state hp hJ hi hev hpc ⟨hpc0.1, by omega⟩
  rcases Dequant.ev_class hp hE (fun f h => by rw [hk] at h; cases h) hpc0.2 with
    ⟨-, _, hk'⟩ | ⟨-, _, _, _, hk'⟩ | ⟨-, _, _, _, hk'⟩ | ⟨-, hk'⟩ | ⟨hnw, -⟩
  all_goals first
    | exact (hnw _ _ _ _ _ hk).elim
    | (rw [hk] at hk'; simp only [Kind.wait.injEq] at hk'; obtain ⟨rfl, -⟩ := hk'; exact ⟨_, rfl⟩)
    | (rw [hk] at hk'; cases hk')

/-- **The MMA warp's poll** at pc 1931, 1983, 2012 or 2107 is of an object of the lane's CTA. -/
theorem mma_loc (hp : Pre P L m) (hnu : ¬ HasUb X)
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ))
    (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hpc0 : 1853 ≤ e.pc ∧ e.pc ≤ 2160) (hk : e.kind = .wait l q ok true sc) :
    ∃ f, l = MbarRow.loc L g f := by
  obtain ⟨d, n, rfl, hR, hE, hl, -⟩ := mma_state hJ hi hev hpc ⟨by omega, by omega⟩
  have hR := hR (state_ub0 hnu hσ)
  have hc : (fun c => n (.mma c)) = fun c => (X.tr g).countP (Mma.cls c) :=
    funext fun c => (state_count hσ (.mma c)).trans (by rw [List.take_length]; rfl)
  rw [hc] at hR
  have hu : (X.tr g).countP (Mma.cls .ub) = 0 := by
    have := take_noUb_of_noUb (X := X) (g := g) (c := Mma.cls .ub) (fun f h => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | ub fl => exact ⟨fl, rfl⟩
      | wait l q ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf] at h
      | tc t => cases t <;> simp [Mma.cls, Mma.kindOf] at h
      | _ => simp [Mma.cls, Mma.kindOf] at h) hnu (X.tr g).length
    rwa [List.take_length] at this
  rcases Mma.ev_class hp hR hu hl hE (fun f h => by rw [hk] at h; cases h) hpc0.2 with
    ⟨-, _, hk'⟩ | ⟨-, _, hk'⟩ | ⟨-, _, _, _, hk'⟩ | ⟨-, _, _, _, hk'⟩ | ⟨hnw, -⟩
  all_goals first
    | exact (hnw _ _ _ _ _ hk).elim
    | (rw [hk] at hk'; simp only [Kind.wait.injEq] at hk'; obtain ⟨rfl, -⟩ := hk'; exact ⟨_, rfl⟩)

/-- **Warpgroup 0's poll** at pc 264, 272 or 1184 is of an object of the lane's CTA. -/
theorem wg0_loc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X)
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ))
    (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) (hev : (table P L).Ev g σ e) (hpc : e.pc = (thread P L g).pc σ)
    (hpc0 : 103 ≤ e.pc ∧ e.pc < 1842) (hk : e.kind = .wait l q ok true sc) :
    ∃ f, l = MbarRow.loc L g f := by
  obtain ⟨d, n, rfl, hR, hE, hw⟩ := wg0_state hJ hi hev hpc hpc0
  have hc : ∀ c, n (.wg0 c) = (X.tr g).countP (Wg0.cls c) := fun c =>
    (state_count hσ (.wg0 c)).trans (by rw [List.take_length]; rfl)
  have hu : n (.wg0 .ub) = 0 := by
    rw [hc]
    have := take_noUb_of_noUb (X := X) (g := g) (c := Wg0.cls .ub) (fun f h => by
      obtain ⟨pc, kd⟩ := f
      cases kd with
      | ub fl => exact ⟨fl, rfl⟩
      | wait l q ok a sc => cases ok <;> simp [Wg0.cls, Wg0.kindOf] at h
      | tc t => cases t <;> simp [Wg0.cls, Wg0.kindOf] at h
      | _ => simp [Wg0.cls, Wg0.kindOf] at h) hnu (X.tr g).length
    rwa [List.take_length] at this
  have hP : ∀ l, okPolls l (X.tr g) = n (.wg0 (.acq l)) := fun l => by
    have h := wg0_okPolls hp hX hFw hw (X.tr g).length l
    rw [List.take_length] at h
    rw [h, hc]
  rcases Wg0.ev_class hp (hR (state_ub0 hnu hσ)) hu hP hE
      (fun f h => by rw [hk] at h; cases h) hpc0.2 with
    ⟨-, hk'⟩ | ⟨-, hk'⟩ | ⟨-, hk'⟩ | ⟨hnw, -⟩
  all_goals first
    | exact (hnw _ _ _ _ _ hk).elim
    | (obtain ⟨ok', hk'⟩ := hk'; rw [hk] at hk'; simp only [Kind.wait.injEq] at hk';
       obtain ⟨rfl, -⟩ := hk'; exact ⟨_, rfl⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
