-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Startup
public import Lemmas.Kernel.Progress.Rank
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime

@[expose] public section

/-! # The state after an allocation request

The state of a lane right after its allocation request is the startup's store of the word (lane
0) or its read-back, at pc 91 either way (`alloc_state`, `alloc_pc_at`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- The state after an allocation: the store for lane 0, the read-back otherwise. -/
theorem alloc_state {k pc n : Nat} {grp : CtaGroup} {dst : Option Loc}
    (ha : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) (hpc : StartupAt pc) :
    pc = 91 ∧ ∃ x1 x2 n', Frame.stateAt (thread P L) X g (k + 1) = some (some
      (.inl ⟨if PTX.laneOf L g = 0 then .allocSt else .ld, x1, x2⟩, n')) := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw ha (fun f h => by cases h)
  obtain ⟨⟨site, x1, x2⟩, n0, rfl, -, -, hE, hx, hp91⟩ := startup_state hJ hi hev hpc' hpc
  obtain rfl : site = .alloc := by
    cases site with
    | alloc => rfl
    | sh j => fin_cases j <;> obtain ⟨r, ok, h⟩ := hE <;> cases h
    | elect j => obtain ⟨_, _, -, h⟩ := hE; cases h
    | allocSt => obtain ⟨col, -, h⟩ := hE; cases h
    | ld => rcases hE with ⟨a, bs, h, -⟩ | ⟨f, h⟩ <;> cases h
    | enter r => simp [Startup.exitOf] at hx
    | _ => simp [Startup.Ev] at hE
  refine ⟨hp91, x1, x2, Code.bump cls n0 ⟨pc, .tc (.resource grp dst (.alloc n))⟩, ?_⟩
  rw [Frame.stateAt_succ (C := thread P L) (show (X.tr g)[k]? = some _ from ha), hσ]
  change (thread P L g).next (.inl ⟨.alloc, x1, x2⟩, n0) _ = _
  rw [next_startup]
  have hs : Startup.succ L g ⟨.alloc, x1, x2⟩ ⟨pc, .tc (.resource grp dst (.alloc n))⟩ =
      some (some ⟨if PTX.laneOf L g = 0 then .allocSt else .ld, x1, x2⟩) := by
    simp only [Startup.succ]
    split_ifs <;> rfl
  rw [hs]
  simp only [Option.map_some]
  rw [Code.enter_none (Code.gatedExit_none.mpr (by
    simp only [startupEnter, Startup.exitOf]; split_ifs <;> rfl))]


/-- **Lane 0's state after its last event, an allocation, is at the allocation's pc.** -/
theorem alloc_pc_at {k pc n : Nat} {grp : CtaGroup} {dst : Option Loc} {σ : (thread P L g).D}
    (ha : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) (hpc : StartupAt pc)
    (hl : PTX.laneOf L g = 0) (hk : (X.tr g).length = k + 1)
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ)) :
    (thread P L g).pc σ = 91 := by
  obtain ⟨-, x1, x2, n', hσ0⟩ := alloc_state hp hX hFw ha hpc
  simp only [hl, ↓reduceIte] at hσ0
  rw [hk, hσ0] at hσ
  cases hσ
  rfl

end
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
