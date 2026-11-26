-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots

@[expose] public section

/-! # The time table of the thread machine

The progress descent ranks a pending thread by the time of its state (`Sched.Timed`,
`Sched.rank`). The glued table `time` is assembled from the roles' local times: the startup at
`Startup.time` (below `100`), every warpgroup's state from `roleBase` on; warpgroup 1's head at
`roleBase + Wg1.time` and its idle code at `idleBase + Wg1.itime`, its barrier 12 at `endSlot`
(`Lib/Slots.lean`: every role's barrier 12 is there). Every role's slot below (`wg0Time`,
`dequantTime`, `mmaTime`, `tmaTime`, `indexTime`) holds its lane's time. The name the progress
layer uses, `timed P L`, is declared opaquely in `Common/Follow.lean` (its body is
`⟨thread P L, time P L⟩`, `Common/FollowView.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The first time of the warpgroups' states: after every startup state. -/
def roleBase : Nat := 100

/-- The first time of the idle code: after the head. -/
def idleBase : Nat := roleBase + 3

/-! ### The slots -/

/-- **Slot `Wg0`**: warpgroup 0's time, its place (`Wg0/Time.lean`) from `roleBase` on. -/
def wg0Time (P : Params) (L : Launch) (g : Nat) :
    (wg0Code P L g (warpW L g)).D → (Cls → Nat) → Nat :=
  fun d _ => roleBase + Wg0.time d

/-- **Slot `Dequant`**: warpgroup 2's time, its place (`Dequant/Time.lean`) from `idleBase + 29`
on: its wait on `bar_q_utccp` (place 3) is at the slot of the MMA lane's commit. -/
def dequantTime (P : Params) (L : Launch) (g : Nat) :
    (dequantCode P L g (warpW L g)).D → (Cls → Nat) → Nat :=
  fun d _ => idleBase + 29 + Dequant.time d

/-- **Slot `Mma`**: the MMA warp's time, its place in the role's order (`Mma/Time.lean`). -/
def mmaTime (P : Params) (L : Launch) (g : Nat) : (mmaCode P L g).D → (Cls → Nat) → Nat :=
  fun d _ => idleBase + Mma.time d

/-- **Slot `Tma`**: the TMA warp's time, its place in the role's order (`Tma/Time.lean`) from
`idleBase + 29` on: its wait on `bar_q_utccp` (place 3) is at the slot of the MMA lane's commit
(`idleBase + 32`), every later state above it. -/
def tmaTime (P : Params) (L : Launch) (g : Nat) : (tmaCode P L g).D → (Cls → Nat) → Nat :=
  fun d _ => idleBase + 29 + Tma.time d

/-- **Slot `Index`**: the index warp's time, its place (`Index/Time.lean`, read from its counts)
from `idleBase = ixOrg` on: block `r`'s site at `frame r + ord`. -/
def indexTime (P : Params) (L : Launch) (g : Nat) : (indexCode P L g).D → (Cls → Nat) → Nat :=
  fun d n => idleBase + Index.time L g d (fun c => n (.index c))

/-- The idle code's time: its loads after the head, barrier 12 at `endSlot`, the return after. -/
def idleTime : IdleSite → Nat
  | .bar => endSlot
  | .ret => endSlot + 1
  | s => idleBase + Wg1.itime s

/-- **Slot `Wg1`**: the head, then its sub-roles; a stub of the dispatch level at `idleBase`. -/
def wg1Time (P : Params) (L : Launch) (g : Nat) : (wg1Code P L g).D → (Cls → Nat) → Nat
  | .inl s, _ => roleBase + Wg1.time s
  | .inr ⟨.inl .mma, d⟩, n => mmaTime P L g d n
  | .inr ⟨.inl .tma, d⟩, n => tmaTime P L g d n
  | .inr ⟨.inl .index, d⟩, n => indexTime P L g d n
  | .inr ⟨.inl .idle, s⟩, _ => idleTime s
  | .inr ⟨.inr _, _⟩, _ => idleBase

/-! ### The table -/

/-- The time of each warpgroup's state. -/
def fragTime (P : Params) (L : Launch) (g : Nat) :
    (i : Entry) → (frag P L g i).D → (Cls → Nat) → Nat
  | .wg0 => wg0Time P L g
  | .wg1 => wg1Time P L g
  | .dequant => dequantTime P L g

/-- **The time of a state of the thread machine**; a stub's is `roleBase`. -/
def time (P : Params) (L : Launch) (g : Nat) : (thread P L g).D → Nat
  | (.inl d, _) => Startup.time d
  | (.inr ⟨.inl i, d⟩, n) => fragTime P L g i d n
  | (.inr ⟨.inr _, _⟩, _) => roleBase

/-- **Every time is at least `2`** (the wait-step's lower bound). -/
theorem time_ge (P : Params) (L : Launch) (g : Nat) (σ : (thread P L g).D) :
    2 ≤ time P L g σ := by
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d⟩
  · exact Startup.time_ge d
  · cases i with
    | wg0 => simp only [time, fragTime, wg0Time, roleBase]; omega
    | dequant => simp only [time, fragTime, dequantTime, idleBase, roleBase]; omega
    | wg1 =>
      rcases d with s | ⟨j | r, d⟩
      · simp only [time, fragTime, wg1Time, roleBase]
        omega
      · cases j
        case idle =>
          cases d <;> simp only [time, fragTime, wg1Time, idleTime, Wg1.itime, idleBase, roleBase,
            endSlot, loopBase, stride, blockCap] <;> omega
        all_goals simp only [time, fragTime, wg1Time, mmaTime, tmaTime, indexTime, idleBase,
          roleBase]; omega
      · simp [time, fragTime, wg1Time, idleBase, roleBase]
  · simp [time, roleBase]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
