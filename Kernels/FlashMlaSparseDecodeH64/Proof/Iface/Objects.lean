-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

/-! # The kernel's synchronization objects: vocabulary

The 23 mbarriers of `SharedMemoryPlan` by family (`Data/Barriers.lean`, `config.h:166-171`), with
their byte offsets from the dynamic shared base and their expected arrival counts, and the named
CTA barriers the code uses (ids 0, 9, 10, 11, 12) with their thread counts. Nothing here is a
statement about executions: the families are the objects the cross-lane predicates of `Iface/`
and the channels of `Protocol/` will speak of.

| family | offset | count | producer side | consumer side |
| - | - | - | - | - |
| `lastStoreDone` | 222768 | 128 | warpgroup 0 | warpgroup 0 |
| `qTma` | 222776 | 1 | Q tensor load | MMA |
| `qUtccp` | 222784 | 1 | MMA commit (Q copy) | warpgroup 2 |
| `dequantReady b` | 222792 + 8b | 128 | warpgroup 2 | MMA |
| `rawReady b` | 222808 + 8b | 1 | gather4 loads | warpgroup 2 |
| `rawFree b` | 222824 + 8b | 128 | warpgroup 2 | TMA warp |
| `coordReady s` | 222840 + 8s | 32 | index warp | TMA warp, warpgroups 0 and 2 |
| `coordFree s` | 222872 + 8s | 129 | warpgroup 0, TMA lane | index warp |
| `qkDone b` | 222904 + 8b | 1 | MMA commit (QK) | warpgroup 0 |
| `soReady b` | 222920 + 8b | 128 | warpgroup 0 | MMA |
| `svDone b` | 222936 + 8b | 1 | MMA commit (PV) | warpgroups 0 and 2 |
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

/-- **The mbarrier families.** `b` is a double-buffer stage, `s` a slot of the 4-slot index
ring. -/
inductive MbarFam where
  | lastStoreDone
  | qTma
  | qUtccp
  | dequantReady (b : Fin 2)
  | rawReady (b : Fin 2)
  | rawFree (b : Fin 2)
  | coordReady (s : Fin 4)
  | coordFree (s : Fin 4)
  | qkDone (b : Fin 2)
  | soReady (b : Fin 2)
  | svDone (b : Fin 2)
  deriving DecidableEq, Repr

namespace MbarFam

/-- The byte offset of the mbarrier from the dynamic shared base. -/
def off : MbarFam → Nat
  | lastStoreDone => 222768
  | qTma => 222776
  | qUtccp => 222784
  | dequantReady b => 222792 + 8 * b.val
  | rawReady b => 222808 + 8 * b.val
  | rawFree b => 222824 + 8 * b.val
  | coordReady s => 222840 + 8 * s.val
  | coordFree s => 222872 + 8 * s.val
  | qkDone b => 222904 + 8 * b.val
  | soReady b => 222920 + 8 * b.val
  | svDone b => 222936 + 8 * b.val

/-- The expected arrival count the startup initializes the mbarrier with. -/
def count : MbarFam → Nat
  | lastStoreDone => 128
  | qTma => 1
  | qUtccp => 1
  | dequantReady _ => 128
  | rawReady _ => 1
  | rawFree _ => 128
  | coordReady _ => 32
  | coordFree _ => 129
  | qkDone _ => 1
  | soReady _ => 128
  | svDone _ => 1

/-- All 23 mbarriers, in the order of their offsets. -/
def all : List MbarFam :=
  [lastStoreDone, qTma, qUtccp, dequantReady 0, dequantReady 1, rawReady 0, rawReady 1,
    rawFree 0, rawFree 1, coordReady 0, coordReady 1, coordReady 2, coordReady 3,
    coordFree 0, coordFree 1, coordFree 2, coordFree 3, qkDone 0, qkDone 1, soReady 0,
    soReady 1, svDone 0, svDone 1]

theorem mem_all (f : MbarFam) : f ∈ all := by
  cases f
  all_goals first
    | decide
    | (rename_i b; revert b; decide)

/-- The offset names the mbarrier. -/
theorem off_inj {f f' : MbarFam} (h : f.off = f'.off) : f = f' := by
  have hall : ∀ f ∈ all, ∀ f' ∈ all, f.off = f'.off → f = f' := by decide
  exact hall f (mem_all f) f' (mem_all f') h

/-- Every mbarrier is an aligned 8-byte word of the barrier block `[222768, 222952)`. -/
theorem off_range (f : MbarFam) : 222768 ≤ f.off ∧ f.off + 8 ≤ 222952 ∧ f.off % 8 = 0 := by
  have hall : ∀ f ∈ all, 222768 ≤ f.off ∧ f.off + 8 ≤ 222952 ∧ f.off % 8 = 0 := by decide
  exact hall f (mem_all f)

end MbarFam

/-- The mbarrier of family `f` in CTA `cta`. -/
def mbarLoc (L : Launch) (cta : Nat) (f : MbarFam) : Loc :=
  ⟨.shared, cta, L.sharedBase + f.off⟩

/-! ### Named barriers -/

/-- **The named CTA barriers** the code uses (`Data/Barriers.lean`): the startup's `bar.sync 0`
of all 384 threads, warpgroup 0's `wg0_sync` (9, 128 threads), its warp-pair barriers (10 for
warps 0 and 2, 11 for warps 1 and 3, 64 threads each), and `everyone_sync` (12, 384 threads)
at the end of every role. -/
inductive NamedBar where
  | cta
  | wg0
  | pair (odd : Bool)
  | everyone
  deriving DecidableEq, Repr

namespace NamedBar

/-- The PTX id. -/
def id : NamedBar → Nat
  | cta => 0
  | wg0 => 9
  | pair odd => if odd then 11 else 10
  | everyone => 12

/-- The number of participating threads. -/
def count : NamedBar → Nat
  | cta => 384
  | wg0 => 128
  | pair _ => 64
  | everyone => 384

/-- The barriers the code uses. -/
def all : List NamedBar := [cta, wg0, pair false, pair true, everyone]

theorem mem_all (b : NamedBar) : b ∈ all := by
  cases b
  all_goals first
    | decide
    | (rename_i o; cases o <;> decide)

end NamedBar

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
