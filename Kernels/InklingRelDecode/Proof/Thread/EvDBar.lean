-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-!
# The twelve mbarriers of the kernel, by function

The default partition's prologue initializes twelve mbarriers in shared memory, each with arrival
count 1, in the order `kv_ready 0`, `kv_empty 0`, `kv_ready 1`, `kv_empty 1`, `kv_ready 2`,
`kv_empty 2`, `s_ready 0`, `p_ready 0`, `s_ready 1`, `p_ready 1`, `o_done`, `o_final`
(the PTX has one `mbarrier.init` per barrier). The layers above the thread layer name a barrier
by its function, never by a register or a pc:

* `kvReady slot` and `kvEmpty slot`, the three-slot K/V ring (`slot = iteration % 3`);
* `sReady b` and `pReady b`, the two-buffer S/P handshake (`b = iteration % 2`);
* `oDone`, the MMA warp's signal that an `O` update finished, and `oFinal`, that the last one did.

`Bar.off` is the offset of the barrier from the shared base `Launch.sharedBase`. The prologue
machine proves that each initialized address is `sharedBase + off` of its barrier
(`EvDProInit`), and the epilogue machine that its poll is on `oFinal` (`EvDEpiSync`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.EvD
open PTX PTX.Kernels.InklingRelDecode

/-- The mbarriers, named by function. -/
inductive Bar where
  | kvReady (slot : Fin 3) | kvEmpty (slot : Fin 3)
  | sReady (buf : Fin 2) | pReady (buf : Fin 2)
  | oDone | oFinal
  deriving DecidableEq

/-- Offset of the barrier's 8-byte object from the shared base. -/
def Bar.off : Bar → Nat
  | .kvReady s => 213216 + 8 * s.val
  | .kvEmpty s => 213248 + 8 * s.val
  | .sReady b => 213280 + 8 * b.val
  | .pReady b => 213296 + 8 * b.val
  | .oDone => 213312
  | .oFinal => 213328

/-- The barrier's object in the shared memory of CTA `cta`. -/
def Bar.loc (L : Launch) (cta : Nat) (b : Bar) : Loc := ⟨.shared, cta, L.sharedBase + b.off⟩

/-- The ring barriers of iteration `it`: slot `it % 3` of `kv_ready` and `kv_empty`, buffer
`it % 2` of `s_ready` and `p_ready`. -/
def kvReadyOf (it : Nat) : Bar := .kvReady ⟨it % 3, Nat.mod_lt _ (by omega)⟩
def sReadyOf (it : Nat) : Bar := .sReady ⟨it % 2, Nat.mod_lt _ (by omega)⟩
def pReadyOf (it : Nat) : Bar := .pReady ⟨it % 2, Nat.mod_lt _ (by omega)⟩

/-- Every barrier object lies inside the kernel's shared window. -/
theorem Bar.off_lt (b : Bar) : b.off + 8 ≤ sharedBytes := by
  cases b with
  | kvReady s => have := s.isLt; simp only [Bar.off, sharedBytes]; omega
  | kvEmpty s => have := s.isLt; simp only [Bar.off, sharedBytes]; omega
  | sReady s => have := s.isLt; simp only [Bar.off, sharedBytes]; omega
  | pReady s => have := s.isLt; simp only [Bar.off, sharedBytes]; omega
  | oDone => simp only [Bar.off, sharedBytes]; omega
  | oFinal => simp only [Bar.off, sharedBytes]; omega

end PTX.Kernels.InklingRelDecode.Proof.EvD
