-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-!
# The twelve mbarriers of the kernel, as shared locations

The default partition initializes twelve mbarriers (count 1 each) in the order `kv_ready` 0,
`kv_empty` 0, `kv_ready` 1, `kv_empty` 1, `kv_ready` 2, `kv_empty` 2, `s_ready` 0, `p_ready` 0,
`s_ready` 1, `p_ready` 1, `o_done`, `o_final`. The ring barriers of the K/V tiles are indexed by
the slot `i % 3` of the iteration, those of the S and P tiles by `i % 2`. Their byte offsets from
the shared base agree with the value tables of the loader (`Loader.table`: `+213216 + 8 (i % 3)`
for `kv_ready`, `+213248 + 8 (i % 3)` for `kv_empty`) and of the MMA warp (`Mma.values`: also
`+213280 + 8 j` for `s_ready`, `+213296 + 8 j` for `p_ready`, `+213312` for `o_done`, `+213328` for
`o_final`).

`barLoc L cta off` is the location of the barrier at byte offset `off` of CTA `cta`'s window; the
named functions below fix the offsets. Event shapes of the roles name their barriers by these
functions only.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.EvW
open PTX

/-- Byte offsets of the barriers from the shared base. -/
def kvReadyOff (s : Nat) : Nat := 213216 + 8 * s
def kvEmptyOff (s : Nat) : Nat := 213248 + 8 * s
def sReadyOff (b : Nat) : Nat := 213280 + 8 * b
def pReadyOff (b : Nat) : Nat := 213296 + 8 * b
def oDoneOff : Nat := 213312
def oFinalOff : Nat := 213328

/-- The location of the shared byte at offset `off` from the base of CTA `cta`'s window. -/
def barLoc (L : Launch) (cta off : Nat) : Loc := ⟨.shared, cta, L.sharedBase + off⟩

/-- The barriers of ring slot `s` (`it % 3` for the K/V tiles) and of S/P buffer `b` (`it % 2`). -/
def kvReady (L : Launch) (cta s : Nat) : Loc := barLoc L cta (kvReadyOff s)
def kvEmpty (L : Launch) (cta s : Nat) : Loc := barLoc L cta (kvEmptyOff s)
def sReady (L : Launch) (cta b : Nat) : Loc := barLoc L cta (sReadyOff b)
def pReady (L : Launch) (cta b : Nat) : Loc := barLoc L cta (pReadyOff b)
def oDone (L : Launch) (cta : Nat) : Loc := barLoc L cta oDoneOff
def oFinal (L : Launch) (cta : Nat) : Loc := barLoc L cta oFinalOff

end PTX.Kernels.InklingRelDecode.Proof.EvW
