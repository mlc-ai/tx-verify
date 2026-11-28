-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Lemmas.Flow.Roles
public import Tactics.KernelRfl

@[expose] public section

/-! # The sites and control registers of the index warp

Warp 7 of warpgroup 1 (all 32 lanes; pcs 2332–2586 and the `ret` at 3611) has 19 event
instructions and the return. Its sites, read from the PTX:

* the two length loads (`lenA`, `lenB`, `ld.global.nc.s32`, each skipped for a null pointer);
* the main cache's blocks: the first block's index pair (`pre`, `ld.global.nc.v2.s32`, before the
  loop), the next block's pair (`pf`, skipped on the last block), the wait on
  `valid_coord_free[slot]` (`wA`), the two butterfly shuffles of the validity bits (`sA1`, `sA2`),
  the coordinate pair's store (`stA`, `st.shared.v2.b32`), the quad's validity byte (`bA`,
  `st.shared.b8`, lanes `0 mod 4`) and the arrival on `valid_coord_ready[slot]` (`arrA`);
* the extra cache's blocks, the same sites (`xpre`, `xpf`, `wB`, `sB1`, `sB2`, `stB`, `bB`,
  `arrB`), continuing the same 4-slot ring;
* named barrier 12 (`bar`) and the return (`exit`).

`sites_pcs`: the sites' pcs are exactly the region's event instructions (by evaluation of the
decoded program). Since this file is below the roles, the warpgroup-1 head (`Wg1/`) can name the
index warp's first event (`Lib/IndexVal.lean`).

**Control registers** (`ixCtl`): the index values the loads return and everything computed from
them (the coordinates, the validity bits and the shuffles' words) are data, havocked by the
control machine: no branch, no event address and no store address reads them (read from the
PTX); so is the lane's mask shift `%r40`. The lengths, the loops' counters, the ring's slot and
parity, the barrier words, the store addresses, the parameters the index warp reads (strides,
pages, the index arrays' bases), the index rows' offsets and the pair loads' addresses and
position words are control registers. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

inductive IxSite where
  | lenA | lenB
  | pre | pf | wA | sA1 | sA2 | stA | bA | arrA
  | xpre | xpf | wB | sB1 | sB2 | stB | bB | arrB
  | bar | exit
  deriving DecidableEq

def IxSite.pc : IxSite → Nat
  | .lenA => 2360 | .lenB => 2365
  | .pre => 2403 | .pf => 2429 | .wA => 2446 | .sA1 => 2464 | .sA2 => 2467 | .stA => 2471
  | .bA => 2474 | .arrA => 2476
  | .xpre => 2501 | .xpf => 2517 | .wB => 2534 | .sB1 => 2553 | .sB2 => 2556 | .stB => 2560
  | .bB => 2563 | .arrB => 2565
  | .bar => 2585 | .exit => 3611

/-- The number of elements of a site's access: the index pairs' loads and the coordinate pairs'
stores have two. -/
def IxSite.elems : IxSite → Nat
  | .pre | .pf | .stA | .xpre | .xpf | .stB => 2
  | _ => 1

/-- Every site, in program order. -/
def IxSite.all : List IxSite :=
  [.lenA, .lenB, .pre, .pf, .wA, .sA1, .sA2, .stA, .bA, .arrA, .xpre, .xpf, .wB, .sB1, .sB2,
    .stB, .bB, .arrB, .bar, .exit]

/-- The index warp's region (the region `Common/Sites.lean` names `index`). -/
def ixRegion : RoleDecl := ⟨[(2332, 2588), (3611, 3612)], [2587, 3611]⟩

/-- **The sites are the region's event instructions**, in program order. -/
theorem IxSite.sites_pcs : IxSite.all.map IxSite.pc = RoleDecl.sites kernel ixRegion := by
  kernel_rfl

/-- The data registers of the index warp (ranges of register ids): the registers that are not
control words, the index pairs' words (`%r2515`-`%r2518`, `%r2523`-`%r2526`) and the values the
code computes from them that live across an event (the quotients and remainders by the page size,
the stored coordinates) being named by the facts (`ixPairs`, `Lib/IndexVal.lean`). -/
def ixData : List (Nat × Nat) :=
  [(21, 28), (36, 43), (562, 562), (580, 580), (582, 584), (590, 590),
   (593, 593), (599, 599), (603, 603), (611, 611), (620, 622), (628, 628), (631, 631),
   (637, 637), (639, 639), (642, 642), (3027, 3032), (3034, 3040), (3042, 3042), (3044, 3044)]

/-- A control register of the index warp: not a data register. -/
def ixCtl (r : Nat) : Bool := !ixData.any fun (a, b) => Nat.ble a r && Nat.ble r b

/-- The control registers live at program counter `pc`. -/
noncomputable def ixLive (pc : Nat) : List Nat := (Flow.live pc).filter ixCtl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
