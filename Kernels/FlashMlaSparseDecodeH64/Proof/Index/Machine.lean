-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexVal
public import Lemmas.Flow.CodeU
public import Lemmas.Flow.NcLoadU

@[expose] public section

/-! # The index warp as a control machine

Warp 7 of warpgroup 1, all 32 lanes, from its first event (`ixFirst`, `Lib/IndexVal.lean`) to
the `ret`. The sites are `IxSite` (`Lib/IndexSites.lean`). The machine follows every outcome of
the code's control: the length loads continue with the recorded word, every branch is the code's
test on the control words (`IxCtl`), a failed poll stays. Per block of either loop it loads the
next block's index pair (skipped on the loop's last block), waits on the slot's
`valid_coord_free`, shuffles, stores the lane's coordinate pair and (lanes `0 mod 4`) the quad's
validity byte, and arrives on the slot's `valid_coord_ready`. The two loops continue one ring.

**Choice: a control machine, the index values by havoc.** The index words the pair loads return,
the index arrays' addresses and everything computed from them (the coordinates, the validity
bits, the shuffles' words; `ixData`) are not stated: the loads continue on any payload, the
shuffles on any word. No branch, wait, arrival or store ADDRESS reads them, so the shapes of all
events but the loads' addresses are exact. The values matter only to the protocol of the
coordinate ring's contents; the UB-tolerant soundness (`Flow.CodeU`) admits the concrete
continuation's faults on them (a `div.u32` by a zero page size). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- A state: the site, the element of a two-element access, the elements read so far and the
control words. -/
structure D where
  site : IxSite
  el : Nat := 0
  ac : List Value := []
  c : IxCtl := {}

/-- The state at a site's first element. -/
abbrev ofC (p : IxSite × IxCtl) : D := ⟨p.1, 0, [], p.2⟩

/-- The index pairs' loads, the only sites that accumulate elements. -/
def isLd : IxSite → Bool
  | .pre | .pf | .xpre | .xpf => true
  | _ => false

/-- The first word of an index pair's load, as the accumulator keeps it (`0` if it keeps none). -/
def D.w0 (d : D) : BitVec 64 :=
  match d.ac with
  | [.bits _ y] => y
  | _ => 0

/-- The elements of an index pair read so far: the first word, a 32-bit one. -/
def D.acc (d : D) : List Value :=
  match d.el with
  | 0 => []
  | _ + 1 => cond (isLd d.site) [.bits 32 d.w0] []

/-- Every site has an element. -/
theorem IxSite.elems_pos (s : IxSite) : 0 < s.elems := by
  cases s <;> decide

/-! ### The loops -/

/-- The main loop's head (pcs 2426–2428): the counter advances; the next block's pair is loaded
unless this is the last block. -/
@[irreducible] def mainTop (c : IxCtl) : IxSite × IxCtl :=
  let c1 := { c with cnt := addi c.cnt 1 }
  if scmp .ge .s c1.cnt (ixNmin c1.l0 c1.l1) then (.wA, c1) else (.pf, c1)

/-- The main loop's entry (pcs 2414–2425): counters, slot and parity at zero, the next pair is
the current one. -/
@[irreducible] def mainEntry (P : Params) (L : Launch) (g : Nat) (c : IxCtl) : IxSite × IxCtl :=
  mainTop { c with
    neg := neg32 (ixNmin c.l0 c.l1), par := false, cnt := i32 0, slot := 0, wpos := ixPos0 L g,
    aptr := ixAp0 P L g, n0 := c.m0, n1 := c.m1 }

/-- After the first pair (pcs 2404–2409): the main loop, or past it (the code tests again). -/
@[irreducible] def afterPre (P : Params) (L : Launch) (g : Nat) (c : IxCtl) : IxSite × IxCtl :=
  if scmpi .lt .s (ixNmin c.l0 c.l1) 1 then ixNoMain c else mainEntry P L g c

/-- The end of a main block (pcs 2477–2494): parity, slot and counter advance; the next pair
becomes the current one. -/
@[irreducible] def mainEnd (c : IxCtl) : IxSite × IxCtl :=
  let c1 := { c with
    par := ixParNext c.par c.slot, slot := c.slot + 1, neg := addi c.neg 1,
    wpos := addi c.wpos 64, aptr := addi64 c.aptr 256, m0 := c.n0, m1 := c.n1 }
  if scmpi .ne .b c1.neg 0 then mainTop c1 else ixMainDone c1

/-- The extra loop's head (pcs 2512–2514). -/
@[irreducible] def xTop (c : IxCtl) : IxSite × IxCtl :=
  let c1 := { c with xb := addi c.xb 1 }
  if scmp .ge .s c1.xb (ixNblk c1.l0 c1.l1) then (.wB, c1) else (.xpf, c1)

/-- After the extra cache's first pair (pcs 2502–2511): the barrier (the code tests again), or the
extra loop with its negative counter. -/
@[irreducible] def afterXpre (L : Launch) (g : Nat) (c : IxCtl) : IxSite × IxCtl :=
  if scmp .ge .s c.xb (ixNblk c.l0 c.l1) then (.bar, c)
  else xTop { c with
    xn := sub32 c.xb (ixNblk c.l0 c.l1), xa := ixXa0 L g, f0 := c.e0, f1 := c.e1 }

/-- The end of an extra block (pcs 2566–2582). -/
@[irreducible] def xEnd (c : IxCtl) : IxSite × IxCtl :=
  let c1 := { c with
    par := ixParNext c.par c.slot, slot := c.slot + 1, xn := addi c.xn 1, xa := addi c.xa 64,
    e0 := c.f0, e1 := c.f1 }
  if scmpi .ne .b c1.xn 0 then xTop c1 else (.bar, c1)

/-! ### Transitions -/

/-- An element of an index pair (a 32-bit word `y`): the next element, keeping the word;
after the last the state `n` of the pair's two words. -/
def ldNext (d : D) (y : BitVec 64) (n : BitVec 64 → BitVec 64 → D) : D :=
  if d.el + 1 < 2 then { d with el := d.el + 1, ac := [.bits 32 y] } else n d.w0 y

/-- An index pair's element: a 32-bit word continues, another value ends the machine, bytes that
do not rebuild fault. -/
def ncPair (e : Event) (d : D) (n : BitVec 64 → BitVec 64 → D) : Option (Option D) :=
  match e.kind with
  | .nc _ bs =>
    match rebuild 3 bs with
    | .ok (.bits 32 y) => some (some (ldNext d y n))
    | .ok _ => some none
    | .error _ => none
  | _ => none

/-- An element of a coordinate pair's store. -/
def stNext (d n : D) : D := if d.el + 1 < 2 then { d with el := d.el + 1, ac := [] } else n

/-- A poll: on success the site `s`, else the poll again. -/
def poll (e : Event) (d : D) (s : IxSite) : Option (Option D) :=
  match e.kind with
  | .wait _ _ ok _ _ => some (some (if ok then { d with site := s } else d))
  | _ => none

/-- A shuffle: the received word `r` (any value) goes to the successor `f r`. -/
def shflNext (e : Event) (f : Value → D) : Option (Option D) :=
  match e.kind with
  | .shfl _ _ _ _ r _ => some (some (f r))
  | _ => none

/-- A length load: a 32-bit word continues to `f`. -/
def lenNext (e : Event) (f : BitVec 64 → D) : Option (Option D) :=
  match e.kind with
  | .nc _ bs => Code.ncNext f bs
  | _ => none

/-- After a coordinate pair: the validity byte on lanes `0 mod 4`, else the arrival. -/
@[irreducible] def afterSt (L : Launch) (g : Nat) (b a : IxSite) : IxSite :=
  if ixSkipB L g then a else b

/-- **The successor after event `e`.** -/
def succ (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .lenA => lenNext e fun x => ofC (ixAfterA P { d.c with l0 := x })
  | .lenB => lenNext e fun x => ofC (ixLens { d.c with l1 := x })
  | .pre => ncPair e d fun y0 y1 => ofC (afterPre P L g { d.c with m0 := y0, m1 := y1 })
  | .pf => ncPair e d fun y0 y1 => ofC (.wA, { d.c with n0 := y0, n1 := y1 })
  | .wA => poll e d .sA1
  | .sA1 => shflNext e fun r => { d with site := .sA2, c := { d.c with rv1 := r } }
  | .sA2 => shflNext e fun r => { d with site := .stA, c := { d.c with rv2 := r } }
  | .stA => some (some (stNext d (ofC (afterSt L g .bA .arrA, d.c))))
  | .bA => some (some { d with site := .arrA })
  | .arrA => some (some (ofC (mainEnd d.c)))
  | .xpre => ncPair e d fun y0 y1 => ofC (afterXpre L g { d.c with e0 := y0, e1 := y1 })
  | .xpf => ncPair e d fun y0 y1 => ofC (.wB, { d.c with f0 := y0, f1 := y1 })
  | .wB => poll e d .sB1
  | .sB1 => shflNext e fun r => { d with site := .sB2, c := { d.c with rv1 := r } }
  | .sB2 => shflNext e fun r => { d with site := .stB, c := { d.c with rv2 := r } }
  | .stB => some (some (stNext d (ofC (afterSt L g .bB .arrB, d.c))))
  | .bB => some (some { d with site := .arrB })
  | .arrB => some (some (ofC (xEnd d.c)))
  | .bar => some (some { d with site := .exit })
  | .exit => none

/-- **The index warp as a control machine.** -/
@[reducible] def code (P : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := ofC (ixFirst P L g)
  pc := (·.site.pc)
  facts := fun d => ixFacts P L g d.c d.site
  sub := (·.el)
  acc := D.acc
  inv := fun d => d.el < d.site.elems
  next := succ P L g


theorem shflNext_some {e : Event} {f : Value → D} {a : D}
    (h : shflNext e f = some (some a)) : ∃ r, a = f r := by
  unfold shflNext at h
  split at h
  · rename_i r
    exact ⟨_, (Option.some.inj (Option.some.inj h)).symm⟩
  · cases h

/-- A step of an index pair's load: a 32-bit word's `ldNext`. -/
theorem ncPair_some {e : Event} {d d' : D} {n : BitVec 64 → BitVec 64 → D}
    (h : ncPair e d n = some (some d')) : ∃ y, d' = ldNext d y n := by
  unfold ncPair at h
  split at h
  · rename_i a bs hk
    split at h
    · rename_i y hy
      exact ⟨y, (Option.some.inj (Option.some.inj h)).symm⟩
    · cases h
    · cases h
  · cases h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
