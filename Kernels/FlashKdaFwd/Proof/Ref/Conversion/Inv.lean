-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Interface

@[expose] public section

/-! # The reference invariant of the Conversion phase (instructions 387 to 621): statement

**How the code is laid out.** A thread converts `pairs g` pairs of elements (43 or 42). The
first loop (instructions 406 to 452) converts one pair a round and runs `head g` rounds (3 or
2: the remainder of the pair count modulo 4, plus 2); the second loop (453 to 618) converts
four pairs a round and runs 10 rounds. Per element there are two sites: the generic load of
the FP32 entry and the store of the bfloat16 slot. So the phase has 23 sites: the proxy fence
(387), ten loads (`load_21` to `load_30`), ten stores (`store_0` to `store_9`) and the two
`bar.sync 0` (620, 621).

**Positions.** A position (`Pos`) is a site of the phase with a ghost index that says where
the loop is: `ld j u` and `st j u` are the load and the store number `j < 10` of the code
(`j < 2`: the two elements of the first loop's pair; `2 ≤ j`: the eight elements of the second
loop's four pairs), in the round whose first pair has the ordinal `u` among the thread's pairs
(`u < head g` in the first loop; `u = head g + 4 m` in round `m < 10` of the second). The
element at such a position is element `elemIx j u` of the thread (`slotOf g (elemIx j u)`).

**The invariant** (`Inv`) of a state before the thread's event `k`, for a thread whose
Conversion phase began at event `k0`: a position; the carried registers (`Keep`) and the
position's registers in closed form (`AtPos`), among them the opaque slots that hold generic
pointers (`sptr g a`: the pointer to address `a` of the block's window); the ledger of the
first `k` events (`led`: the startup's with the `bar.sync 0` of the phase); the number of
events since the entry (`k = k0 + done pos`), so that the position, and with it the element
that an event converts, is a function of the event's index; and at a store the link to the
load before it (`Link`: the stored register holds the narrowed value of what that load
returned).

Abbreviations: `S` is the shared base `P.sharedBase`, `W n` the 64-bit word of `n`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

/-! ### Positions -/

/-- The sites of the Conversion phase, with the ordinal `u` of the first pair of the current
round. -/
inductive Pos where
  | fence
  | ld (j : Fin 10) (u : Nat)
  | st (j : Fin 10) (u : Nat)
  | bar (j : Fin 2)
  deriving DecidableEq

/-- The site of a position. -/
def Pos.site : Pos → Site
  | .fence => .fenceProxy 0
  | .ld j _ => .load ⟨21 + j.val, by omega⟩
  | .st j _ => .store ⟨j.val, by omega⟩
  | .bar j => .bar ⟨3 + j.val, by omega⟩

/-- The pair of a round that load or store `j` of the code works on (0 in the first loop, 0 to
3 in the second). -/
def qOf (j : Nat) : Nat := [0, 0, 0, 0, 1, 1, 2, 2, 3, 3].getD j 0

/-- **The ordinal, among the elements the thread converts, of the element at load or store `j`
in the round whose first pair is `u`.** -/
def elemIx (j u : Nat) : Nat := 2 * (u + qOf j) + j % 2

/-- The opaque slot the loaded FP32 value of load `j` is written to (`%r233`, `%r234`, `%r258`
to `%r265`). -/
def ldReg (j : Nat) : Nat := [539, 540, 564, 565, 566, 567, 568, 569, 570, 571].getD j 0

/-- The opaque slot of the narrowed value that store `j` writes (`%rs7` to `%rs16`). -/
def nrReg (j : Nat) : Nat := [96, 97, 98, 99, 100, 101, 102, 103, 104, 105].getD j 0

/-! ### Facts -/

/-- The three words of the lane that both loops read (`%r10`, `%r11`, `%r12`): `2 l + 1`,
`l / 4` and `2 (l % 4)` for the lane `l`. -/
def LaneW (g : Nat) (d : D) : Prop :=
  d.w 316 = W (2 * lane g + 1) ∧ d.w 317 = W (lane g / 4) ∧ d.w 318 = W (2 * (lane g % 4))

/-- The word `%r13` of the first loop's exit test: the pair count modulo 4. -/
def rem4 (g : Nat) : Nat := if warp g < 4 then 1 else 0

/-- **A round of the first loop** whose pair has the ordinal `u`: the round counter
(`%r1794`), the word of the exit test (`%r13`) and the pair index (`%r1795`). -/
def First (g u : Nat) (d : D) : Prop :=
  u < head g ∧ d.w 2100 = W u ∧ d.w 319 = W (rem4 g) ∧ d.w 2101 = W (pairIx g u)

/-- **A round of the second loop** whose first pair has the ordinal `u`: the pair index of that
pair (`%r1795`). -/
def Second (g u : Nat) (d : D) : Prop :=
  (∃ m, m < 10 ∧ u = head g + 4 * m) ∧ d.w 2101 = W (pairIx g u)

/-- The word `%r242` (and its copies in the second loop) of the pair `r`: the part of the
element index that the second element of the pair is computed from. -/
def hiOf (g r : Nat) : Nat := 1024 * (pairIx g r % 16) + 256 * (lane g % 4)

/-- **The registers at a position.** At a load: the element index, the shared base and the
swizzled address (an opaque slot); at a store: the address of the slot. The base pointer of a
loop (`%rd48`, `%rd62`) and the words the next element is computed from are kept as long as
the code reads them. -/
def AtPos (P : Params) (g : Nat) : Pos → D → Prop
  | .fence, _ => True
  | .ld j u, d =>
    let S := P.sharedBase
    LaneW g d ∧
    match j.val with
    | 0 => First g u d ∧ d.w 548 = W (hiOf g u) ∧ d.w 551 = W (slot0 g u) ∧ d.w 552 = W S ∧
      d.x 2294 = sptr g S ∧ d.x 2299 = sptr g (rdAddr P (slot0 g u))
    | 1 => First g u d ∧ d.w 560 = W (slot0 g u + 1) ∧ d.w 552 = W S ∧
      d.x 2305 = sptr g (rdAddr P (slot0 g u + 1))
    | 2 => Second g u d ∧ d.w 579 = W (hiOf g u) ∧ d.w 582 = W (slot0 g u) ∧ d.w 583 = W S ∧
      d.x 2308 = sptr g S ∧ d.x 2313 = sptr g (rdAddr P (slot0 g u))
    | 3 => Second g u d ∧ d.w 591 = W (slot0 g u + 1) ∧ d.w 583 = W S ∧ d.x 2308 = sptr g S ∧
      d.x 2319 = sptr g (rdAddr P (slot0 g u + 1))
    | 4 => Second g u d ∧ d.w 594 = W (pairIx g (u + 1)) ∧ d.w 602 = W (hiOf g (u + 1)) ∧
      d.w 605 = W (slot0 g (u + 1)) ∧ d.w 583 = W S ∧ d.x 2308 = sptr g S ∧
      d.x 2325 = sptr g (rdAddr P (slot0 g (u + 1)))
    | 5 => Second g u d ∧ d.w 613 = W (slot0 g (u + 1) + 1) ∧ d.w 583 = W S ∧
      d.x 2308 = sptr g S ∧ d.x 2331 = sptr g (rdAddr P (slot0 g (u + 1) + 1))
    | 6 => Second g u d ∧ d.w 616 = W (pairIx g (u + 2)) ∧ d.w 624 = W (hiOf g (u + 2)) ∧
      d.w 627 = W (slot0 g (u + 2)) ∧ d.w 583 = W S ∧ d.x 2308 = sptr g S ∧
      d.x 2337 = sptr g (rdAddr P (slot0 g (u + 2)))
    | 7 => Second g u d ∧ d.w 635 = W (slot0 g (u + 2) + 1) ∧ d.w 583 = W S ∧
      d.x 2308 = sptr g S ∧ d.x 2343 = sptr g (rdAddr P (slot0 g (u + 2) + 1))
    | 8 => Second g u d ∧ d.w 638 = W (pairIx g (u + 3)) ∧ d.w 646 = W (hiOf g (u + 3)) ∧
      d.w 649 = W (slot0 g (u + 3)) ∧ d.w 583 = W S ∧ d.x 2308 = sptr g S ∧
      d.x 2349 = sptr g (rdAddr P (slot0 g (u + 3)))
    | _ => Second g u d ∧ d.w 657 = W (slot0 g (u + 3) + 1) ∧ d.w 583 = W S ∧
      d.x 2355 = sptr g (rdAddr P (slot0 g (u + 3) + 1))
  | .st j u, d =>
    let S := P.sharedBase
    LaneW g d ∧
    match j.val with
    | 0 => First g u d ∧ d.w 548 = W (hiOf g u) ∧ d.w 552 = W S ∧ d.x 2294 = sptr g S ∧
      d.w 554 = W (wrAddr P (slot0 g u))
    | 1 => First g u d ∧ d.w 562 = W (wrAddr P (slot0 g u + 1))
    | 2 => Second g u d ∧ d.w 579 = W (hiOf g u) ∧ d.w 583 = W S ∧ d.x 2308 = sptr g S ∧
      d.w 585 = W (wrAddr P (slot0 g u))
    | 3 => Second g u d ∧ d.w 583 = W S ∧ d.x 2308 = sptr g S ∧
      d.w 593 = W (wrAddr P (slot0 g u + 1))
    | 4 => Second g u d ∧ d.w 594 = W (pairIx g (u + 1)) ∧ d.w 602 = W (hiOf g (u + 1)) ∧
      d.w 583 = W S ∧ d.x 2308 = sptr g S ∧ d.w 607 = W (wrAddr P (slot0 g (u + 1)))
    | 5 => Second g u d ∧ d.w 583 = W S ∧ d.x 2308 = sptr g S ∧
      d.w 615 = W (wrAddr P (slot0 g (u + 1) + 1))
    | 6 => Second g u d ∧ d.w 616 = W (pairIx g (u + 2)) ∧ d.w 624 = W (hiOf g (u + 2)) ∧
      d.w 583 = W S ∧ d.x 2308 = sptr g S ∧ d.w 629 = W (wrAddr P (slot0 g (u + 2)))
    | 7 => Second g u d ∧ d.w 583 = W S ∧ d.x 2308 = sptr g S ∧
      d.w 637 = W (wrAddr P (slot0 g (u + 2) + 1))
    | 8 => Second g u d ∧ d.w 638 = W (pairIx g (u + 3)) ∧ d.w 646 = W (hiOf g (u + 3)) ∧
      d.w 583 = W S ∧ d.x 2308 = sptr g S ∧ d.w 651 = W (wrAddr P (slot0 g (u + 3)))
    | _ => Second g u d ∧ d.w 659 = W (wrAddr P (slot0 g (u + 3) + 1))
  | .bar _, d => d.w 317 = W (lane g / 4) ∧ d.p 30 = decide (127 < tid g)

/-- **The reference invariant of a state at a position.** -/
structure RefAt (P : Params) (g : Nat) (pos : Pos) (d : D) : Prop where
  site : d.site = pos.site
  keep : Keep P g d
  pos : AtPos P g pos d

/-! ### The ledger and the number of events -/

/-- **The ledger before a position**: the startup's exit ledger; the second `bar.sync 0` of
the phase has one more `bar.sync 0` before it. -/
def led (g : Nat) : Pos → Startup.Led
  | .bar j => ⟨3 + j.val, (Startup.ledExit g).inits, (Startup.ledExit g).arrs,
      (Startup.ledExit g).issues, 1, 3⟩
  | _ => Startup.ledExit g

/-- **The number of events of the phase before a position**: the proxy fence, then a load and
a store per element, in the order of the elements. -/
def done (g : Nat) : Pos → Nat
  | .fence => 0
  | .ld j u => 1 + 2 * elemIx j.val u
  | .st j u => 2 + 2 * elemIx j.val u
  | .bar j => 1 + 4 * pairs g + j.val

/-- **The link of a store to the load before it**: the event before a store position is the
load of the same element, of the four bytes at the element's swizzled address, and the
register that the store writes holds the narrowed value of what the load returned (`ldVal`:
the value of the four bytes; `Rules.narrowE`: the outcome of `cvt.rn.bf16.f32`). -/
def Link (P : Params) (X : Execution) (g k : Nat) : Pos → D → Prop
  | .st j u, d => ∃ bs v y, 0 < k ∧
      X.get (g, k - 1) = some ⟨(Pos.ld j u).site.pc,
        .rd { loc := ⟨.shared, cta g, rdAddr P (slotOf g (elemIx j.val u))⟩, size := 4 } bs⟩ ∧
      ldVal .same 32 bs = .ok v ∧ Rules.narrowE [v] = .ok y ∧ d.x (nrReg j.val) = y
  | _, _ => True

variable (P : Params) (X : Execution) (g : Nat)

/-- **The invariant of the Conversion phase** before the thread's event `k`, for a thread that
entered the phase at its event `k0`. -/
def Inv (k0 k : Nat) (d : D) : Prop :=
  ∃ pos, RefAt P g pos d ∧ Startup.ledOf ((X.tr g).take k) = led g pos ∧
    k = k0 + done g pos ∧ Link P X g k pos d

/-- The thread left the Conversion phase, which it entered at event `k0`, at or before its
event `k`: the exit condition held at event `k0 + len g`. -/
def Left (L : Launch) (k0 k : Nat) : Prop :=
  k0 + len g ≤ k ∧ ∃ s1, Frame.stateAt (code L) X g (k0 + len g) = some (some s1) ∧
    Out P X g (k0 + len g) s1

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
