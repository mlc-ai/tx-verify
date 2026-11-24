-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Places
public import Kernels.TmlFa4Fwd.Proof.Mma.Cnt
public import Kernels.TmlFa4Fwd.Proof.Mma.Ledger
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Lemmas.Flow.Counter32
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's reference invariant for its barrier counts and loop registers

The ledger's counts at every state of the MMA warp's counted machine are closed forms in the
state's place in the pipeline and the number `r` of loop rounds done (`RefCounts`), and every
step keeps them (`ref_step`).

* **Place.** `Site.ord` numbers the pipeline's sites in program order: `0` before the pipeline
  (the scheduler's first pass, the request's reads, and the end without a tile), `1`–`16` the
  first K/V block, `20`–`49` one loop round, `60`–`85` the tail, `100` the second pass and the end
  after it. A site at place `x` has been passed `pq x q r` times at place `q`: once if it lies
  before `q`, and for a loop site once per round done plus once if `q` lies after it in the
  current round.
* **Loop registers** (`LoopRegs`): in the loop and the tail, the K/V slot is `(2r + 1) mod 3`,
  its parity `((2r + 1) / 3) mod 2`, the P parity `r mod 2` and the accumulate flag `r ≠ 0`.
  In the loop `r + 1 < B` for the tile's `B` K/V blocks (as a signed word, `Bs`) and `%r6144`
  is `r - B`; in the tail `r + 1 = B`, or `r = 0` when the tile has fewer than two blocks.
* **Ready counts** (`acqAt`): the successful polls of each barrier. The K/V ring's slot `k`
  is acquired once for each ring index `j < ringAcq` with `j mod 3 = k` (`ringCount`), the ring
  indices being K₀, then `V_i, K_{i+1}` per round, then the last `V`.
* **Empty counts** (`commitAt`): the commits to each barrier, on the lane that wins the
  elections (`w`), zero on the others; a ring release `j` releases slot `j mod 3`.
* **Elections** (`electAll`): the lane wins all of them or none. That is what `Expect` asks of an
  election: no win after a loss and no loss after a win, which the execution's election rule
  gives (every election of a warp with one mask returns one leader).

That exactly one lane of the warp wins, so that the warp's commits to a barrier are the winning
lane's, is the same rule applied across the warp's lanes, above the machine. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- The count conjuncts at place `q` with `r` rounds done, on a lane that wins every election
(`w`) or none. -/
structure RefQ (p : Params) (L : Launch) (g : Nat) (q : Nat) (v : V) (n : Cnt → Nat) (r : Nat)
    (w : Bool) : Prop where
  pre : q < 20 → r = 0
  regs : 20 ≤ q ∧ q < 100 → LoopRegs v r
  loop : 20 ≤ q ∧ q < 60 → (r : Int) + 1 < Bs p L g v ∧ v.trip = i32 (r - Bs p L g v)
  tail : 60 ≤ q ∧ q < 100 → (r : Int) + 1 = Bs p L g v ∨ (r = 0 ∧ Bs p L g v < 2)
  acq : ∀ o, n (.acquire (bl L g o)) = acqAt q r o
  com : ∀ o, n (.commit (bl L g o)) = if w then commitAt q r o else 0
  won : n .won = if w then electAll q r else 0
  lost : n .lost = if w then 0 else electAll q r
  ps : v.ps = shAt q r

/-- **The count conjuncts of the MMA warp's reference invariant** at a counted state. -/
def RefCounts (p : Params) (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  ∃ r w, RefQ p L g dn.1.site.ord dn.1.v dn.2 r w ∧ (dn.1.site.ord ∈ cmQ → w = true)

/-- What an election must return for the counts to continue: the lane wins it if it won one
before, and loses it if it lost one before. -/
def ExpectElect (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) (e : Event) : Prop :=
  ∀ m inst ld, e.kind = .elect m inst ld →
    (0 < dn.2 .won → ld = laneOf L g) ∧ (0 < dn.2 .lost → ld ≠ laneOf L g)

/-! ### Barrier addresses -/

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

theorem sb_lt (hp : Pre p L m) : L.sharedBase < 2 ^ 18 := by
  have := hp.shared.2.1; omega

theorem smLoc_add (hp : Pre p L m) {x : BitVec 64} {o : Nat} (hx : x.toNat = L.sharedBase + o)
    (ho : o < 2 ^ 20) : smLoc L g x 0 = bl L g o := by
  have := sb_lt hp
  simp only [smLoc, bl, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
    hx, Loc.mk.injEq, true_and]
  omega

theorem smLoc_off (hp : Pre p L m) {o : Nat} (ho : o < 2 ^ 20) :
    smLoc L g (sbW L) (o : Int) = bl L g o := by
  have := sb_lt hp
  simp only [smLoc, bl, sbW, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
    Loc.mk.injEq, true_and]
  omega

theorem addi_sb (hp : Pre p L m) {o : Nat} (ho : o < 2 ^ 20) :
    (addi (sbW L) o).toNat = L.sharedBase + o := by
  have := sb_lt hp
  simp only [addi, r32, i32, sbW, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  omega

theorem slotAddr_toNat (hp : Pre p L m) {k : Nat} (hk : k < 3) :
    (slotAddr L (iw k)).toNat = L.sharedBase + 8 * k := by
  have := sb_lt hp
  interval_cases k <;>
    simp [slotAddr, Epilogue.add32, Epilogue.shl, r32, i32, sbW, truncBits] <;> omega

theorem bl_inj {o o' : Nat} : bl L g o = bl L g o' ↔ o = o' := by
  simp [bl]

/-- The next slot of the ring after slot `(2r + 1) mod 3`, and its parity. -/
theorem slot1_eq {v : V} {r : Nat} (h : LoopRegs v r) :
    slot1 v = iw ((2 * r + 2) % 3) ∧ kvp1 v = iw ((2 * r + 2) / 3 % 2) := by
  obtain ⟨hs, hk, -, -⟩ := h
  simp only [slot1, kvp1, hs, hk]
  have h6 : r % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases hr : r % 6
  · rw [show (2 * r + 1) % 3 = 1 by omega, show (2 * r + 1) / 3 % 2 = 0 by omega,
      show (2 * r + 2) % 3 = 2 by omega, show (2 * r + 2) / 3 % 2 = 0 by omega]; decide
  · rw [show (2 * r + 1) % 3 = 0 by omega, show (2 * r + 1) / 3 % 2 = 1 by omega,
      show (2 * r + 2) % 3 = 1 by omega, show (2 * r + 2) / 3 % 2 = 1 by omega]; decide
  · rw [show (2 * r + 1) % 3 = 2 by omega, show (2 * r + 1) / 3 % 2 = 1 by omega,
      show (2 * r + 2) % 3 = 0 by omega, show (2 * r + 2) / 3 % 2 = 0 by omega]; decide
  · rw [show (2 * r + 1) % 3 = 1 by omega, show (2 * r + 1) / 3 % 2 = 0 by omega,
      show (2 * r + 2) % 3 = 2 by omega, show (2 * r + 2) / 3 % 2 = 0 by omega]; decide
  · rw [show (2 * r + 1) % 3 = 0 by omega, show (2 * r + 1) / 3 % 2 = 1 by omega,
      show (2 * r + 2) % 3 = 1 by omega, show (2 * r + 2) / 3 % 2 = 1 by omega]; decide
  · rw [show (2 * r + 1) % 3 = 2 by omega, show (2 * r + 1) / 3 % 2 = 1 by omega,
      show (2 * r + 2) % 3 = 0 by omega, show (2 * r + 2) / 3 % 2 = 0 by omega]; decide

/-! ### Barrier locations of the warp's events -/

theorem smLoc_addi (hp : Pre p L m) (n : Int) (h0 : 0 ≤ n) (h1 : n < 2 ^ 20) :
    smLoc L g (addi (sbW L) n) 0 = bl L g n.toNat := by
  have := sb_lt hp
  simp only [smLoc, bl, addi, r32, i32, sbW, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt, Loc.mk.injEq, true_and]
  omega

theorem smLoc_sbW (hp : Pre p L m) (n : Int) (h0 : 0 ≤ n) (h1 : n < 2 ^ 20) :
    smLoc L g (sbW L) n = bl L g n.toNat := by
  have := sb_lt hp
  simp only [smLoc, bl, sbW, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
    Loc.mk.injEq, true_and]
  omega

theorem smLoc_sb144 (hp : Pre p L m) :
    smLoc L g (BitVec.ofNat 64 (L.sharedBase + 144)) 0 = bl L g 144 := by
  have := sb_lt hp
  simp only [smLoc, bl, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
    Loc.mk.injEq, true_and]
  omega

theorem smLoc_slot (hp : Pre p L m) {k : Nat} (hk : k < 3) :
    smLoc L g (addi (slotAddr L (iw k)) 32) 0 = bl L g (32 + 8 * k) := by
  have := sb_lt hp
  have h := slotAddr_toNat hp hk
  refine smLoc_add hp ?_ (by omega)
  generalize slotAddr L (iw k) = x at h ⊢
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt, h]
  omega

theorem smLoc_slot56 (hp : Pre p L m) {k : Nat} (hk : k < 3) :
    smLoc L g (slotAddr L (iw k)) 56 = bl L g (56 + 8 * k) := by
  have := sb_lt hp
  have h := slotAddr_toNat hp hk
  generalize slotAddr L (iw k) = x at h ⊢
  simp only [smLoc, bl, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
    Loc.mk.injEq, true_and, h]
  omega

/-- The barrier of the poll inside PV block `b`. -/
theorem mw_loc (hp : Pre p L m) (b : Fin 4) :
    smLoc L g (mwOp L b) 0 = bl L g (if b.val % 2 = 0 then 112 else 120) := by
  unfold mwOp
  split
  · exact smLoc_addi hp 112 (by decide) (by decide)
  · exact smLoc_addi hp 120 (by decide) (by decide)

/-- The barrier of commit `c`; the ring releases read the loop registers. -/
theorem cm_loc (hp : Pre p L m) {v : V} {r : Nat} (c : Fin 12)
    (hR : c.val = 4 ∨ c.val = 6 ∨ c.val = 9 → LoopRegs v r) :
    smLoc L g (cmOp L v c).1 (cmOp L v c).2 = bl L g (cmO r c) := by
  fin_cases c
  all_goals simp only [cmOp, cmO, Fin.isValue, Fin.reduceFinMk, Fin.val_mk, List.getD_cons_succ,
    List.getD_cons_zero]
  · exact smLoc_addi hp 80 (by decide) (by decide)
  · exact smLoc_sbW hp 88 (by decide) (by decide)
  · exact smLoc_sbW hp 56 (by decide) (by decide)
  · exact smLoc_addi hp 80 (by decide) (by decide)
  · rw [(hR (by decide)).1]; exact smLoc_slot56 hp (by omega)
  · exact smLoc_addi hp 88 (by decide) (by decide)
  · rw [(slot1_eq (hR (by decide))).1]; exact smLoc_slot56 hp (by omega)
  · exact smLoc_sbW hp 16 (by decide) (by decide)
  · exact smLoc_sbW hp 24 (by decide) (by decide)
  · rw [(hR (by decide)).1]; exact smLoc_slot56 hp (by omega)
  · exact smLoc_sb144 hp
  · exact smLoc_sbW hp 152 (by decide) (by decide)

/-! ### Moving between places -/

/-- The places of the sites the counts read. -/
def cnt : List Nat := [1, 2, 9, 20, 21, 27, 29, 35, 40, 64, 65, 71, 73, 78, 8, 14, 16, 34, 43, 47,
  49, 61, 63, 81, 83, 85, 5, 11, 31, 44, 7, 13, 15, 33, 42, 46, 48, 60, 62, 80, 82, 84, 25, 38,
  69, 76, 3, 4, 10, 22, 23, 24, 30, 36, 37, 66, 67, 68, 74, 75]

/-- A move from place `q` to place `q'` in one region that passes no counted site except `x0`
(`x0 = 1000` for none). -/
def qmove (x0 q q' : Nat) : Bool :=
  (decide (q < 20) == decide (q' < 20)) &&
    (decide (20 ≤ q ∧ q < 60) == decide (20 ≤ q' ∧ q' < 60)) &&
    (decide (60 ≤ q ∧ q < 100) == decide (60 ≤ q' ∧ q' < 100)) && decide (q ≤ x0) &&
    cnt.all (fun x => decide (x < q') == (decide (x < q) || decide (x = x0)))

theorem pq_move {x0 q q' x : Nat} (r : Nat) (h : qmove x0 q q' = true) (hx : x ∈ cnt) :
    pq x q' r = pq x q r + if x = x0 then 1 else 0 := by
  simp only [qmove, Bool.and_eq_true, beq_iff_eq, decide_eq_decide, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have h6 : x < q' ↔ (x < q ∨ x = x0) := by
    rw [← decide_eq_decide, Bool.decide_or]; exact h5 x hx
  unfold pq
  split_ifs <;> omega

/-- The ring indices below `n + 1` with residue `k` are those below `n` and `n` itself if it has
residue `k`. -/
theorem ringCount_succ {n k : Nat} (hk : k < 3) :
    ringCount (n + 1) k = ringCount n k + if n % 3 = k then 1 else 0 := by
  unfold ringCount
  split_ifs <;> omega

theorem qmove_regions {x0 q q' : Nat} (hm : qmove x0 q q' = true) :
    (q < 20 ↔ q' < 20) ∧ (20 ≤ q ∧ q < 60 ↔ 20 ≤ q' ∧ q' < 60) ∧
      (60 ≤ q ∧ q < 100 ↔ 60 ≤ q' ∧ q' < 100) := by
  simp only [qmove, Bool.and_eq_true, beq_iff_eq, decide_eq_decide] at hm
  exact ⟨hm.1.1.1.1, hm.1.1.1.2, hm.1.1.2⟩

theorem ite_add0 {c : Prop} [Decidable c] (a b : Nat) :
    (if c then a + b else 0) = (if c then a else 0) + (if c then b else 0) := by
  split <;> simp

theorem ringCount_add_ite {n k : Nat} {c : Prop} [Decidable c] (hk : k < 3) :
    ringCount (n + if c then 1 else 0) k = ringCount n k + if c ∧ n % 3 = k then 1 else 0 := by
  split <;> simp_all [ringCount_succ hk]

/-- The ring sites among the counted places. -/
def ringA (x0 : Nat) : Bool := x0 == 2 || x0 == 20 || x0 == 29 || x0 == 64
def ringR (x0 : Nat) : Bool := x0 == 16 || x0 == 43 || x0 == 49 || x0 == 81

/-- What a move passing `x0` adds to the counts of the barrier at offset `o`. -/
def acqD (x0 q r o : Nat) : Nat :=
  (if o = 0 then (if x0 = 1 then 1 else 0) else 0) +
    (if o = 8 then (if x0 = 9 then 1 else 0) else 0) +
    (if o = 96 then (if x0 = 21 then 1 else 0) + (if x0 = 65 then 1 else 0) else 0) +
    (if o = 104 then (if x0 = 35 then 1 else 0) + (if x0 = 73 then 1 else 0) else 0) +
    (if o = 112 then (if x0 = 27 then 1 else 0) + (if x0 = 71 then 1 else 0) else 0) +
    (if o = 120 then (if x0 = 40 then 1 else 0) + (if x0 = 78 then 1 else 0) else 0) +
    (if 32 ≤ o ∧ o < 56 ∧ o % 8 = 0 then
      (if ringA x0 = true ∧ ringAcq q r % 3 = (o - 32) / 8 then 1 else 0) else 0)

def comD (x0 q r o : Nat) : Nat :=
  (if o = 80 then (if x0 = 8 then 1 else 0) + (if x0 = 34 then 1 else 0) else 0) +
    (if o = 88 then (if x0 = 14 then 1 else 0) + (if x0 = 47 then 1 else 0) else 0) +
    (if o = 16 then (if x0 = 61 then 1 else 0) else 0) +
    (if o = 24 then (if x0 = 63 then 1 else 0) else 0) +
    (if o = 144 then (if x0 = 83 then 1 else 0) else 0) +
    (if o = 152 then (if x0 = 85 then 1 else 0) else 0) +
    (if 56 ≤ o ∧ o < 80 ∧ o % 8 = 0 then
      (if ringR x0 = true ∧ ringRel q r % 3 = (o - 56) / 8 then 1 else 0) else 0)

/-- What a move passing `x0` adds to the pipeline's broadcasts. -/
def shD (x0 : Nat) : Nat :=
  (if x0 = 3 then 1 else 0) + (if x0 = 4 then 1 else 0) + (if x0 = 10 then 1 else 0) +
    (if x0 = 22 then 1 else 0) + (if x0 = 23 then 1 else 0) + (if x0 = 24 then 1 else 0) +
    (if x0 = 30 then 1 else 0) + (if x0 = 36 then 1 else 0) + (if x0 = 37 then 1 else 0) +
    (if x0 = 66 then 1 else 0) + (if x0 = 67 then 1 else 0) + (if x0 = 68 then 1 else 0) +
    (if x0 = 74 then 1 else 0) + (if x0 = 75 then 1 else 0)

def elD (x0 : Nat) : Nat :=
  (if x0 = 5 then 1 else 0) +
    (if x0 = 11 then 1 else 0) +
    (if x0 = 31 then 1 else 0) +
    (if x0 = 44 then 1 else 0) +
    (if x0 = 7 then 1 else 0) +
    (if x0 = 13 then 1 else 0) +
    (if x0 = 15 then 1 else 0) +
    (if x0 = 33 then 1 else 0) +
    (if x0 = 42 then 1 else 0) +
    (if x0 = 46 then 1 else 0) +
    (if x0 = 48 then 1 else 0) +
    (if x0 = 60 then 1 else 0) +
    (if x0 = 62 then 1 else 0) +
    (if x0 = 80 then 1 else 0) +
    (if x0 = 82 then 1 else 0) +
    (if x0 = 84 then 1 else 0) +
    (if x0 = 25 then 1 else 0) +
    (if x0 = 38 then 1 else 0) +
    (if x0 = 69 then 1 else 0) +
    (if x0 = 76 then 1 else 0)

theorem pq_move' {x0 q q' : Nat} (r : Nat) (h : qmove x0 q q' = true) (x : Nat) (hx : x ∈ cnt) :
    pq x q' r = pq x q r + if x0 = x then 1 else 0 := by
  rw [pq_move r h hx]; simp only [eq_comm]

theorem ringAcq_move {x0 q q' : Nat} (r : Nat) (h : qmove x0 q q' = true) :
    ringAcq q' r = ringAcq q r + if ringA x0 = true then 1 else 0 := by
  simp only [ringAcq, pq_move' r h _ (by decide : 2 ∈ cnt), pq_move' r h _ (by decide : 20 ∈ cnt),
    pq_move' r h _ (by decide : 29 ∈ cnt), pq_move' r h _ (by decide : 64 ∈ cnt), ringA,
    Bool.or_eq_true, beq_iff_eq]
  split_ifs <;> omega

theorem ringRel_move {x0 q q' : Nat} (r : Nat) (h : qmove x0 q q' = true) :
    ringRel q' r = ringRel q r + if ringR x0 = true then 1 else 0 := by
  simp only [ringRel, pq_move' r h _ (by decide : 16 ∈ cnt), pq_move' r h _ (by decide : 43 ∈ cnt),
    pq_move' r h _ (by decide : 49 ∈ cnt), pq_move' r h _ (by decide : 81 ∈ cnt), ringR,
    Bool.or_eq_true, beq_iff_eq]
  split_ifs <;> omega

theorem acqAt_move {x0 q q' : Nat} (r o : Nat) (h : qmove x0 q q' = true) :
    acqAt q' r o = acqAt q r o + acqD x0 q r o := by
  have hk : (o - 32) / 8 < 3 ∨ ¬ (32 ≤ o ∧ o < 56 ∧ o % 8 = 0) := by omega
  simp only [acqAt, acqD, ringAcq_move r h]
  simp (disch := decide) only [pq_move' r h]
  by_cases hr : 32 ≤ o ∧ o < 56 ∧ o % 8 = 0
  · simp only [hr, and_self, ↓reduceIte, ringCount_add_ite (by omega : (o - 32) / 8 < 3), ite_add0]
    omega
  · simp only [hr, ↓reduceIte, ite_add0]
    omega

theorem commitAt_move {x0 q q' : Nat} (r o : Nat) (h : qmove x0 q q' = true) :
    commitAt q' r o = commitAt q r o + comD x0 q r o := by
  simp only [commitAt, comD, ringRel_move r h]
  simp (disch := decide) only [pq_move' r h]
  by_cases hr : 56 ≤ o ∧ o < 80 ∧ o % 8 = 0
  · simp only [hr, and_self, ↓reduceIte, ringCount_add_ite (by omega : (o - 56) / 8 < 3), ite_add0]
    omega
  · simp only [hr, ↓reduceIte, ite_add0]
    omega

theorem electAll_move {x0 q q' : Nat} (r : Nat) (h : qmove x0 q q' = true) :
    electAll q' r = electAll q r + elD x0 := by
  simp only [electAll, elD]
  simp (disch := decide) only [pq_move' r h]
  omega

theorem shAt_move {x0 q q' : Nat} (r : Nat) (h : qmove x0 q q' = true) :
    shAt q' r = shAt q r + shD x0 := by
  simp only [shAt, shD]
  simp (disch := decide) only [pq_move' r h]
  omega

/-- **A move from place `q` to `q'` passing `x0`**: the counts grow by what `x0` adds. -/
theorem refQ_move {x0 q q' : Nat} {v v' : V} {n n' : Cnt → Nat} {r : Nat} {w : Bool}
    (hQ : RefQ p L g q v n r w) (hm : qmove x0 q q' = true)
    (ha : ∀ o, n' (.acquire (bl L g o)) = n (.acquire (bl L g o)) + acqD x0 q r o)
    (hc : ∀ o, n' (.commit (bl L g o)) = n (.commit (bl L g o)) + if w then comD x0 q r o else 0)
    (hw : n' .won = n .won + if w then elD x0 else 0)
    (hl : n' .lost = n .lost + if w then 0 else elD x0)
    (hv : 20 ≤ q ∧ q < 100 → v'.slot = v.slot ∧ v'.kvp = v.kvp ∧ v'.pp = v.pp ∧
      v'.accum = v.accum ∧ v'.trip = v.trip ∧ blocks p L g v' = blocks p L g v)
    (hps : v'.ps = v.ps + shD x0) :
    RefQ p L g q' v' n' r w := by
  obtain ⟨g1, g2, g3⟩ := qmove_regions hm
  have hq100 : 20 ≤ q' ∧ q' < 100 → 20 ≤ q ∧ q < 100 := fun h => by
    by_cases h' : q' < 60
    · have := g2.mpr ⟨h.1, h'⟩; omega
    · have := g3.mpr ⟨by omega, h.2⟩; omega
  refine ⟨fun h => hQ.pre (g1.mpr h), fun h => ?_, fun h => ?_, fun h => ?_, fun o => ?_,
    fun o => ?_, ?_, ?_, by rw [hps, hQ.ps, shAt_move r hm]⟩
  · obtain ⟨h1, h2, h3, h4, -, -⟩ := hv (hq100 h)
    obtain ⟨e1, e2, e3, e4⟩ := hQ.regs (hq100 h)
    exact ⟨h1.trans e1, h2.trans e2, h3.trans e3, h4.trans e4⟩
  · obtain ⟨-, -, -, -, h5, h6⟩ := hv (hq100 ⟨h.1, by omega⟩)
    have hB : Bs p L g v' = Bs p L g v := by simp only [Bs, h6]
    rw [hB, h5]
    exact hQ.loop (g2.mpr h)
  · obtain ⟨-, -, -, -, -, h6⟩ := hv (hq100 ⟨by omega, h.2⟩)
    have hB : Bs p L g v' = Bs p L g v := by simp only [Bs, h6]
    rw [hB]
    exact hQ.tail (g3.mpr h)
  · rw [ha, hQ.acq, acqAt_move r o hm]
  · rw [hc, hQ.com, commitAt_move r o hm]; cases w <;> simp
  · rw [hw, hQ.won, electAll_move r hm]; cases w <;> simp
  · rw [hl, hQ.lost, electAll_move r hm]; cases w <;> simp


/-! ### Quiet events -/

/-- An event the counts do not see: no successful poll, commit or election. -/
def quietK : Kind → Bool
  | .wait _ _ true _ _ | .tc (.commit _) | .elect .. => false
  | _ => true

theorem bump_quiet {n : Cnt → Nat} {e : Event} (hk : quietK e.kind = true) :
    (∀ l, Code.bump (cls L g) n e (.acquire l) = n (.acquire l)) ∧
      (∀ l, Code.bump (cls L g) n e (.commit l) = n (.commit l)) ∧
      Code.bump (cls L g) n e .won = n .won ∧ Code.bump (cls L g) n e .lost = n .lost := by
  obtain ⟨pc, k⟩ := e
  refine ⟨fun l => ?_, fun l => ?_, ?_, ?_⟩ <;>
    cases k with
    | tc tk => cases tk <;> simp_all [Code.bump, cls, quietK]
    | wait m par ok a sc => cases ok <;> simp_all [Code.bump, cls, quietK]
    | _ => simp_all [Code.bump, cls, quietK]

theorem qmove_refl {q : Nat} (hq : q ≤ 1000) : qmove 1000 q q = true := by
  simp only [qmove, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, beq_iff_eq]
  refine ⟨hq, fun x hx => ?_⟩
  have : x ≠ 1000 := by rintro rfl; exact absurd hx (by decide)
  simp [this]

theorem acqD_none (q r o : Nat) : acqD 1000 q r o = 0 := by simp [acqD, ringA]
theorem comD_none (q r o : Nat) : comD 1000 q r o = 0 := by simp [comD, ringR]

/-- A quiet step to a place that passes no counted site keeps the counts. -/
theorem refc_quiet {s s' : Site} {v v' : V} {n : Cnt → Nat} {e : Event} {r : Nat} {w : Bool}
    (hQ : RefQ p L g s.ord v n r w ∧ (s.ord ∈ cmQ → w = true)) (hk : quietK e.kind = true)
    (hm : qmove 1000 s.ord s'.ord = true) (hcm : s'.ord ∈ cmQ → s.ord ∈ cmQ)
    (hv : 20 ≤ s.ord ∧ s.ord < 100 → v'.slot = v.slot ∧ v'.kvp = v.kvp ∧ v'.pp = v.pp ∧
      v'.accum = v.accum ∧ v'.trip = v.trip ∧ blocks p L g v' = blocks p L g v)
    (hps : v'.ps = v.ps) :
    RefCounts p L g (⟨s', v'⟩, Code.bump (cls L g) n e) := by
  have hb := bump_quiet (L := L) (g := g) (n := n) hk
  refine ⟨r, w, refQ_move hQ.1 hm (fun o => ?_) (fun o => ?_) ?_ ?_ hv (by simp [hps, shD]),
    fun h => hQ.2 (hcm h)⟩
  · dsimp only; rw [hb.1, acqD_none]; rfl
  · dsimp only; rw [hb.2.1, comD_none]; simp
  · dsimp only; rw [hb.2.2.1]; simp [elD]
  · dsimp only; rw [hb.2.2.2]; simp [elD]

theorem ord_le (s : Site) : s.ord ≤ 1000 := by
  cases s with
  | wt k => fin_cases k <;> decide
  | sh k => fin_cases k <;> decide
  | eq b => fin_cases b <;> decide
  | ep b => fin_cases b <;> decide
  | qk b j => fin_cases b <;> simp [Site.ord]
  | pv b j => fin_cases b <;> fin_cases j <;> decide
  | mw b l => fin_cases b <;> simp [Site.ord]
  | ce c => fin_cases c <;> decide
  | cm c => fin_cases c <;> decide
  | word k => cases k <;> decide
  | down k => cases k <;> decide
  | up k j => cases k <;> simp [Site.ord, Epilogue.Scan.late]
  | total k => cases k <;> decide
  | vote l => cases l <;> decide
  | pre l => cases l <;> decide
  | tiles l => cases l <;> decide
  | relinq l => cases l <;> decide
  | bar2 l => cases l <;> decide
  | dealloc l => cases l <;> decide
  | exit l => cases l <;> decide
  | _ => decide

theorem setS_same (v : V) (x : BitVec 64) (k : Fin 14) :
    (setS v x k).slot = v.slot ∧ (setS v x k).kvp = v.kvp ∧ (setS v x k).pp = v.pp ∧
      (setS v x k).accum = v.accum ∧ (setS v x k).trip = v.trip ∧
      blocks p L g (setS v x k) = blocks p L g v := by
  fin_cases k <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A broadcast of the pipeline: the next site, with the broadcast's word recorded. -/
theorem refc_sh (k : Fin 14) {v : V} {x : BitVec 64} {n : Cnt → Nat} {e : Event} {r : Nat}
    {w : Bool} (hQ : RefQ p L g (Site.sh k).ord v n r w ∧ ((Site.sh k).ord ∈ cmQ → w = true))
    (hk : quietK e.kind = true) :
    RefCounts p L g (⟨shNext k, { setS v x k with ps := v.ps + 1 }⟩, Code.bump (cls L g) n e) := by
  have hb := bump_quiet (L := L) (g := g) (n := n) hk
  refine ⟨r, w, refQ_move (x0 := (Site.sh k).ord) hQ.1 ?_ (fun o => ?_) (fun o => ?_) ?_ ?_
    (fun _ => setS_same (p := p) (L := L) (g := g) v x k) ?_, fun h => ?_⟩
  · show qmove _ _ (shNext k).ord = true; fin_cases k <;> decide
  · dsimp only; rw [hb.1]; fin_cases k <;> simp [acqD, ringA, Site.ord]
  · dsimp only; rw [hb.2.1]; fin_cases k <;> simp [comD, ringR, Site.ord]
  · dsimp only; rw [hb.2.2.1]; fin_cases k <;> simp [elD, Site.ord]
  · dsimp only; rw [hb.2.2.2]; fin_cases k <;> simp [elD, Site.ord]
  · show v.ps + 1 = v.ps + _; fin_cases k <;> simp [shD, Site.ord]
  · fin_cases k <;> simp [Site.ord, shNext, cmQ] at h

/-- A successful poll of the barrier at offset `o0`. -/
theorem refc_poll {s s' : Site} {v : V} {n : Cnt → Nat} {r : Nat} {w : Bool} {o0 pc par : Nat}
    {sc : MbarScope} (hQ : RefQ p L g s.ord v n r w ∧ (s.ord ∈ cmQ → w = true))
    (hm : qmove s.ord s.ord s'.ord = true) (hcm : s'.ord ∈ cmQ → s.ord ∈ cmQ)
    (hD : ∀ o, acqD s.ord s.ord r o = if o = o0 then 1 else 0)
    (hC : ∀ o, comD s.ord s.ord r o = 0) (hE : elD s.ord = 0)
    (hS : shD s.ord = 0 := by decide) :
    RefCounts p L g (⟨s', v⟩, Code.bump (cls L g) n ⟨pc, .wait (bl L g o0) par true true sc⟩) := by
  refine ⟨r, w, refQ_move hQ.1 hm (fun o => ?_) (fun o => ?_) ?_ ?_
    (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by simp [hS]), fun h => hQ.2 (hcm h)⟩
  · rw [hD]
    by_cases ho : o = o0
    · subst ho; simp [Code.bump, cls]
    · have : ¬ bl L g o0 = bl L g o := fun h => ho (bl_inj.mp h).symm
      simp [Code.bump, cls, ho, this]
  · rw [hC]; simp [Code.bump, cls]
  · rw [hE]; simp [Code.bump, cls]
  · rw [hE]; simp [Code.bump, cls]

/-- A commit to the barrier at offset `o0`, on the lane that wins the elections. -/
theorem refc_commit {s : Site} {q' : Nat} {v : V} {n : Cnt → Nat} {r : Nat} {w : Bool}
    {o0 pc : Nat} {sp : TcCommit.Spec}
    (hQ : RefQ p L g s.ord v n r w ∧ (s.ord ∈ cmQ → w = true)) (hs : s.ord ∈ cmQ)
    (hm : qmove s.ord s.ord q' = true) (hloc : sp.mbar = bl L g o0)
    (hA : ∀ o, acqD s.ord s.ord r o = 0)
    (hD : ∀ o, comD s.ord s.ord r o = if o = o0 then 1 else 0) (hE : elD s.ord = 0)
    (hS : shD s.ord = 0 := by decide) :
    RefQ p L g q' v (Code.bump (cls L g) n ⟨pc, .tc (.commit sp)⟩) r w := by
  have hw := hQ.2 hs
  subst hw
  refine refQ_move hQ.1 hm (fun o => ?_) (fun o => ?_) ?_ ?_
    (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by simp [hS])
  · rw [hA]; simp [Code.bump, cls]
  · rw [hD]
    by_cases ho : o = o0
    · subst ho; simp [Code.bump, cls, hloc]
    · have : ¬ bl L g o0 = bl L g o := fun h => ho (bl_inj.mp h).symm
      simp [Code.bump, cls, hloc, ho, this]
  · rw [hE]; simp [Code.bump, cls]
  · rw [hE]; simp [Code.bump, cls]

/-- An election: the lane wins all elections or none (`Expect`), so the counts continue with
`w` the outcome. -/
theorem refc_elect {s : Site} {q' : Nat} {v v' : V} {n : Cnt → Nat} {r : Nat} {w : Bool}
    {pc inst ld : Nat} (hQ : RefQ p L g s.ord v n r w)
    (hE : ExpectElect L g (⟨s, v⟩, n) ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩)
    (hm : qmove s.ord s.ord q' = true)
    (hA : ∀ o, acqD s.ord s.ord r o = 0) (hC : ∀ o, comD s.ord s.ord r o = 0)
    (hel : elD s.ord = 1)
    (hfirst : electAll s.ord r = 0 → ∀ o, commitAt s.ord r o = 0)
    (hv : 20 ≤ s.ord ∧ s.ord < 100 → v'.slot = v.slot ∧ v'.kvp = v.kvp ∧ v'.pp = v.pp ∧
      v'.accum = v.accum ∧ v'.trip = v.trip ∧ blocks p L g v' = blocks p L g v)
    (hps : v'.ps = v.ps := by rfl) (hS : shD s.ord = 0 := by decide) :
    RefQ p L g q' v' (Code.bump (cls L g) n ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩) r
      (decide (ld = laneOf L g)) := by
  have hEl := hE _ inst ld rfl
  simp only at hEl
  have key : (ld = laneOf L g → w = false → electAll s.ord r = 0) ∧
      (ld ≠ laneOf L g → w = true → electAll s.ord r = 0) := by
    refine ⟨fun hl hw => ?_, fun hl hw => ?_⟩
    · have := hQ.lost; rw [hw] at this; simp only [Bool.false_eq_true, ↓reduceIte] at this
      by_contra h0; exact hEl.2 (by omega) hl
    · have := hQ.won; rw [hw] at this; simp only [↓reduceIte] at this
      by_contra h0; exact hl (hEl.1 (by omega))
  -- the counts as if the lane had always had the outcome of this election
  have hQ' : RefQ p L g s.ord v n r (decide (ld = laneOf L g)) := by
    by_cases hl : ld = laneOf L g <;> cases w <;> simp only [hl, decide_true, decide_false] <;>
      first
      | exact hQ
      | (have h0 := key.1 hl rfl
         exact ⟨hQ.pre, hQ.regs, hQ.loop, hQ.tail, hQ.acq, fun o => by
           rw [hQ.com o]; simp [hfirst h0 o], by rw [hQ.won]; simp [h0],
           by rw [hQ.lost]; simp [h0], hQ.ps⟩)
      | (have h0 := key.2 hl rfl
         exact ⟨hQ.pre, hQ.regs, hQ.loop, hQ.tail, hQ.acq, fun o => by
           rw [hQ.com o]; simp [hfirst h0 o], by rw [hQ.won]; simp [h0],
           by rw [hQ.lost]; simp [h0], hQ.ps⟩)
  refine refQ_move hQ' hm (fun o => ?_) (fun o => ?_) ?_ ?_ hv (by simp [hps, hS])
  · rw [hA]; simp [Code.bump, cls]
  · rw [hC]; simp [Code.bump, cls]
  · rw [hel]; by_cases hl : ld = laneOf L g <;> simp [Code.bump, cls, hl]
  · rw [hel]; by_cases hl : ld = laneOf L g <;> simp [Code.bump, cls, hl]

/-- A move that passes a commit the lane does not issue (it lost the election). -/
theorem refQ_skip {q q' : Nat} {v : V} {n : Cnt → Nat} {r : Nat}
    (hQ : RefQ p L g q v n r false) (hm : qmove q q q' = true)
    (hA : ∀ o, acqD q q r o = 0) (hE : elD q = 0) (hS : shD q = 0 := by decide) :
    RefQ p L g q' v n r false :=
  refQ_move hQ hm (fun o => by simp [hA]) (fun o => by simp) (by simp) (by simp [hE])
    (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by simp [hS])

/-- An election whose successor is no commit site. -/
theorem refc_elect' {s s' : Site} {v v' : V} {n : Cnt → Nat} {r : Nat} {w : Bool}
    {pc inst ld : Nat} (hQ : RefQ p L g s.ord v n r w)
    (hE : ExpectElect L g (⟨s, v⟩, n) ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩)
    (hm : qmove s.ord s.ord s'.ord = true)
    (hA : ∀ o, acqD s.ord s.ord r o = 0) (hC : ∀ o, comD s.ord s.ord r o = 0)
    (hel : elD s.ord = 1) (hfirst : electAll s.ord r = 0 → ∀ o, commitAt s.ord r o = 0)
    (hv : 20 ≤ s.ord ∧ s.ord < 100 → v'.slot = v.slot ∧ v'.kvp = v.kvp ∧ v'.pp = v.pp ∧
      v'.accum = v.accum ∧ v'.trip = v.trip ∧ blocks p L g v' = blocks p L g v)
    (hcm : s'.ord ∉ cmQ) (hps : v'.ps = v.ps := by rfl) (hS : shD s.ord = 0 := by decide) :
    RefCounts p L g (⟨s', v'⟩, Code.bump (cls L g) n ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩) :=
  ⟨r, _, refc_elect hQ hE hm hA hC hel hfirst hv hps hS, fun h => absurd h hcm⟩

theorem shD_ce (c : Fin 12) : shD (Site.ce c).ord = 0 := by fin_cases c <;> decide
theorem shD_cm (c : Fin 12) : shD (Site.cm c).ord = 0 := by fin_cases c <;> decide

/-- The election before commit `c` on the lane that wins it: the counts at the commit. -/
theorem refc_win {c : Fin 12} {v : V} {n : Cnt → Nat} {r : Nat} {w : Bool} {pc inst ld : Nat}
    (hQ : RefQ p L g (Site.ce c).ord v n r w)
    (hE : ExpectElect L g (⟨.ce c, v⟩, n) ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩) (hl : ld = laneOf L g)
    (hm : qmove (Site.ce c).ord (Site.ce c).ord (Site.cm c).ord = true)
    (hA : ∀ o, acqD (Site.ce c).ord (Site.ce c).ord r o = 0)
    (hC : ∀ o, comD (Site.ce c).ord (Site.ce c).ord r o = 0) (hel : elD (Site.ce c).ord = 1)
    (hfirst : electAll (Site.ce c).ord r = 0 → ∀ o, commitAt (Site.ce c).ord r o = 0) :
    RefCounts p L g (⟨.cm c, v⟩, Code.bump (cls L g) n ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩) := by
  have h := refc_elect (v' := v) hQ hE hm hA hC hel hfirst (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    rfl (shD_ce c)
  rw [decide_eq_true hl] at h
  exact ⟨r, true, h, fun _ => rfl⟩

/-- The election before commit `c` on a lane that loses it: the counts after the commit. -/
theorem refc_lose {c : Fin 12} {v : V} {n : Cnt → Nat} {r : Nat} {w : Bool} {pc inst ld : Nat}
    (hQ : RefQ p L g (Site.ce c).ord v n r w)
    (hE : ExpectElect L g (⟨.ce c, v⟩, n) ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩) (hl : ld ≠ laneOf L g)
    (hm : qmove (Site.ce c).ord (Site.ce c).ord (Site.cm c).ord = true)
    (hA : ∀ o, acqD (Site.ce c).ord (Site.ce c).ord r o = 0)
    (hC : ∀ o, comD (Site.ce c).ord (Site.ce c).ord r o = 0) (hel : elD (Site.ce c).ord = 1)
    (hfirst : electAll (Site.ce c).ord r = 0 → ∀ o, commitAt (Site.ce c).ord r o = 0)
    (hm2 : qmove (Site.cm c).ord (Site.cm c).ord ((Site.cm c).ord + 1) = true)
    (hA2 : ∀ o, acqD (Site.cm c).ord (Site.cm c).ord r o = 0) (hE2 : elD (Site.cm c).ord = 0) :
    RefQ p L g ((Site.cm c).ord + 1) v (Code.bump (cls L g) n ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩) r
      false := by
  have h := refc_elect (v' := v) hQ hE hm hA hC hel hfirst (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    rfl (shD_ce c)
  rw [decide_eq_false hl] at h
  exact refQ_skip h hm2 hA2 hE2 (shD_cm c)

/-! ### The loop's entry and end -/

theorem neg32_eq (x : BitVec 64) : neg32 x = i32 (0 - toSigned 32 (r32 x)) :=
  PTX.Flow.Arith32.neg_eq x

/-- The loop registers after a round. -/
def endV (v : V) : V :=
  { v with
    slot := sel (scmpi .eq .b (addi (slot1 v) 1) 3) (i32 0) (addi (slot1 v) 1),
    kvp := xor32 (kvp1 v) (sel (scmpi .eq .b (addi (slot1 v) 1) 3) (i32 1) (i32 0)),
    pp := xori v.pp 1, trip := addi v.trip 1, accum := i32 1 }

theorem loopEnd_eq (d : D) : loopEnd d =
    if scmpi .ne .b (addi d.v.trip 1) (-1) then ⟨.wt 3, endV d.v⟩ else ⟨.ce 7, endV d.v⟩ := rfl

theorem loopEnd_regs {v : V} {r : Nat} (h : LoopRegs v r) : LoopRegs (endV v) (r + 1) := by
  have h1 := slot1_eq h
  obtain ⟨-, -, hp, -⟩ := h
  obtain ⟨hs1, hk1⟩ := h1
  simp only [LoopRegs, endV, hs1, hk1, hp]
  have h6 : r % 6 < 6 := Nat.mod_lt _ (by decide)
  refine ⟨?_, ?_, ?_, by simp [iw]⟩
  · interval_cases hr : r % 6
    all_goals first
      | (rw [show (2 * r + 2) % 3 = 2 by omega, show (2 * (r + 1) + 1) % 3 = 0 by omega]; decide)
      | (rw [show (2 * r + 2) % 3 = 1 by omega, show (2 * (r + 1) + 1) % 3 = 2 by omega]; decide)
      | (rw [show (2 * r + 2) % 3 = 0 by omega, show (2 * (r + 1) + 1) % 3 = 1 by omega]; decide)
  · interval_cases hr : r % 6
    all_goals first
      | (rw [show (2 * r + 2) % 3 = 2 by omega, show (2 * r + 2) / 3 % 2 = 0 by omega,
          show (2 * (r + 1) + 1) / 3 % 2 = 1 by omega]; decide)
      | (rw [show (2 * r + 2) % 3 = 1 by omega, show (2 * r + 2) / 3 % 2 = 1 by omega,
          show (2 * (r + 1) + 1) / 3 % 2 = 1 by omega]; decide)
      | (rw [show (2 * r + 2) % 3 = 0 by omega, show (2 * r + 2) / 3 % 2 = 0 by omega,
          show (2 * (r + 1) + 1) / 3 % 2 = 0 by omega]; decide)
  · rcases Nat.mod_two_eq_zero_or_one r with h2 | h2
    · rw [h2, show (r + 1) % 2 = 1 by omega]; decide
    · rw [h2, show (r + 1) % 2 = 0 by omega]; decide

/-- A place that is no commit site. -/
macro "not_cm" : term =>
  `(fun h => absurd h (by simp [Site.ord, cmQ, ceNext, scAt, Epilogue.Scan.late]))

/-- The successor of commit `c`, from the place after it. -/
theorem ceNext_ref {c : Fin 12} {s0 : Site} {v : V} {n : Cnt → Nat} {r : Nat} {w : Bool}
    (hQ : RefQ p L g ((Site.cm c).ord + 1) v n r w) :
    RefCounts p L g (ceNext p L g ⟨s0, v⟩ c, n) := by
  fin_cases c
  case «2» =>
    replace hQ : RefQ p L g 17 v n r w := hQ
    have hr := hQ.pre (by decide)
    subst hr
    simp only [ceNext, enterLoop]
    have hB := toSigned_r32 (blocks p L g v)
    have h2 : toSigned 32 (i32 2) = 2 := by decide
    split <;> rename_i hlt <;> simp only [scmpi, compare, decide_eq_true_eq, h2] at hlt
    · refine ⟨0, w, ?_, not_cm⟩
      show RefQ p L g 60 _ n 0 w
      refine ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl, rfl⟩,
        fun h => absurd h (by decide), fun _ => .inr ⟨rfl, ?_⟩, fun o => ?_, fun o => ?_, ?_, ?_,
        ?_⟩
      · show toSigned 32 (r32 (blocks p L g v)) < 2
        exact hlt
      all_goals first
        | (rw [hQ.acq]; simp [acqAt, ringAcq, pq])
        | (rw [hQ.com]; simp [commitAt, ringRel, pq])
        | (rw [hQ.won]; simp [electAll, pq])
        | (rw [hQ.lost]; simp [electAll, pq])
        | (simp only [hQ.ps]; simp [shAt, pq])
    · refine ⟨0, w, ?_, not_cm⟩
      show RefQ p L g 20 _ n 0 w
      refine ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl, rfl⟩,
        fun _ => ⟨?_, ?_⟩, fun h => absurd h (by decide), fun o => ?_, fun o => ?_, ?_, ?_, ?_⟩
      · show (0 : Int) + 1 < toSigned 32 (r32 (blocks p L g v))
        omega
      · simp only [Bs, neg32_eq]; rfl
      all_goals first
        | (rw [hQ.acq]; simp [acqAt, ringAcq, pq])
        | (rw [hQ.com]; simp [commitAt, ringRel, pq])
        | (rw [hQ.won]; simp [electAll, pq])
        | (rw [hQ.lost]; simp [electAll, pq])
        | (simp only [hQ.ps]; simp [shAt, pq])
  case «6» =>
    replace hQ : RefQ p L g 50 v n r w := hQ
    have hR := loopEnd_regs (hQ.regs (by decide))
    obtain ⟨hlt, htrip⟩ := hQ.loop (by decide)
    have hB := toSigned_r32 (blocks p L g v)
    have ht : (endV v).trip = i32 (((r + 1 : Nat) : Int) - Bs p L g v) := by
      simp only [endV, htrip, i32_addi]; congr 1; push_cast; ring
    have hBe : Bs p L g (endV v) = Bs p L g v := rfl
    simp only [ceNext, loopEnd_eq]
    split <;> rename_i hne <;> rw [htrip, i32_addi] at hne
    · have hne' := (ne_m1 (by simp only [Bs] at hlt hB ⊢; omega) (by omega)).mp hne
      refine ⟨r + 1, w, ?_, not_cm⟩
      show RefQ p L g 20 (endV v) n (r + 1) w
      refine ⟨fun h => absurd h (by decide), fun _ => hR, fun _ => ⟨?_, ?_⟩,
        fun h => absurd h (by decide), fun o => ?_, fun o => ?_, ?_, ?_, ?_⟩
      · rw [hBe]; push_cast; omega
      · rw [hBe]; exact ht
      all_goals first
        | (rw [hQ.acq]; simp [acqAt, ringAcq, pq]; done)
        | (rw [hQ.com]; simp [commitAt, ringRel, pq]; done)
        | (rw [hQ.won]; simp [electAll, pq] <;> omega)
        | (rw [hQ.lost]; simp [electAll, pq] <;> omega)
        | (simp only [endV, hQ.ps]; simp [shAt, pq] <;> omega)
    · have hne' : ¬ ((r : Int) - Bs p L g v + 1 ≠ -1) := fun h =>
        hne ((ne_m1 (by simp only [Bs] at hlt hB ⊢; omega) (by omega)).mpr h)
      refine ⟨r + 1, w, ?_, not_cm⟩
      show RefQ p L g 60 (endV v) n (r + 1) w
      refine ⟨fun h => absurd h (by decide), fun _ => hR, fun h => absurd h (by decide),
        fun _ => .inl ?_, fun o => ?_, fun o => ?_, ?_, ?_, ?_⟩
      · rw [hBe]; push_cast; omega
      all_goals first
        | (rw [hQ.acq]; simp [acqAt, ringAcq, pq]; done)
        | (rw [hQ.com]; simp [commitAt, ringRel, pq]; done)
        | (rw [hQ.won]; simp [electAll, pq] <;> omega)
        | (rw [hQ.lost]; simp [electAll, pq] <;> omega)
        | (simp only [endV, hQ.ps]; simp [shAt, pq] <;> omega)
  case «11» =>
    replace hQ : RefQ p L g 86 v n r w := hQ
    simp only [ceNext, passStart, ↓reduceIte]
    split_ifs <;> refine ⟨r, w, ?_, not_cm⟩ <;>
      show RefQ p L g 100 _ n r w <;>
      refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun o => ?_, fun o => ?_, ?_,
        ?_, ?_⟩
    all_goals first
      | (rw [hQ.acq]; simp [acqAt, ringAcq, pq]; done)
      | (rw [hQ.com]; simp [commitAt, ringRel, pq]; done)
      | (rw [hQ.won]; simp [electAll, pq]; done)
      | (rw [hQ.lost]; simp [electAll, pq]; done)
      | (simp only [hQ.ps]; simp [shAt, pq]; done)
  all_goals exact ⟨r, w, hQ, not_cm⟩

/-- A commit, then its successor. -/
theorem refc_commit_next {c : Fin 12} {s0 : Site} {v : V} {n : Cnt → Nat} {r : Nat} {w : Bool}
    {o0 pc : Nat} {sp : TcCommit.Spec}
    (hQ : RefQ p L g (Site.cm c).ord v n r w ∧ ((Site.cm c).ord ∈ cmQ → w = true))
    (hs : (Site.cm c).ord ∈ cmQ)
    (hm : qmove (Site.cm c).ord (Site.cm c).ord ((Site.cm c).ord + 1) = true)
    (hloc : sp.mbar = bl L g o0) (hA : ∀ o, acqD (Site.cm c).ord (Site.cm c).ord r o = 0)
    (hD : ∀ o, comD (Site.cm c).ord (Site.cm c).ord r o = if o = o0 then 1 else 0)
    (hE : elD (Site.cm c).ord = 0) :
    RefCounts p L g (ceNext p L g ⟨s0, v⟩ c, Code.bump (cls L g) n ⟨pc, .tc (.commit sp)⟩) :=
  ceNext_ref (refc_commit (s := .cm c) hQ hs hm hloc hA hD hE (shD_cm c))

theorem afterTiles_ord {d d' : D} {x : BitVec 64}
    (h : (afterTiles p L g d x).map some = some (some d')) :
    d'.site.ord = 0 ∧ d'.v.ps = d.v.ps := by
  simp only [afterTiles] at h
  split_ifs at h <;> simp at h
  all_goals (subst h; exact ⟨rfl, rfl⟩)

/-- The places of concrete sites as numbers. -/
macro "ord_simp" : tactic => `(tactic| simp only [Site.ord, Fin.isValue, Fin.coe_ofNat_eq_mod,
  Nat.reduceMod, List.getD_cons_succ, List.getD_cons_zero, wtNext, shNext, qkDone, pvDone,
  ↓reduceIte, Bool.false_eq_true])

/-- What a move between concrete places adds to the counts. -/
macro "cnt_tac" : tactic => `(tactic| (
  first
    | (intro o; (try ord_simp); simp [acqD, comD, ringA, ringR, ringAcq, ringRel, pq, cmO,
        Fin.coe_ofNat_eq_mod, List.getD_cons_succ, List.getD_cons_zero] <;>
        (try split_ifs) <;> omega)
    | ((try ord_simp); simp [elD])
    | (intro h o
       simp only [Site.ord, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.getD_cons_succ,
         List.getD_cons_zero] at h ⊢
       simp [electAll, commitAt, ringRel, pq, ringCount] at h ⊢ <;> omega)))

set_option hygiene false in
/-- Before the pipeline no loop round is done: `r = 0` from the reference invariant. -/
macro "pre_r" : tactic => `(tactic| try (
  have hr := hQ.1.pre
  simp only [Site.ord, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.getD_cons_succ,
    List.getD_cons_zero, Nat.reduceLT, true_implies, false_implies] at hr
  try subst hr))

set_option hygiene false in
/-- The location of a poll or commit as the barrier at its offset. -/
macro "loc_tac" : tactic => `(tactic| (
  simp only [wtOp, mwOp, cmOp, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, ↓reduceIte] at *
  first
    | rw [(slot1_eq (hQ.1.regs (by decide))).1, smLoc_slot hp (by omega)]
    | rw [(slot1_eq (hQ.1.regs (by decide))).1, smLoc_slot56 hp (by omega)]
    | rw [(hQ.1.regs (by decide)).1, smLoc_slot hp (by omega)]
    | rw [(hQ.1.regs (by decide)).1, smLoc_slot56 hp (by omega)]
    | rw [smLoc_sb144 hp]
    | simp (disch := decide) only [smLoc_addi hp, smLoc_sbW hp, smLoc_sb144 hp, Int.toNat_zero,
        Int.reduceToNat]))

set_option hygiene false in
/-- A quiet step of a branch `hn : X = d'` (or its symmetric form). -/
macro "rq_quiet" : tactic => `(tactic| (
  first | subst hn | (simp only [Option.some.injEq] at hn; subst hn)
  exact refc_quiet hQ (by simp [quietK])
    (by simp only [Site.ord, Epilogue.Scan.late, Epilogue.loopOf, Fin.isValue, shNext, qkDone,
      pvDone, wtNext, ↓reduceIte, Bool.false_eq_true]; decide)
    (by simp only [Site.ord, Epilogue.Scan.late, Epilogue.loopOf, Fin.isValue, shNext, qkDone,
      pvDone, wtNext, ↓reduceIte, Bool.false_eq_true]; decide)
    (by first
      | (intro h; simp [Site.ord, Epilogue.Scan.late, Fin.isValue] at h; done)
      | exact (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
      | exact (fun _ => setS_same _ _ _))
    rfl))

/-- The step obligation of the counts at site `s`: a step of the machine from a state at `s` on
an expected event of the state's shape that is not undefined behaviour keeps `RefCounts`. -/
def StepRef (p : Params) (L : Launch) (g : Nat) (s : Site) : Prop :=
  ∀ (v : V) (n : Cnt → Nat) (r : Nat) (w : Bool) (pc : Nat) (k : Kind) (d' : D),
    RefQ p L g s.ord v n r w ∧ (s.ord ∈ cmQ → w = true) →
    ExpectElect L g (⟨s, v⟩, n) ⟨pc, k⟩ → Ev p L g ⟨s, v⟩ ⟨pc, k⟩ → (∀ f, k ≠ .ub f) →
    succ p L g ⟨s, v⟩ ⟨pc, k⟩ = some (some d') → RefCounts p L g (d', Code.bump (cls L g) n ⟨pc, k⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
