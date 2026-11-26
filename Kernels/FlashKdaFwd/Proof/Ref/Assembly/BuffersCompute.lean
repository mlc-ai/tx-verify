-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.BuffersLib
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProtocolLib

@[expose] public section

/-!
# The share of the Compute phase in the buffer contracts

`computeOwes : Buffers.ComputeOwes P L X` for every consistent execution: the four facts about
the events of a compute thread in the tile loop (the Compute phase, instructions 2106 to 2944)
that `Buffers.lean` needs for the contracts `UnionFacts`, `StoreCover` and `StoresIssued` of
the protocol layer.

**Words.** A *position* of the Compute phase is the entry or the pair of a tile `t` and an
index `n < 268` in the tile's straight line of 268 events (`Compute.Pos`). `Proto` below is the
namespace `Compute.Proto` of the Compute phase's protocol exports. The memory access of a
position is the footprint `Proto.accOf P L g t n`: in the shared memory of the thread's own
block, at the closed form of an address register (`Compute.regVal`) plus a constant, of the
size the table `Compute.addrTab` gives (`Proto.addrOf n`: register, constant, size). A *row*
is 16 bytes: an `ldmatrix` reads one row per lane, an `stmatrix` writes one. `tid g` is the
index of thread `g` in its block. The tile `t` uses input buffer `t % 3` and output buffer
`t % 2`.

## The accesses of a tile, by region (`acc_class`)

A position with a memory access is one of five kinds, by its address register:

* a row of the bfloat16 state copy (16 registers; offsets below 32768 of the window): read by
  an `ldmatrix`, written by an `stmatrix`; not in the buffer region;
* a row of the input buffer of the tile (28 registers): a read;
* a row of the output buffer of the tile (registers 1672 and 1677, positions 165 and 167: the
  row writes of the first two `stmatrix`): a write of the two rows of the lane, at offsets
  `1024 * (tid / 32) + 16 * (tid % 32)` and that plus 512 of the buffer;
* one of the two gate logits (2 bytes) and one of the sixteen decay factors (4 bytes) in the
  input buffer of the tile: scalar reads.

So an access of a byte of the buffer region is a read of the tile's input buffer (class
`input` of `Protocol.ThreadClass`) or a write of the tile's output buffer (class `output`), and
the owner function `Buffers.outOwner` names the writing lane (`outOwner_row`,
`row_of_owner`).

## The four facts

* `compute_thread` (`UnionFacts.thread`): the class of an access, with the gates from the
  ledger: at a position between the polls and the named barrier the thread has polled
  `loadFull` and `storeEmpty` of the tile's stages once more than it has arrived on `loadEmpty`
  and `storeFull`.
* `compute_out_cover` (`StoreCover.out_cover`): the arrival on `storeFull` is position 266 of
  a tile; the two row writes of the output buffer are positions 165 and 167 of the same tile,
  101 and 99 events earlier (`Proto.back`), with the same number of arrivals before them.
* `compute_matrix_len` (`StoreCover.matrix_len`): the write event of an `stmatrix` carries the
  bytes of the row that the state's site holds (`Proto.acc_at`); that state is the successor
  of the instruction's matrix event, which put 16 known bytes there (`Proto.st_row`).
* `compute_wr_shared`: a write event is at a position's footprint, in shared memory.

The tools are the Compute phase's own (`Ref/Compute/ExportsProtocolAccess.lean`,
`ExportsProtocolLib.lean`): the event of a position in closed form (`Proto.EvAt`,
`Proto.ev_at`), the invariant with its position (`Proto.InvAt`), the earlier states
(`Proto.step_back`, `Proto.back`), the ledger readouts (`Proto.cnt_*`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (Owners Bar bar0Before InUnion InInput InOutput InShared
  ThreadClass computeThread uses)
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute (skOf regVal)
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute.Proto (addrOf accOf isWr InvAt)

noncomputable section

-- `omega` compares a hypothesis and a goal that differ in the grouping of large literals by
-- unfolding the literals, which needs a deeper recursion than the default.
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

namespace Buffers

/-! ### The accesses of a tile, by region -/

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The five kinds of memory access of a tile** (see the header): a row of the state copy, a
row of the input buffer (read), a row of the output buffer (written), a gate logit (read), a
decay factor (read). -/
theorem acc_class : ∀ n < 268, (addrOf n).2.2 ≠ 0 →
    ((addrOf n).1 ∈ Compute.accRegs ∧ (addrOf n).2.1 = 0 ∧ (addrOf n).2.2 = 16) ∨
    ((addrOf n).1 ∈ Compute.inRegs ∧ (addrOf n).2.1 = 0 ∧ (addrOf n).2.2 = 16 ∧
      isWr (skOf n) = false) ∨
    ((addrOf n).1 ∈ Compute.outRegs ∧ (addrOf n).2.1 = 0 ∧ (addrOf n).2.2 = 16 ∧
      isWr (skOf n) = true) ∨
    ((addrOf n).1 = 1948 ∧ ((addrOf n).2.1 = 36864 ∨ (addrOf n).2.1 = 36880) ∧
      (addrOf n).2.2 = 2 ∧ isWr (skOf n) = false) ∨
    ((addrOf n).1 = 2014 ∧ 49280 ≤ (addrOf n).2.1 ∧ (addrOf n).2.1 ≤ 49760 ∧
      (addrOf n).2.1 % 4 = 0 ∧ (addrOf n).2.2 = 4 ∧ isWr (skOf n) = false) := by
  decide +kernel

/-- A list of known bytes keeps its length when the options are dropped. -/
theorem reduceOption_length_of_all {α : Type} (l : List (Option α))
    (h : l.all Option.isSome = true) : l.reduceOption.length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a with
    | none => simp at h
    | some a =>
      have h' : l.all Option.isSome = true := by simpa using h
      simpa [List.reduceOption, List.filterMap_cons] using ih h'

/-- A row write of an `stmatrix` is a position from 3 on, of 16 bytes. -/
theorem wr_pos : ∀ n < 268, isWr (skOf n) = true → 3 ≤ n ∧ (addrOf n).2.2 = 16 := by
  decide +kernel

/-- Positions 165 and 167 of a tile are the row writes of the two rows of the output buffer. -/
theorem out_pos : addrOf 165 = (1672, 0, 16) ∧ addrOf 167 = (1677, 0, 16) ∧
    isWr (skOf 165) = true ∧ isWr (skOf 167) = true := by
  decide +kernel

/-- **A byte of one of the lane's two rows of the output buffer is the lane's own.** -/
theorem outOwner_row (ht : tid g < 128) {l : Loc} {t r : Nat} (hr : r ∈ Compute.outRegs)
    (h1 : regVal P g t r ≤ l.addr) (h2 : l.addr < regVal P g t r + 16) :
    outOwner P l = tid g := by
  have h128 : tid g < 128 := ht
  have hm : t % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [Compute.outRegs, List.mem_cons, List.mem_nil_iff, or_false] at hr
  unfold outOwner
  rcases hr with rfl | rfl
  · rw [Compute.rv_1672] at h1 h2
    simp only [Compute.warpOff, Compute.laneOff] at h1 h2
    omega
  · rw [Compute.rv_1677] at h1 h2
    simp only [Compute.warpOff, Compute.laneOff] at h1 h2
    omega

/-- **A byte of the output buffer of tile `t` that the lane owns is in one of its two rows.** -/
theorem row_of_owner (hpre : Pre P L mem0) (ht : tid g < 128) {l : Loc} {t : Nat}
    (hl : InOutput L (g / L.block) (t % 2) l) (ho : outOwner P l = tid g) :
    (regVal P g t 1672 ≤ l.addr ∧ l.addr < regVal P g t 1672 + 16) ∨
      (regVal P g t 1677 ≤ l.addr ∧ l.addr < regVal P g t 1677 + 16) := by
  have h128 : tid g < 128 := ht
  have hm : t % 2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨-, -, h3, h4⟩ := hl
  rw [hpre.sharedBase] at h3 h4
  rw [Compute.rv_1672, Compute.rv_1677]
  simp only [Compute.warpOff, Compute.laneOff]
  unfold outOwner at ho
  omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-! ### The position of a read or a write -/

/-- **A read or a write event at a state of the Compute phase is the access of a position**
between the polls and the named barrier of a tile: its footprint is the position's, a read is
at no row-write site and a write is at one. -/
theorem acc_pos_of {j0 k : Nat} {s : D} {e : Event} {a : Acc} (hσ : At (code L) X g k s)
    (hI : Compute.Inv P L X g j0 k s) (he : X.get (g, k) = some e)
    (hk : (∃ bs, e.kind = .rd a bs) ∨ ∃ bs, e.kind = .wr a bs) :
    ∃ t n, InvAt P L X g j0 k (.tile t n) s ∧ 2 ≤ n ∧ n < 264 ∧ (addrOf n).2.2 ≠ 0 ∧
      a = accOf P L g t n ∧ ((∃ bs, e.kind = .rd a bs) → isWr (skOf n) = false) ∧
      ((∃ bs, e.kind = .wr a bs) → isWr (skOf n) = true) := by
  obtain ⟨pos, hR, hl, hjk, hcnt⟩ := hI
  have hev := Compute.Proto.ev_at hpre hX hR hσ he
  cases pos with
  | entry =>
    rw [show e = _ from hev] at hk
    rcases hk with ⟨bs, h⟩ | ⟨bs, h⟩ <;> cases h
  | tile t n =>
    have hn : n < 268 := hR.facts.pos
    rcases Compute.Proto.pos_cases hn with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h2, h264⟩
    · obtain ⟨ok, rfl⟩ := Compute.Proto.evAt_0.mp hev
      rcases hk with ⟨bs, h⟩ | ⟨bs, h⟩ <;> cases h
    · obtain ⟨ok, rfl⟩ := Compute.Proto.evAt_1.mp hev
      rcases hk with ⟨bs, h⟩ | ⟨bs, h⟩ <;> cases h
    · obtain rfl := Compute.Proto.evAt_264.mp hev
      rcases hk with ⟨bs, h⟩ | ⟨bs, h⟩ <;> cases h
    · obtain rfl := Compute.Proto.evAt_265.mp hev
      rcases hk with ⟨bs, h⟩ | ⟨bs, h⟩ <;> cases h
    · obtain rfl := Compute.Proto.evAt_266.mp hev
      rcases hk with ⟨bs, h⟩ | ⟨bs, h⟩ <;> cases h
    · obtain rfl := Compute.Proto.evAt_267.mp hev
      rcases hk with ⟨bs, h⟩ | ⟨bs, h⟩ <;> cases h
    · rw [Compute.Proto.evAt_body h2 h264] at hev
      by_cases ha : (addrOf n).2.2 = 0
      · rw [ite_eq_left ha] at hev
        rcases hev with ⟨op, own, recv, h'⟩ | ⟨f, h'⟩ <;> rcases hk with ⟨bs, h⟩ | ⟨bs, h⟩ <;>
          rw [h'] at h <;> cases h
      · rw [ite_eq_right ha] at hev
        rcases hev with ⟨bs1, h1, hw1⟩ | ⟨bs1, h1, hw1⟩
        · rcases hk with ⟨bs, h⟩ | ⟨bs, h⟩
          · rw [h1] at h
            cases h
            exact ⟨t, n, ⟨hR, hl, hjk, hcnt⟩, h2, h264, ha, rfl, fun _ => hw1,
              fun ⟨bs', h'⟩ => (by rw [h1] at h'; cases h')⟩
          · rw [h1] at h
            cases h
        · rcases hk with ⟨bs, h⟩ | ⟨bs, h⟩
          · rw [h1] at h
            cases h
          · rw [h1] at h
            cases h
            exact ⟨t, n, ⟨hR, hl, hjk, hcnt⟩, h2, h264, ha, rfl,
              fun ⟨bs', h'⟩ => (by rw [h1] at h'; cases h'), fun _ => hw1⟩

/-! ### The four facts -/

/-- **The frame of the writes**: a write event at a state of the Compute phase is in shared
memory. -/
theorem compute_wr_shared {j0 k pc : Nat} {s : D} {a : Acc} {bs : List Byte}
    (hσ : At (code L) X g k s) (hI : Compute.Inv P L X g j0 k s)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) : a.loc.space = .shared := by
  obtain ⟨t, n, -, -, -, -, rfl, -⟩ := acc_pos_of hpre hX hσ hI he (.inr ⟨bs, rfl⟩)
  rfl

/-- **`StoreCover.matrix_len`**: a write event at a state of the Compute phase (the row write
of an `stmatrix`) carries 16 bytes, the size of its footprint: the bytes of the row that the
matrix event of the instruction, one event earlier, put into the state's site. -/
theorem compute_matrix_len (hg : g < L.threads) {j0 k pc : Nat} {s0 s : D} {a : Acc}
    {bs : List Byte} (h0 : At (code L) X g j0 s0) (hin : Compute.In P L X g j0 s0)
    (hσ : At (code L) X g k s) (hI : Compute.Inv P L X g j0 k s)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) : bs.length = a.size := by
  have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨t, n, hIA, h2, h264, ha, rfl, -, hwr⟩ :=
    acc_pos_of hpre hX hσ hI he (.inr ⟨bs, rfl⟩)
  have hw : isWr (skOf n) = true := hwr ⟨bs, rfl⟩
  have hn : n < 268 := by omega
  obtain ⟨h3, hsz⟩ := wr_pos n hn hw
  -- the state one event earlier is at the matrix event of the same `stmatrix`
  obtain ⟨-, s', e', -, hIA', -, hnext⟩ :=
    Compute.Proto.step_back hpre hX hg h0 hin hlt.le hσ hIA h3
  obtain ⟨site', w', p', x'⟩ := s'
  have hs' : (skOf (n - 1)).At site' := hIA'.1.site
  obtain ⟨j', row', hrow, hlen, hall⟩ := Compute.Proto.st_row (n := n - 1) (by omega)
    (by rw [Nat.sub_add_cancel (by omega)]; exact hw) hs' hnext
  -- the write event carries the row of the state's site
  obtain ⟨tt, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  obtain ⟨site, w, p, x⟩ := s
  have hsite : (skOf n).At site := hIA.1.site
  rcases Compute.Proto.acc_at hpre hIA.1.facts hsite hat hc hf ha with
    ⟨bs', -, hf'⟩ | ⟨j, row, hs, hkd, -⟩
  · rw [hw] at hf'
    cases hf'
  · obtain rfl : bs = row.reduceOption := by
      cases hkd
      rfl
    have hsr : Site.matrixStoreWr j' row' = Site.matrixStoreWr j row := hrow.symm.trans hs
    obtain rfl : row' = row := (Site.matrixStoreWr.inj hsr).2
    have hfull : row'.reduceOption.length = row'.length :=
      reduceOption_length_of_all row' hall
    show row'.reduceOption.length = (addrOf n).2.2
    rw [hfull, hlen, hsz]

/-- **`UnionFacts.thread` for the Compute phase**: a thread access, at a state of the phase,
of a byte of the buffer region of a block is of the thread's own block and is a read of the
input buffer of its tile (class `input`) or a write of a byte it owns of the output buffer of
its tile (class `output`), with six `bar.sync 0` before it and inside the gates of the
stages. -/
theorem compute_thread {j0 k c : Nat} {s : D} {a : Acc} {w : Bool} {l : Loc} (O : Owners)
    (hOut : O.out = outOwner P) (hσ : At (code L) X g k s) (hI : Compute.Inv P L X g j0 k s)
    (hacc : X.Access (g, k) a w) (hcov : a.Covers l) (hin : InUnion L c l) :
    g / L.block = c ∧ ThreadClass L X O c g k w l := by
  obtain ⟨e, he, hk, hw⟩ : ∃ e, X.get (g, k) = some e ∧
      ((∃ bs, e.kind = .rd a bs) ∨ ∃ bs, e.kind = .wr a bs) ∧
      ((∃ bs, e.kind = .rd a bs) → w = false) ∧ ((∃ bs, e.kind = .wr a bs) → w = true) := by
    rcases hacc with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨o, n, pc, he⟩
    · exact ⟨_, he, .inl ⟨bs, rfl⟩, fun _ => rfl, fun ⟨bs', h⟩ => (by cases h)⟩
    · exact ⟨_, he, .inr ⟨bs, rfl⟩, fun ⟨bs', h⟩ => (by cases h), fun _ => rfl⟩
    · exact (Bool.false_ne_true (kind_compute hpre hX he hσ hI)).elim
  obtain ⟨t, n, hIA, h2, h264, ha, rfl, hrd, hwr⟩ := acc_pos_of hpre hX hσ hI he hk
  have hww : w = isWr (skOf n) := by
    rcases hk with h | h
    · rw [hw.1 h, hrd h]
    · rw [hw.2 h, hwr h]
  obtain ⟨hR, hl, hjk, hcnt⟩ := hIA
  have hn : n < 268 := by omega
  have ht : tid g < 128 := (show Compute.Tile P L g t n s.w s.p s.x from hR.facts).compute
  obtain ⟨c1, c2, c3, c4⟩ := hcov
  obtain ⟨u1, u2, u3, u4⟩ := hin
  simp only [accOf] at c1 c2 c3 c4
  obtain rfl : c = g / L.block := u2.symm.trans c2
  have hsb := hpre.sharedBase
  have hm2 : t % 2 < 2 := Nat.mod_lt _ (by decide)
  have hm3 : t % 3 < 3 := Nat.mod_lt _ (by decide)
  have hb6 : bar0Before X (g, k) = 6 := Compute.Proto.cnt_bar0 hl
  have hthr : g = computeThread L (g / L.block) ⟨tid g, ht⟩ := by
    have h := Protocol.thr_eq hpre.block g
    rw [block_mod hpre] at h
    exact h.symm
  have i1 : Compute.ind 1 n = 1 := ite_eq_left (by omega)
  have i2 : Compute.ind 2 n = 1 := ite_eq_left h2
  have i267 : Compute.ind 267 n = 0 := ite_eq_right (by omega)
  -- the gate of the input stage of the tile
  have gin : arrivals ((Bar.loadEmpty (Compute.stage3 t)).loc L (g / L.block))
      ((X.tr g).take k) + 1 ≤
      okPolls ((Bar.loadFull (Compute.stage3 t)).loc L (g / L.block)) ((X.tr g).take k) := by
    have e1 : arrivals ((Bar.loadEmpty (Compute.stage3 t)).loc L (g / L.block))
        ((X.tr g).take k) = t / 3 :=
      (Compute.Proto.cnt_ae hl (Compute.stage3 t)).trans (Compute.Proto.uses3_self t)
    have e2 : okPolls ((Bar.loadFull (Compute.stage3 t)).loc L (g / L.block))
        ((X.tr g).take k) = t / 3 + 1 := by
      rw [Compute.Proto.cnt_pf hl (Compute.stage3 t), i2]
      exact Compute.Proto.uses3_succ t
    omega
  have hinput : ∀ lo hi : Nat, P.sharedBase + 32768 + 18048 * (t % 3) ≤ lo →
      hi ≤ P.sharedBase + 32768 + 18048 * (t % 3) + 18048 → lo ≤ l.addr → l.addr < hi →
      isWr (skOf n) = false → ThreadClass L X O (g / L.block) g k w l := by
    intro lo hi b1 b2 b3 b4 hwf
    refine .input ⟨tid g, ht⟩ (Compute.stage3 t) hthr (hww.trans hwf) hb6 ⟨u1, u2, ?_, ?_⟩ gin
    · show L.sharedBase + (32768 + 18048 * (t % 3)) ≤ l.addr
      omega
    · show l.addr < L.sharedBase + (32768 + 18048 * (t % 3 + 1))
      omega
  refine ⟨rfl, ?_⟩
  rcases acc_class n hn ha with ⟨hr, hc0, hs16⟩ | ⟨hr, hc0, hs16, hwf⟩ | ⟨hr, hc0, hs16, hwt⟩ |
    ⟨hr, hcc, hs2, hwf⟩ | ⟨hr, hc1, hc2, hc3, hs4, hwf⟩
  · -- a row of the state copy is below the buffer region
    exfalso
    have hb := Compute.acc_addr hpre ht (t := t) hr
    omega
  · -- a row of the input buffer
    have hb := Compute.in_addr hpre ht (t := t) hr
    exact hinput _ _ hb.2.1 hb.2.2 (by omega) (by omega) hwf
  · -- a row of the output buffer: the lane's own
    have hb := Compute.out_addr hpre ht (t := t) hr
    have e1 : arrivals ((Bar.storeFull (Compute.stage2 t)).loc L (g / L.block))
        ((X.tr g).take k) = t / 2 := by
      rw [Compute.Proto.cnt_af hl (Compute.stage2 t), i267]
      exact Compute.Proto.uses2_self t
    have e2 : okPolls ((Bar.storeEmpty (Compute.stage2 t)).loc L (g / L.block))
        ((X.tr g).take k) = t / 2 + 1 := by
      rw [Compute.Proto.cnt_pe hl (Compute.stage2 t), i1]
      exact Compute.Proto.uses2_succ t
    refine .output ⟨tid g, ht⟩ (Compute.stage2 t) hthr (hww.trans hwt) hb6 ⟨u1, u2, ?_, ?_⟩
      (by omega) ?_
    · show L.sharedBase + (86912 + 4096 * (t % 2)) ≤ l.addr
      omega
    · show l.addr < L.sharedBase + (86912 + 4096 * (t % 2 + 1))
      omega
    · rw [hOut]
      exact outOwner_row (t := t) ht hr (by omega) (by omega)
  · -- a gate logit
    rw [hr] at c3 c4
    have hb := Compute.gate_addr hpre ht (t := t) hcc
    exact hinput (regVal P g t 1948 + (addrOf n).2.1) (regVal P g t 1948 + (addrOf n).2.1 + 2)
      (by omega) (by omega) c3 (by omega) hwf
  · -- a decay factor
    rw [hr] at c3 c4
    have hb := Compute.decay_addr hpre ht (t := t) hc1 hc2 hc3
    exact hinput (regVal P g t 2014 + (addrOf n).2.1) (regVal P g t 2014 + (addrOf n).2.1 + 4)
      (by omega) (by omega) c3 (by omega) hwf

/-- The row write of the lane's row of the output buffer that position `m` of tile `t` makes
(`m` is 165 or 167, register `r` is 1672 or 1677), seen from the arrival at position 266 of
the tile: it is `266 - m` events earlier, a write event of the 16 bytes at `regVal P g t r`,
with as many arrivals on `storeFull` of the tile's stage before it as before the arrival. -/
theorem out_write (hg : g < L.threads) {j0 k t : Nat} {s0 s : D}
    (h0 : At (code L) X g j0 s0) (hin : Compute.In P L X g j0 s0) (hσ : At (code L) X g k s)
    (hlt : k < (X.tr g).length) (hIA : InvAt P L X g j0 k (.tile t 266) s) {m r : Nat}
    (hm2 : 2 ≤ m) (hm : m < 264) (ha : addrOf m = (r, 0, 16)) (hw : isWr (skOf m) = true)
    (o : Fin 2) :
    ∃ i pcw bs, i < k ∧ X.get (g, i) =
        some ⟨pcw, .wr { loc := ⟨.shared, g / L.block, regVal P g t r⟩, size := 16 } bs⟩ ∧
      arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take i) =
        arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨hdk, s', hσ', hIA'⟩ :=
    Compute.Proto.back hpre hX hg h0 hin hlt.le hσ hIA (266 - m) (by omega)
  have hpos : 266 - (266 - m) = m := by omega
  rw [hpos] at hIA'
  obtain ⟨e', he'⟩ : ∃ e', (X.tr g)[k - (266 - m)]? = some e' :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hev := Compute.Proto.ev_at hpre hX hIA'.1 hσ' he'
  rw [Compute.Proto.evAt_body hm2 hm] at hev
  have hne : (addrOf m).2.2 ≠ 0 := by
    rw [ha]
    exact Nat.succ_ne_zero 15
  rw [ite_eq_right hne] at hev
  have i1 : Compute.ind 267 m = 0 := ite_eq_right (by omega)
  have i2 : Compute.ind 267 266 = 0 := ite_eq_right (by decide)
  have harr : arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take (k - (266 - m))) =
      arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) := by
    rw [Compute.Proto.cnt_af hIA'.2.1 o, Compute.Proto.cnt_af hIA.2.1 o, i1, i2]
  rcases hev with ⟨bs, -, hf⟩ | ⟨bs, hkd, -⟩
  · rw [hw] at hf
    cases hf
  · obtain ⟨pc', kd'⟩ := e'
    dsimp only at hkd
    subst hkd
    have hacc : accOf P L g t m =
        { loc := ⟨.shared, g / L.block, regVal P g t r⟩, size := 16 } := by
      simp only [accOf, ha, Nat.add_zero]
    rw [hacc] at he'
    exact ⟨k - (266 - m), pc', bs, by omega, he', harr⟩

/-- **`StoreCover.out_cover` for the Compute phase**: at its arrival on `storeFull o` (position
266 of a tile of stage `o`) the thread has written, since its previous arrival on that
mbarrier, every byte of output buffer `o` that it owns: the byte is in one of the lane's two
rows, written at positions 165 and 167 of the same tile. -/
theorem compute_out_cover (hg : g < L.threads) {j0 k pc tx cnt : Nat} {s0 s : D} {rel : Bool}
    {sc : MbarScope} (o : Fin 2) {l : Loc} (h0 : At (code L) X g j0 s0)
    (hin : Compute.In P L X g j0 s0) (hσ : At (code L) X g k s)
    (hI : Compute.Inv P L X g j0 k s)
    (he : X.get (g, k) =
      some ⟨pc, .arrive ((Bar.storeFull o).loc L (g / L.block)) tx cnt rel sc⟩)
    (hl : InOutput L (g / L.block) o.val l) (hown : outOwner P l = g % L.block) :
    ∃ i pcw aw bs, i < k ∧ X.get (g, i) = some ⟨pcw, .wr aw bs⟩ ∧ aw.Covers l ∧
      arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take i) =
        arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) := by
  have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨pos, hR, hled, hjk, hcnt⟩ := hI
  have hev := Compute.Proto.ev_at hpre hX hR hσ he
  cases pos with
  | entry => cases hev
  | tile t n =>
    have hn : n < 268 := hR.facts.pos
    have ht : tid g < 128 := (show Compute.Tile P L g t n s.w s.p s.x from hR.facts).compute
    rcases Compute.Proto.pos_cases hn with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h2, h264⟩
    · obtain ⟨ok, h⟩ := Compute.Proto.evAt_0.mp hev
      cases h
    · obtain ⟨ok, h⟩ := Compute.Proto.evAt_1.mp hev
      cases h
    · cases Compute.Proto.evAt_264.mp hev
    · cases Compute.Proto.evAt_265.mp hev
    · -- the arrival on `storeFull` of the tile's stage
      have h := Compute.Proto.evAt_266.mp hev
      simp only [Event.mk.injEq, Kind.arrive.injEq] at h
      obtain ⟨hbar, -⟩ := Bar.loc_inj h.2.1
      obtain rfl : o = Compute.stage2 t := by
        cases hbar
        rfl
      have hIA : InvAt P L X g j0 k (.tile t 266) s := ⟨hR, hled, hjk, hcnt⟩
      obtain ⟨p1, p2, p3, p4⟩ := out_pos
      have hl' : InOutput L (g / L.block) (t % 2) l := hl
      rcases row_of_owner hpre ht hl' (hown.trans (block_mod hpre)) with ⟨r1, r2⟩ | ⟨r1, r2⟩
      · obtain ⟨i, pcw, bs, hik, hget, harr⟩ := out_write hpre hX hg h0 hin hσ hlt hIA
          (m := 165) (by decide) (by decide) p1 p3 (Compute.stage2 t)
        exact ⟨i, pcw, _, bs, hik, hget, ⟨hl.1, hl.2.1, r1, r2⟩, harr⟩
      · obtain ⟨i, pcw, bs, hik, hget, harr⟩ := out_write hpre hX hg h0 hin hσ hlt hIA
          (m := 167) (by decide) (by decide) p2 p4 (Compute.stage2 t)
        exact ⟨i, pcw, _, bs, hik, hget, ⟨hl.1, hl.2.1, r1, r2⟩, harr⟩
    · -- the arrival of position 267 is on `loadEmpty`
      have h := Compute.Proto.evAt_267.mp hev
      simp only [Event.mk.injEq, Kind.arrive.injEq] at h
      obtain ⟨hbar, -⟩ := Bar.loc_inj h.2.1
      cases hbar
    · rw [Compute.Proto.evAt_body h2 h264] at hev
      split_ifs at hev
      · rcases hev with ⟨op, own, recv, h⟩ | ⟨f, h⟩ <;> cases h
      · rcases hev with ⟨bs, h, -⟩ | ⟨bs, h, -⟩ <;> cases h

/-- **The share of the Compute phase in the buffer contracts**, for every consistent
execution. -/
theorem computeOwes : ComputeOwes P L X where
  thread O hOut _ _ _ hσ hI hacc hcov hin := compute_thread hpre hX O hOut hσ hI hacc hcov hin
  out_cover := fun o => fun hg h0 hin hσ hI he hl hown =>
    compute_out_cover hpre hX hg o h0 hin hσ hI he hl hown
  matrix_len hg h0 hin hσ hI he := compute_matrix_len hpre hX hg h0 hin hσ hI he
  wr_shared _ hσ hI he := compute_wr_shared hpre hX hσ hI he

end

end Buffers

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
