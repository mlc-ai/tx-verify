-- SPDX-License-Identifier: Apache-2.0
-- iface: W0Words producer=W1 status=stated domain=consistent
-- iface: W0Valid producer=W1 status=stated domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
public import Lemmas.Flow.OutKinds
public import Lemmas.Flow.OutFloatItems
public import Kernels.FlashMlaSparseDecodeH64.Assumptions

@[expose] public section

/-! # Warpgroup 0's loop reads: the words a block's loads read

The vocabulary of the softmax value export (`Wg0/Export/Value.lean`). A lane's trace is cut into
blocks at its events at pc 1122 (the softmax-ready arrival, `w0ArrSPc`): `w0Scan l` is the list
of the finished blocks' events and the events of the block in progress. The words a block's loads
read ("reads as"): the low and high halves of the score words (the last Tensor Memory loads at pcs
280, 283 and 278, 285), the valid-mask word (pc 289), the sixteen peer elements (two reads at pc
`477 + 5 k`, the peer pair `k`), the peer's row maximum (pc 572) and the vote's result (pc 578),
each taken from the last load of its pcs in the block (`w0Words`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The pc of the softmax-ready arrival that closes a block. -/
def w0ArrSPc : Nat := 1122

/-- The finished blocks' events and the events of the block in progress. -/
def w0Scan (l : List Event) : List (List Event) × List Event :=
  l.foldl (fun s e => if e.pc = w0ArrSPc then (s.1 ++ [s.2], []) else (s.1, s.2 ++ [e])) ([], [])

/-- The words of a tensor load event (none for another event). -/
def w0TcVals (e : Event) : Option (List Value) :=
  match e.kind with
  | .tc (.ld _ vals _) => some vals
  | _ => none

/-- The value a generic read event delivers (none for another event). -/
def w0RdVal (e : Event) : Option Value :=
  match e.kind with
  | .rd _ bs => some ((rebuild 3 bs).toOption.getD (.pred false))
  | _ => none

/-- The first element of a peer pair, as the control machine keeps it. -/
def w0A0 (e : Event) : Value :=
  match e.kind with
  | .rd _ bs => (rebuild 3 bs).toOption.getD (.bits 64 0)
  | _ => .bits 64 0

/-- The result of a vote event. -/
def w0VoteOf (e : Event) : Option Bool :=
  match e.kind with
  | .voteMode _ _ _ r => some r
  | _ => none

/-- The last event of a block at one of the pcs that satisfies a reading `f`. -/
def w0Last {α : Type} (f : Event → Option α) (pcs : List Nat) (seg : List Event) : Option α :=
  (seg.filterMap fun e => if e.pc ∈ pcs then f e else none).getLast?

/-- The pairs of peer reads of one pc: the reads in pairs, the first element's raw value and the
second's. -/
def w0Peer (seg : List Event) (k : Nat) : Value × Value :=
  match lastN 2 ((seg.filter fun e => e.pc = 477 + 5 * k && (w0RdVal e).isSome).take
      (2 * ((seg.filter fun e => e.pc = 477 + 5 * k && (w0RdVal e).isSome).length / 2))) with
  | [e0, e1] => (w0A0 e0, (w0RdVal e1).getD (.pred false))
  | _ => (.pred false, .pred false)

/-- The words one block's loads read. -/
structure W0Words where
  lo : List Value
  hi : List Value
  mw : Value
  pw : Nat → Value × Value
  pm : Value
  vt : Bool

/-- **The words a block's loads read**, from the block's events. -/
def w0Words (seg : List Event) : W0Words where
  lo := (w0Last w0TcVals [280, 283] seg).getD []
  hi := (w0Last w0TcVals [278, 285] seg).getD []
  mw := (w0Last w0RdVal [289] seg).getD (.pred false)
  pw := fun k => if k < 8 then w0Peer seg k else (.pred false, .pred false)
  pm := (w0Last w0RdVal [572] seg).getD (.pred false)
  vt := (w0Last w0VoteOf [578] seg).getD false

/-! ### Valid data and the reference -/

/-- A value that reads as a finite `f32`. -/
def W0Fin (v : Value) : Prop := ∃ x : ℝ, valFloat .f32 v = .ok x

/-- The `f32` bits of negative infinity. -/
def w0NegInf : Value := .bits 32 (BitVec.ofNat 64 4286578688)

/-- The number a value reads as (`0` if it reads as none). -/
def w0F (v : Value) : ℝ := ((valFloat .f32 v).toOption).getD 0

/-- The extended number a value reads as: negative infinity for its bits. -/
def w0FE (v : Value) : EReal := if v = w0NegInf then ⊥ else (w0F v : EReal)

/-- Bit `i` of a mask word read. -/
def w0Bit (v : Value) (i : Nat) : Bool :=
  match v with
  | .bits 32 x => x.toNat.testBit i
  | _ => false

/-- Word `j` of the block's peer reads: the half (`j % 2`) of element `(j / 2) % 2` of pair
`j / 4`. -/
def w0PeerF (w : W0Words) (j : Nat) : ℝ :=
  let p := w.pw (j / 4)
  let v := if (j / 2) % 2 = 0 then p.1 else p.2
  w0F (if j % 2 = 0 then (splitValue 64 v).1 else (splitValue 64 v).2)

/-- **The score of column `i`** of a block: the high half's word if the mask selects the column,
plus the peer's word; negative infinity if the mask drops it. -/
def w0Score (w : W0Words) (i : Nat) : EReal :=
  if w0Bit w.mw i then ((w0F (w.hi.getD i (.pred false)) + w0PeerF w i : ℝ) : EReal) else ⊥

/-- The probability of column `i` (with the scale `sc` and the maximum `m`): `2 ^ (sc s - m)`;
zero for a dropped column. -/
def w0Prob (sc m : ℝ) (s : EReal) : ℝ := if s = ⊥ then 0 else (2 : ℝ) ^ (sc * s.toReal - m)

/-- The lane's own row maximum of a block, scaled (the code's `max` fold and `mul.ftz`). -/
def w0Loc (sc : ℝ) (w : W0Words) : EReal := (sc : EReal) * (Finset.range 32).sup (w0Score w)

/-- **The maximum after a block** from the carried one `m`: the code rescales lazily, the maximum
moves (to the larger of the lane's, the peer's and the carried one) only if the warp's vote saw
a rise above 6 (`vt`). -/
def w0Max (sc m : ℝ) (w : W0Words) : ℝ :=
  if w.vt then (max (max (w0Loc sc w) (w0FE w.pm)) (m : EReal)).toReal else m

/-- **The carried statistics after a block**: the maximum (`w0Max`) and the lane's partial row
sum, `l * 2 ^ (m - m') + Σ_i P_i`. -/
def w0Next (sc : ℝ) (ml : ℝ × ℝ) (w : W0Words) : ℝ × ℝ :=
  (w0Max sc ml.1 w, ml.2 * (2 : ℝ) ^ (ml.1 - w0Max sc ml.1 w) +
    ∑ i ∈ Finset.range 32, w0Prob sc (w0Max sc ml.1 w) (w0Score w i))

/-! ### The words of a valid block -/

/-- A peer pair of elements whose four half words each read as a finite number. -/
def W0PeerOk (p : Value × Value) : Prop :=
  W0Fin (splitValue 64 p.1).1 ∧ W0Fin (splitValue 64 p.1).2 ∧ W0Fin (splitValue 64 p.2).1 ∧
    W0Fin (splitValue 64 p.2).2

/-- **The words of a valid block** (valid rows) with the positive scale `sc`: the high score
words are 32 clean words that read as finite numbers, the mask word is a 32-bit word, the
peer elements read as finite numbers, and the peer's row maximum is a clean word that reads as
a finite number or is the pattern of negative infinity. -/
structure W0Ok (sc : ℝ) (w : W0Words) : Prop where
  scale : 0 < sc
  hiLen : w.hi.length = 32
  hi : ∀ c < 32, PTX.Flow.Clean (w.hi.getD c (.pred false)) ∧ W0Fin (w.hi.getD c (.pred false))
  loLen : w.lo.length = 32
  lo : ∀ c < 32, Kernels.FlashMlaSparseDecodeH64.Assumptions.scoreHalf
    (w.lo.getD c (.pred false))
  mask : ∃ n < 2 ^ 32, w.mw = .bits 32 (BitVec.ofNat 64 n)
  peer : ∀ k < 8, W0PeerOk (w.pw k)
  pm : PTX.Flow.Clean w.pm ∧ (W0Fin w.pm ∨ w.pm = w0NegInf)

/-! ### The statistics a block starts from and the valid trace -/

theorem w0Scan_snoc (l : List Event) (e : Event) :
    w0Scan (l ++ [e]) = if e.pc = w0ArrSPc then ((w0Scan l).1 ++ [(w0Scan l).2], [])
      else ((w0Scan l).1, (w0Scan l).2 ++ [e]) := by
  unfold w0Scan; rw [List.foldl_append]; rfl

/-- The pc of the arrival that ends the set-up (`arrL`): the loop's statistics start here. -/
def w0ArrLPc : Nat := 200

/-- The finished blocks since the lane's last arrival at pc `w0ArrLPc` (the statistics restart
there) and the events of the block in progress. -/
def w0Fin (l : List Event) : List (List Event) × List Event :=
  l.foldl (fun s e =>
    if e.pc = w0ArrSPc then (s.1 ++ [s.2], [])
    else if e.pc = w0ArrLPc then ([], s.2 ++ [e]) else (s.1, s.2 ++ [e])) ([], [])

theorem w0Fin_snoc (l : List Event) (e : Event) :
    w0Fin (l ++ [e]) =
      if e.pc = w0ArrSPc then ((w0Fin l).1 ++ [(w0Fin l).2], [])
      else if e.pc = w0ArrLPc then ([], (w0Fin l).2 ++ [e])
      else ((w0Fin l).1, (w0Fin l).2 ++ [e]) := by
  unfold w0Fin; rw [List.foldl_append]; rfl

theorem w0Fin_snd (l : List Event) : (w0Fin l).2 = (w0Scan l).2 := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    rw [w0Fin_snoc, w0Scan_snoc]
    by_cases h1 : e.pc = w0ArrSPc
    · simp [h1]
    · have hne : ¬ (w0ArrLPc = w0ArrSPc) := by unfold w0ArrLPc w0ArrSPc; decide
      by_cases h2 : e.pc = w0ArrLPc <;> simp [h1, h2, ih, hne]

/-- The initial maximum (`-1e30`, the pattern `0fF149F2CA`) as a number. -/
def w0M0 : ℝ := w0F (.bits 32 (BitVec.ofNat 64 4048155338))

/-- **The statistics after finished blocks `bs`**: the blocks fold `w0Next` from the initial
maximum and the empty sum. -/
def w0Carry (sc : ℝ) (bs : List (List Event)) : ℝ × ℝ :=
  bs.foldl (fun ml seg => w0Next sc ml (w0Words seg)) (w0M0, 0)

theorem w0Carry_snoc (sc : ℝ) (bs : List (List Event)) (seg : List Event) :
    w0Carry sc (bs ++ [seg]) = w0Next sc (w0Carry sc bs) (w0Words seg) := by
  unfold w0Carry; rw [List.foldl_append]; rfl

/-- **The true running maximum after finished blocks `bs`** (scaled, `-inf` before the first): the
code's `mx` takes the larger of the lane's own maximum and the peer's word of every block. -/
def w0MxCarry (sc : ℝ) (bs : List (List Event)) : EReal :=
  bs.foldl (fun r seg => max r (max (w0Loc sc (w0Words seg)) (w0FE (w0Words seg).pm))) ⊥

theorem w0MxCarry_snoc (sc : ℝ) (bs : List (List Event)) (seg : List Event) :
    w0MxCarry sc (bs ++ [seg]) =
      max (w0MxCarry sc bs) (max (w0Loc sc (w0Words seg)) (w0FE (w0Words seg).pm)) := by
  unfold w0MxCarry; rw [List.foldl_append]; rfl

/-- The words of the blocks of a trace are valid at the trace's end: those of every finished
block since the arrival at pc `w0ArrLPc`, and those of the block in progress once it has voted
(pc 578). -/
def W0Now (sc : ℝ) (l : List Event) : Prop :=
  (∀ seg ∈ (w0Fin l).1, W0Ok sc (w0Words seg)) ∧
    ((∃ e ∈ (w0Fin l).2, e.pc = 578) → W0Ok sc (w0Words (w0Fin l).2))

/-- The words a block in progress has read so far are those of a valid block: some valid block
`w'` has the same low half, high half, mask word, peer pairs and exchange word wherever the
block in progress has read them (the others still have their defaults). It is what the runs
before the vote need: their words are not yet `W0Ok`. -/
def W0Early (sc : ℝ) (l : List Event) : Prop :=
  (w0Fin l).2 = [] ∨ ∃ w' : W0Words, W0Ok sc w' ∧
    ((w0Words (w0Fin l).2).lo = [] ∨ (w0Words (w0Fin l).2).lo = w'.lo) ∧
    ((w0Words (w0Fin l).2).hi = [] ∨ (w0Words (w0Fin l).2).hi = w'.hi) ∧
    ((w0Words (w0Fin l).2).mw = .pred false ∨ (w0Words (w0Fin l).2).mw = w'.mw) ∧
    (∀ k < 8, (w0Words (w0Fin l).2).pw k = (.pred false, .pred false) ∨
      (w0Words (w0Fin l).2).pw k = w'.pw k) ∧
    ((w0Words (w0Fin l).2).pm = .pred false ∨ (w0Words (w0Fin l).2).pm = w'.pm)

/-! ### Words read as extended reals -/

/-- A clean word that reads as `x`, a real or `-inf`. -/
def Rd (v : Value) (x : EReal) : Prop :=
  PTX.Flow.Clean v ∧ PTX.Assumption.readEReal .f32 v = some (.ok x) ∧ PTX.Flow.SK.ni.Lane x

theorem rd_lane {v : Value} {x : EReal} (h : Rd v x) : PTX.Flow.SK.ni.Lane x := h.2.2

theorem rd_read {v : Value} {x : EReal} (h : Rd v x) :
    PTX.Assumption.readEReal .f32 v = some (.ok x) := h.2.1

theorem rd_unique {v : Value} {x y : EReal} (hx : Rd v x) (hy : Rd v y) : x = y := by
  have h := hx.2.1.symm.trans hy.2.1
  simpa using h

/-! ### The epilogue's words -/

/-- The pcs of the loads of the accumulator words. -/
def w0OPcs : List Nat := [716, 817, 918, 1019, 1201, 1361, 1519, 1676]

/-- The peer's row-sum word a block read (the last read at pc 1157). -/
def w0EpiPe (seg : List Event) : Value := (w0Last w0RdVal [1157] seg).getD (.pred false)

/-- The accumulator words a block read (the last load at the pcs of `w0OPcs`). -/
def w0EpiO (seg : List Event) : List Value := (w0Last w0TcVals w0OPcs seg).getD []

/-- The sink word an event leaves: `-inf` at the `setmaxnreg`, the sink load's word at pc 156
scaled by the multiplier `0x3FB8AA3B` (register 932, immediate 1069066811). -/
def w0SkOf (e : Event) : Option Value :=
  if e.pc = 103 then some (.bits 32 (BitVec.ofNat 64 4286578688))
  else if e.pc = 156 then
    match e.kind with
    | .nc _ bs => some (okVal (.bits 32 0)
        (fF (mulL true) [.reg 932, .f32imm 1069066811]
          [(rebuild 3 bs).toOption.getD (.pred false)]))
    | _ => none
  else none

/-- The sink word after the events `l`. -/
def w0SkWord (l : List Event) : Value :=
  (l.filterMap w0SkOf).getLast?.getD (.bits 32 (BitVec.ofNat 64 4286578688))

/-- The word the sink load at pc 156 returns, unscaled. -/
def w0SkRawOf (e : Event) : Option Value :=
  if e.pc = 156 then
    match e.kind with
    | .nc _ bs => some ((rebuild 3 bs).toOption.getD (.pred false))
    | _ => none
  else none

/-- The raw sink word after the events `l`: the last sink load's word, if there was one. -/
def w0SkRaw (l : List Event) : Option Value := (l.filterMap w0SkRawOf).getLast?

/-- **The words the epilogue reads are valid** at the end of the events `l`: the sink word is
`-inf` or reads as a number, the peer's row-sum word of the block in progress is unread or reads as
a non-negative number (zero for a row without a kept column), the accumulator words of its
last output load are unread or are 64 words that read as numbers, and the raw word of the sink load
(pc 156, before the scaling) reads as a number (the sink input is a real float). -/
def W0EpiOk (sc : ℝ) (l : List Event) : Prop :=
  (w0SkWord l = w0NegInf ∨ ∃ sk, Rd (w0SkWord l) sk) ∧
    (w0EpiPe (w0Scan l).2 = .pred false ∨ ∃ p : ℝ, 0 ≤ p ∧ Rd (w0EpiPe (w0Scan l).2) p ∧
      (w0MxCarry sc (w0Fin l).1 = ⊥ → p = 0)) ∧
    (w0EpiO (w0Scan l).2 = [] ∨ ((w0EpiO (w0Scan l).2).length = 64 ∧
      ∃ O : Nat → ℝ, ∀ i < 64, Rd ((w0EpiO (w0Scan l).2).getD i (.pred false)) (O i))) ∧
    (∀ v, w0SkRaw l = some v → ∃ x, Rd v x)

/-- **A valid trace** (valid rows, the guard itself) with the positive scale `sc`: the words are
valid at the end of every prefix, and the words of the block in progress are those of a valid
block (`W0Early`), and the epilogue's words are valid (`W0EpiOk`). -/
def W0Valid (sc : ℝ) (l : List Event) : Prop :=
  (∀ j ≤ l.length, W0Now sc (l.take j)) ∧ (∀ j ≤ l.length, W0Early sc (l.take j)) ∧
    ∀ j ≤ l.length, W0EpiOk sc (l.take j)

theorem W0Valid.take {sc : ℝ} {l : List Event} (h : W0Valid sc l) {j : Nat} :
    W0Valid sc (l.take j) :=
  ⟨fun i hi => by
    rw [List.take_take]
    exact h.1 (min i j) (by simp at hi; omega),
   fun i hi => by
    rw [List.take_take]
    exact h.2.1 (min i j) (by simp at hi; omega),
   fun i hi => by
    rw [List.take_take]
    exact h.2.2 (min i j) (by simp at hi; omega)⟩

theorem W0Valid.now {sc : ℝ} {l : List Event} (h : W0Valid sc l) : W0Now sc l := by
  simpa using h.1 l.length le_rfl

theorem W0Valid.early {sc : ℝ} {l : List Event} (h : W0Valid sc l) : W0Early sc l := by
  simpa using h.2.1 l.length le_rfl

theorem W0Valid.epi {sc : ℝ} {l : List Event} (h : W0Valid sc l) : W0EpiOk sc l := by
  simpa using h.2.2 l.length le_rfl

/-- **The probability of column `i`** a lane stores in its block in progress after the events `l`:
`2 ^ (sc s_i - m')` with the new maximum `m'` of the block (`w0Max`) from the statistics after the
blocks finished since the arrival at pc `w0ArrLPc` (`w0Carry`). -/
def w0PWord (sc : ℝ) (l : List Event) (i : Nat) : ℝ :=
  w0Prob sc (w0Max sc (w0Carry sc (w0Fin l).1).1 (w0Words (w0Fin l).2))
    (w0Score (w0Words (w0Fin l).2) i)

/-- The sum the epilogue starts from: zero for a row without a kept column, else the carried one. -/
def w0ESum (r : EReal) (l : ℝ) : ℝ := if r = ⊥ then 0 else l

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
