-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmTotV

@[expose] public section

/-! # The default-partition softmax region as a code machine

Warps 0 to 3 (`tid < 128`) walk the online-softmax loop of `_verify_softmax`
(`attention.py:680-806`) between the second `barrier.sync 1` after `setmaxnreg.inc 256`
(pc 574) and the exit to the epilogue (pc 2560). This file is the region's machine: the event
sites in execution order, the abstract state, the register table and the invariant.

Execution order differs from program order: the region's loop body runs the P store and the
`p_ready` arrival of the previous block (pcs 949-1013), packs the bias words loaded last
iteration (pcs 1014-1045), advances the loop variables (pcs 1046-1048), tests the loop counter
(pcs 1049-1050), computes the next block's bias pointers (pcs 1051-1123) and loads that bias
(pcs 1124-1250) before it waits on `s_ready` (pc 1257), reads the S tile (pc 1265), and
returns to the P store through the score, maximum, exponential and sum code (pcs 1302-2236),
the first-iteration test (pc 2237, which skips to the P store when `i = 0`), the wait on `o_done`
(pcs 2238-2240, every iteration `i > 0`), the minimum of `alpha` (pcs 2241-2257) and, unless
that minimum is at least 1 (pc 2258), the O rescale (pcs 2259-2329). The preload of the first
block's bias (pcs 680-806) and the setup code (pcs 576-679 and 807-948) are outside the loop;
the first pass enters the loop at its test (pc 1049).

**State.** A state is the next event, the numbers the prologue left in registers (`Ent`), the
loop counter `i` (`%rd498`; the block of iteration `i` is `split + i * num_splits`), the running
maximum and sum (`m`, `l`: `%r1453`, `%r1454`), the bias words the loads returned (`w` for the
block in the registers, `v` for the block being loaded) and how many words of each group are
loaded (`cw`, `cv`). Every register of the code is a function of the state (`valueOf`), whatever
the site: a register a site does not use yet or any more is dead there.

**The table.** The table is a list of keyed entries looked up by `List.lookup` and is nested to
the right (`a ++ (b ++ (c ++ …))`). Nested to the left, one lookup of a register unfolds the
whole spine of the append once per entry and costs seconds; nested to the right it costs
milliseconds. This is what lets a segment of a hundred instructions with a hundred live
registers pass at the default heartbeats. A family of registers (the 64 bias pointers, the 31
position pairs, the loaded words) is one `List.map` over `List.range`, whose keys and values
the segment evaluator reads one cell at a time.

**Masks.** The bias loads are masked on launch data (`row_valid`, `n_first >= n_bias`,
`num_iters > 0`). A state at a load site has its mask true (`Inv`); where a mask is false the
guarded loads are skipped (local steps) and the registers keep the zero half-words, so the
machine continues at the next event (`afterSetup`). Only a loop test that leaves the region
(`num_iters = 0`) stops the machine's following (`next` returns `some none`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000

/-! ### The invariant -/

/-- The sites of the preload. -/
def PreSite : Site → Prop
  | .pre _ => True
  | _ => False

/-- The sites after the loop's bias loads: from the `s_ready` poll on, the loaded block is in the
registers and the next block's loads are done. -/
def LateSite : Site → Prop
  | .setMaxReg => False
  | .bar0 => False
  | .pre _ => False
  | .nxt _ => False
  | _ => True

/-- The words of the stage that the rescale test shuffles or stores have four bytes: `alpha`, the
running minima `cm1` … `cm4`, the word loaded from shared memory and the minimum `m2`; `alpha`
also reads as the real number the stage records for it (`alr`, which the O rescale multiplies by),
on any words: the stage's `alpha` is `1.0` or the exact `2 ^ alpha_log2` of an `alpha_log2` below
`-8` (`alT_read`). -/
structure Stg.Four (s : Stg) : Prop where
  al : readEReal .f32 s.al = some (.ok (s.alr : EReal))
  cm1 : s.cm1.bytes = 4
  cm2 : s.cm2.bytes = 4
  cm3 : s.cm3.bytes = 4
  cm4 : s.cm4.bytes = 4
  ld : s.ld.bytes = 4
  m2 : s.m2.bytes = 4
  /-- The thread's sum of probabilities, which the exchange of the half sums shuffles. -/
  sw : s.sw.bytes = 4

/-- The registers of the stage hold the real numbers the state records: the word of `alpha`
(`%r46`) reads as `alr` (the O rescale multiplies by it), the running maximum and the new maximum
are score words, and the probability words and their sum's word are the `.f32` values of `pf` and
`sumP`. -/
structure RealSt (s : Stg) (m : Value) (pf : Nat → ℝ) : Prop where
  al : readEReal .f32 s.al = some (.ok (s.alr : EReal))
  m : ScoreWord m
  mn : ScoreWord s.mn
  pv : ∀ k, s.pv k = .float .f32 (pf k)
  sw : s.sw = .float .f32 ((List.range 64).map pf).sum

/-- The invariant of a state. The thread is a softmax thread (index below 128); the entry numbers
satisfy `Ent.Ok`; the loop counter is at most `num_iters`; the counters are the site's index; the
loads of a site are issued; the running maximum and sum of the first iteration are the
registers' initial values. -/
structure Inv (L : Launch) (g : Nat) (d : D) : Prop where
  tid : g % L.block < 128
  ok : d.e.Ok
  i : d.i ≤ d.e.r26
  cwPre : ∀ k, d.site = .pre k → d.cw = k.val ∧ act0 d.e (g % L.block) = true
  cwNxt : ∀ k, d.site = .nxt k → d.cw = 64 ∧ d.cv = k.val ∧
    actB d.e (g % L.block) d.i = true ∧ d.i < d.e.r26
  loop : (∀ k, d.site = .pre k → d.i = 0 ∧ d.cv = 0 ∧ d.m = b32 4286578688 ∧ d.l = b32 0) ∧
    (d.site = .bar0 → d.i = 0 ∧ d.m = b32 4286578688 ∧ d.l = b32 0 ∧ d.cw = 0 ∧ d.cv = 0)
  /-- The words the loads returned are half-words (`.bytes = 2`). -/
  wb : ∀ k, (d.w k).bytes = 2
  vb : ∀ k, (d.v k).bytes = 2
  /-- The first state: no iteration, no word loaded, the running maximum and sum at their start. -/
  start : d.site = .setMaxReg →
    d.i = 0 ∧ d.m = b32 4286578688 ∧ d.l = b32 0 ∧ d.cw = 0 ∧ d.cv = 0
  /-- From the `s_ready` poll on: both blocks' words are loaded and the loop has an iteration
  left. -/
  late : LateSite d.site → d.cw = 64 ∧ d.cv = 64 ∧ d.i < d.e.r26
  /-- The thread that arrives on `p_ready` is thread 0 (the guard `%p177` is `tid % 128 = 0`). -/
  lead : d.site = .arrive → g % L.block = 0
  /-- Where the stage's numbers are the real ones (`Stg.re`): `alpha`, the running maximum, the new
  maximum and the probability words are those numbers (`RealSt`). -/
  re : d.stg.re = true → RealSt d.stg d.m d.pf
  /-- The running sum is a word of four bytes (the bridge reads it at the loop's exit). -/
  lb : d.l.bytes = 4
  /-- The stage's shuffled and stored words have four bytes (`shfl.sync.b32`, `st.shared.b32`). -/
  four : d.stg.Four
  /-- The recorded lane bits are 0 or the warp index: the Tensor Memory accesses accept no others
  (`next` kills the thread at the broadcast). -/
  bw : d.stg.bw = 0 ∨ d.stg.bw = g % L.block / 32
  /-- The bias words are `bf16` numbers or the zero half-word: the loads follow only `bf16`
  words, and the masked loads leave the zero half-word. -/
  wf : ∀ k, BfOk (d.w k)
  vf : ∀ k, BfOk (d.v k)

/-! ### Transitions -/

/-- The new word record after a load of word `k`. -/
def setW (w : Nat → Value) (k : Nat) (x : Value) : Nat → Value := Function.update w k x

/-- A bias word the machine follows: a `bf16` number. -/
def isBf16 : Value → Bool
  | .float .bf16 _ => true
  | _ => false

/-- After the setup that follows the first block's bias (pcs 807-1123): the loop test leaves
the region where the split has no block (`num_iters = i`, the machine stops following); where the
next block's loads are issued the machine is at the first of them, and where they are not the
loads are skipped and the machine is at the `s_ready` poll with the zero words. -/
def afterSetup (L : Launch) (g : Nat) (d : D) : Option (Option D) :=
  if d.e.r26 = d.i then some none
  else if actB d.e (g % L.block) d.i then some (some { d with site := .nxt 0 })
  else some (some { d with site := .waitS, cv := 64, v := fun _ => z16 })

/-- After the P store's arrival (or where its guard is false): the packs of the next block's bias
(`v` becomes `w`), the loop variables, the loop test and the next block's pointers, as after the
first block's setup: the end of the loop leaves the region, the next block's loads are issued or,
where masked, skipped. -/
def afterArrive (L : Launch) (g : Nat) (d : D) : Option (Option D) :=
  afterSetup L g { d with i := d.i + 1, w := d.v, cw := 64, cv := 0 }

/-- The 64 words of the S tile a load returned, as the table's words: `vals` at its positions. -/
def svOf (vals : List Value) (h : ∀ x ∈ vals, x.bytes = 4) : Nat → { v : Value // v.bytes = 4 } :=
  fun k => if hk : k < vals.length then ⟨vals[k], h _ (List.getElem_mem hk)⟩ else ⟨b32 0, rfl⟩

/-- The 64 words a load returned, as the record of the words of `O`: `vals` at its positions. -/
def owOf (vals : List Value) : Nat → Value := fun k => vals.getD k (b32 0)

/-- The 64 products of the O rescale have outcomes (`mul.f32` faults where `alpha` or a word is no
`f32` datum). -/
def D.owOk (d : D) : Prop := ∀ k < 64, (mulE false d.stg.al (d.stg.ow k)).toBool = true

/-! ### The edges into the P store

The loop's tail updates the running maximum and sum (pc 949, `selp.f32 %r1453, %r1453, %r1061,
%p168`, and pc 950, `fma.rn.f32 %r1454, %r1454, %r46, %r1070`) before the P store. It is reached
from three places: the first-iteration test (the branch at pc 2237, taken when `%p169`), the
rescale test (the branch at pc 2258, taken when `%p170`) and the end of the O rescale
(`bra.uni` at pc 2330). The step of pcs 949-950 reads the running maximum and sum, the
numbers of the score stage (`D.stg`) and writes the new running maximum and sum. -/

/-- The new running maximum (`%r1453`): the old one where the rescale is lazy (`%p168`), else the
new maximum `%r1061`. -/
def D.mNew (d : D) : Value := if d.stg.kp then d.m else d.stg.mn

/-- The outcome of `fma.rn.f32 %r1454, %r1454, %r46, %r1070`: the new running sum. -/
def D.lOut (d : D) : Exec Value := floatE (fmaI .rn false) [d.l, d.stg.al, d.stg.rs]

/-- Pcs 949-998 do not fault: the selected maximum is a word of four bytes, the fma has an
outcome and so have the 24 unpacks and conversions of the P store's packed pairs (`D.pqOk`). -/
def D.updOk (d : D) : Bool := decide (d.mNew.bytes = 4) && d.lOut.toBool && decide d.pqOk

/-- The state after pcs 949-950: the new running maximum and sum. -/
def D.upd (d : D) : D := { d with m := d.mNew, l := okVal (b32 0) d.lOut }

/-- The edge into the P store: the new running maximum and sum, and the barrier before the P
store; the thread faults where pcs 949-950 do. -/
def toBar20 (d : D) : Option (Option D) :=
  if d.updOk then some (some { d.upd with site := .bar20 }) else none

/-- The outcome of `add.f32 %r1070, %r1068, %r1069` (pc 2235): the thread's sum of probabilities
plus the word the exchange returned, any word (`add` without a rounding modifier faults where the
ideal rule declines: a NaN, `+inf - inf`, or a word that is no `.f32` datum). -/
def D.rsOut (d : D) (recv : Value) : Exec Value := floatE (addI false) [d.stg.sw, recv]

/-- `%p170 = (min(%r1083, %r1084) >= 1.0)` (pcs 2256-2257, unordered `geu`), for the value
`recv` the last exchange returned (`%r1084`). -/
def D.p170 (d : D) (recv : Value) : Exec Bool :=
  (minE [d.stg.m2, recv]).bind fun r => setpE (.unord .ge) false r (b32 1065353216)

/-- The abstract successor after event `e`. A loaded bias word that is no `bf16` number stops the
machine's following (`some none`); an unreadable word is a fault (`none`). Every word the broadcast
of the warp index returns is followed: the lane bits are recorded (`Stg.bw`) where the Tensor
Memory accesses accept them (`Raw.laneOk`); otherwise the shift faults (a word without bits) or the
S load is undefined behaviour (its lane field leaves the warp's lanes), and the thread is dead
(`none`). The words of the S load
are followed whatever they are; the thread is dead (`none`) where one is not four bytes (the pack
that reads it, pcs 1266 to 1297, throws: `step_ldS`), and after the wait for the load where an
instruction of the score stage's first half faults (`D.s1Ok`). The word the exchange of the row
maximum returns is followed whatever it is: where it, the running maximum and the 64 words of the
columns are score words the successor holds the real numbers (`D.afterMax`), otherwise Core's
outcomes (`D.afterMaxT`, the flag `Stg.re` cleared), and the thread is dead (`none`) where an
instruction of the stage's second half faults (`D.s2Ok`). The words of the O rescale's load are
followed whatever they are; the thread is dead (`none`) where a product by `alpha` faults
(`D.owOk`). The word the exchange of the half sums returns is followed whatever it is; the thread
is dead (`none`) where the row sum's `add` faults (`D.rsOut`). -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .setMaxReg => some (some { d with site := .bar0 })
  | .bar0 =>
    if act0 d.e (g % L.block) then some (some { d with site := .pre 0 })
    else afterSetup L g { d with cw := 64, w := fun _ => z16 }
  | .pre j =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok x =>
        if isBf16 x then
          if h : j.val + 1 < 64 then
            some (some { d with
              site := .pre ⟨j.val + 1, h⟩
              cw := j.val + 1
              w := setW d.w j.val x })
          else afterSetup L g { d with cw := 64, w := setW d.w j.val x }
        else some none
      | .error _ => none
    | _ => none
  | .nxt j =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok x =>
        if isBf16 x then
          if h : j.val + 1 < 64 then
            some (some { d with
              site := .nxt ⟨j.val + 1, h⟩
              cv := j.val + 1
              v := setW d.v j.val x })
          else some (some { d with site := .waitS, cv := 64, v := setW d.v j.val x })
        else some none
      | .error _ => none
    | _ => none
  | .waitS =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .shfl4 } else d))
    | _ => none
  | .shfl4 =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      match Raw.laneOk (g % L.block / 32) v with
      | some b => some (some { d with site := .ldS, stg := { d.stg with bw := b } })
      | none => none
    | _ => none
  | .ldS =>
    match e.kind with
    | .tc (.ld _ vals _) =>
      if h : vals.length = 64 ∧ ∀ x ∈ vals, x.bytes = 4 then
        some (some { d with site := .waitLd, sv := svOf vals h.2 })
      else none
    | _ => none
  | .waitLd =>
    if D.s1Ok L g d then
      some (some { d with site := .shfl5, stg := { d.stg with fsv := D.finT L g d } })
    else none
  | .shfl5 =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      if d.RealIn recv then some (some (d.afterMax recv))
      else if d.s2Ok L g recv then some (some (d.afterMaxT L g recv)) else none
    | _ => none
  | .shfl6 =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      match D.rsOut d recv with
      | .ok v =>
        if d.i = 0 then toBar20 (d.afterSum v) else some (some (d.afterSum v))
      | .error _ => none
    | _ => none
  | .bar22 => some (some { d with site := .shfl7 })
  | .shfl7 =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      match minE [d.stg.al, recv] with
      | .ok v => some (some { d with site := .shfl8, stg := { d.stg with cm1 := v } })
      | .error _ => none
    | _ => none
  | .shfl8 =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      match minE [d.stg.cm1, recv] with
      | .ok v => some (some { d with site := .shfl9, stg := { d.stg with cm2 := v } })
      | .error _ => none
    | _ => none
  | .shfl9 =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      match minE [d.stg.cm2, recv] with
      | .ok v => some (some { d with site := .shfl10, stg := { d.stg with cm3 := v } })
      | .error _ => none
    | _ => none
  | .shfl10 =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      match minE [d.stg.cm3, recv] with
      | .ok v => some (some { d with site := .store10, stg := { d.stg with cm4 := v } })
      | .error _ => none
    | _ => none
  | .store10 => some (some { d with site := .bar23 })
  | .bar23 => some (some { d with site := .ldL })
  | .ldL =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok x => some (some { d with site := .shfl11, stg := { d.stg with ld := x } })
      | .error _ => none
    | _ => none
  | .shfl11 =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      match minE [d.stg.ld, recv] with
      | .ok v => some (some { d with site := .shfl12, stg := { d.stg with m2 := v } })
      | .error _ => none
    | _ => none
  | .shfl12 =>
    match e.kind with
    | .shfl _ _ _ _ recv _ =>
      match d.p170 recv with
      | .ok p170 =>
        if p170 then toBar20 d else some (some { d with site := .ldO })
      | .error _ => none
    | _ => none
  | .waitO =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then { d with site := .bar22 } else d))
    | _ => none
  | .ldO =>
    match e.kind with
    | .tc (.ld _ vals _) =>
      some (some { d with site := .waitLdO, stg := { d.stg with ow := owOf vals } })
    | _ => none
  | .waitLdO => if d.owOk then some (some { d with site := .bar24 }) else none
  | .bar24 => some (some { d with site := .stO })
  | .stO =>
    match e.kind with
    | .tc (.st _ _ _) => some (some { d with site := .waitStO })
    | _ => none
  | .waitStO => toBar20 d
  | .bar20 => if d.psOk then some (some { d with site := .tmemSt }) else none
  | .tmemSt =>
    match e.kind with
    | .tc (.st _ _ _) => some (some { d with site := .tmemWait })
    | _ => none
  | .tmemWait => some (some { d with site := .bar21 })
  | .bar21 =>
    if g % L.block = 0 then some (some { d with site := .arrive }) else afterArrive L g d
  | .arrive =>
    match e.kind with
    | .arrive _ _ _ _ _ => afterArrive L g d
    | _ => none

/-! ### The P store's words on numbers -/

/-- Where the probability words are the `.f32` numbers `f`, the stored word `w` is the pair of the
two numbers as `bf16` payloads. -/
theorem pwE_float {d : D} {f : Nat → ℝ} (h : ∀ k, d.stg.pv k = .float .f32 (f k)) (w : Nat) :
    d.pwE w = .ok (.pair (.float .bf16 (f (2 * w))) (.float .bf16 (f (2 * w + 1)))) := by
  unfold D.pwE
  rw [h, h]
  split_ifs
  · simp [joinValue, unpackE, splitValue, Value.bytes, FloatFmt.bytes, Except.bind,
      cvtBfE_float]
  · exact cvtBfE_float _ _

theorem pqOk_float {d : D} {f : Nat → ℝ} (h : ∀ k, d.stg.pv k = .float .f32 (f k)) : d.pqOk :=
  fun q _ => by rw [pwE_float h]; rfl

theorem psOk_float {d : D} {f : Nat → ℝ} (h : ∀ k, d.stg.pv k = .float .f32 (f k)) : d.psOk :=
  fun j _ => by rw [pwE_float h]; rfl

/-- A stored word has four bytes. -/
theorem pwV_bytes (d : D) (w : Nat) : (d.pwV w).bytes = 4 := by
  unfold D.pwV
  rcases h : d.pwE w with f | v
  · rfl
  · show v.bytes = 4
    unfold D.pwE at h
    split_ifs at h
    · rcases hu : unpackE 64 (joinValue (d.stg.pv (2 * w)) (d.stg.pv (2 * w + 1))) with f | p
      · rw [hu] at h; cases h
      · rw [hu] at h
        exact cvtBfE_four h
    · exact cvtBfE_four h

/-- The stored word of a state whose probability words are the `.f32` values of `pf`. -/
theorem pwV_real {d : D} (h : ∀ k, d.stg.pv k = .float .f32 (d.pf k)) (w : Nat) :
    d.pwV w = d.pw w := by
  unfold D.pwV
  rw [pwE_float h]
  rfl

/-- The softmax region as a code machine from the state `d0`. -/
@[reducible] def code (A : List Assumption) (L : Launch) (g : Nat) (d0 : D) :
    Flow.Code kernel A L g where
  D := D
  init := d0
  pc := (·.site.pc)
  facts := facts L g
  inv := Inv L g
  next := next L g

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
