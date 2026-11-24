-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles

@[expose] public section

/-! # The phases of the time table

The bases of the phases of a CTA's timeline (`Progress/Time.lean` describes it), the pipeline's
clock, the collective count of a ledger, and the order of the times of two phases. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The phases -/

/-- The largest K length of a request of the batch. -/
def kMax (p : Params) : Nat := (Finset.range p.batch).sup p.kLength

/-- A bound on the K/V blocks of every tile. -/
def bmax (p : Params) : Nat := kMax p / 128 + 1

/-- A bound on the warp collectives a first scan makes (seven shuffles per round, at most
`batch + 2` rounds, the startup's three shuffles and the choice's ballot and shuffles). -/
def cmax (p : Params) : Nat := 7 * (p.batch + 3) + 6

/-- The width of a pipeline slot. -/
def span : Nat := 4096

/-- The first scan's base, above every startup time. -/
def scanBase : Nat := 256

/-- The prime region's base, above every first-scan time. -/
def primeBase (p : Params) : Nat := scanBase + 2 * cmax p + 4

/-- The pipeline's base, after the prime region. -/
def pipeBase (p : Params) : Nat := primeBase p + 1024

/-- Offset `o` of pipeline slot `s`. -/
def clk (p : Params) (s o : Nat) : Nat := pipeBase p + span * s + o

/-- A slot read off a ghost count, clamped to the last slot before the tail. -/
def slotOf (p : Params) (s : Nat) : Nat := min s (bmax p)

/-! ### The bands of a slot -/

/-- Softmax stage `st`'s score part (stage 1's opens with its closing poll of the round
before). -/
abbrev bandS (st : Nat) : Nat := 1024 + 512 * st
/-- The correction's part of stage `st`. -/
abbrev bandC (st : Nat) : Nat := 1280 + 512 * st
/-- Softmax stage `st`'s P part. -/
abbrev bandP (st : Nat) : Nat := 2048 + 256 * st
/-- The loader's band: TMA group 6, the K packet, TMA groups 4 and 5, the V packet. -/
abbrev bandL : Nat := 3072

/-- The tail, after every slot of every tile. -/
def tailBase (p : Params) : Nat := clk p (bmax p + 1) 0

/-- The second scan and the end sites. -/
def endBase (p : Params) : Nat := tailBase p + span

/-- The end: the sites after the second scan, the loader's
drain, the Tensor Memory hand-back and barrier 2. The scans make at most `2 cmax p + 2`
collectives together. -/
def doneBase (p : Params) : Nat := endBase p + 4 * cmax p + 8

/-- The time of the end's site `o` after the second pass (`late`), or after the first pass without
a tile, before the pipeline. -/
def endT (p : Params) (late : Bool) (o : Nat) : Nat :=
  if late then doneBase p + o else primeBase p + 1000 + o

/-- A scan state with `c` warp collectives before it: at `base + 2 c` when its event is the
`c`-th collective, one earlier otherwise. -/
def passTime (base c : Nat) (coll : Bool) : Nat := if coll then base + 2 * c else base + 2 * c - 1

/-- The warp collectives the ghost ledger counts: shuffles and full-mask ballots. -/
def collCount (n : Cls → Nat) : Nat := n .shfl + n .vote

theorem scanBase_le_endBase (p : Params) : scanBase ≤ endBase p := by
  simp only [endBase, tailBase, clk, pipeBase, scanBase, span]
  omega

/-! ### The order of the phases -/

theorem passTime_ge (b c : Nat) (coll : Bool) : b - 1 ≤ passTime b c coll := by
  unfold passTime; split_ifs <;> omega

theorem scanBase_le_primeBase (p : Params) : scanBase ≤ primeBase p := by
  unfold primeBase; omega

/-- An end time is after the entry. -/
theorem endT_ge (p : Params) (l : Bool) (o : Nat) : scanBase ≤ endT p l o := by
  have h1 := scanBase_le_endBase p
  have h2 := scanBase_le_primeBase p
  unfold endT doneBase
  split_ifs <;> omega

theorem primeBase_le_clk (p : Params) (s o : Nat) : primeBase p + 1024 ≤ clk p s o := by
  unfold clk pipeBase; omega

theorem le_clk (p : Params) (s o : Nat) : scanBase - 1 ≤ clk p s o := by
  have := primeBase_le_clk p s o
  have := scanBase_le_primeBase p
  omega

theorem scanBase_le_tailBase (p : Params) : scanBase ≤ tailBase p := by
  have := primeBase_le_clk p (bmax p + 1) 0
  have := scanBase_le_primeBase p
  unfold tailBase; omega

theorem scan_pass_ge (p : Params) (late : Bool) (c : Nat) (coll : Bool) :
    scanBase - 1 ≤ passTime (if late then endBase p else scanBase) c coll := by
  have h1 := passTime_ge (if late then endBase p else scanBase) c coll
  have h2 := scanBase_le_endBase p
  split_ifs at h1 ⊢ <;> omega

/-! ### The order of the times -/

/-- An earlier slot is earlier, at any offsets inside the slot. -/
theorem clk_lt_of_slot {p : Params} {s s' o o' : Nat} (hs : s < s') (ho : o < span) :
    clk p s o < clk p s' o' := by
  have : span * s + span ≤ span * s' := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hs
  unfold clk; omega

/-- Within a slot an earlier offset is earlier. -/
theorem clk_lt_of_off {p : Params} {s o o' : Nat} (ho : o < o') : clk p s o < clk p s o' := by
  unfold clk; omega

/-- A clamped slot is monotone. -/
theorem slotOf_le {p : Params} {a b : Nat} (h : a ≤ b) : slotOf p a ≤ slotOf p b := by
  unfold slotOf; omega

/-- A clamped slot is at most the last slot before the tail. -/
theorem slotOf_le_bmax (p : Params) (a : Nat) : slotOf p a ≤ bmax p := by
  unfold slotOf; omega

/-- An unclamped slot. -/
theorem slotOf_eq {p : Params} {a : Nat} (h : a ≤ bmax p) : slotOf p a = a := by
  unfold slotOf; omega

/-- The prime region is before every pipeline slot. -/
theorem prime_lt_clk {p : Params} {o : Nat} (ho : o < 1024) (s o' : Nat) :
    primeBase p + o < clk p s o' := by
  have := primeBase_le_clk p s o'; omega

/-- A clamped slot is before the tail. -/
theorem clk_lt_tail {p : Params} {a o : Nat} (ho : o < span) :
    clk p (slotOf p a) o < tailBase p :=
  clk_lt_of_slot (Nat.lt_succ_of_le (slotOf_le_bmax p a)) ho

/-- The first scan is before the prime region when its collectives are within `cmax` (and a
ballot). -/
theorem pass_lt_prime {p : Params} {c : Nat} (hc : c ≤ cmax p + 1) (coll : Bool) :
    passTime scanBase c coll < primeBase p := by
  unfold passTime primeBase; split_ifs <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
