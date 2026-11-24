-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine

@[expose] public section

/-! # The times of the loader warps' states -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The loader warps -/

namespace Ld

/-- The scheduler's sites as the output warp's sites. -/
def toE : Loader.Site → Epilogue.Site
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | _ => .q0

/-- The second pass's sites. -/
def late : Loader.Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l => l
  | _ => false

/-- A packet site's offset in its packet, in program order: the page-table loop, the slot wait,
the pointer loop, per half of the rows its address load and per row the two shuffles and the
two copies, the commit, the arrival. -/
def pkOff : Loader.Site → Nat
  | .pgLd _ it => 3 * it.val
  | .pgSt _ it => 1 + 3 * it.val
  | .rwSt _ it => 2 + 3 * it.val
  | .slot _ _ => 6
  | .ptP _ _ it => 8 + 3 * it.val
  | .ptR _ _ it => 9 + 3 * it.val
  | .ptS _ _ it => 10 + 3 * it.val
  | .lw _ _ h => 14 + 33 * h.val
  | .xl _ _ i => 16 + 4 * i.val + (if 8 ≤ i.val then 1 else 0)
  | .xh _ _ i => 17 + 4 * i.val + (if 8 ≤ i.val then 1 else 0)
  | .cp _ _ i c => 18 + 4 * i.val + (if 8 ≤ i.val then 1 else 0) + c.val
  | .commit _ _ => 84
  | .arrive _ _ => 86
  | _ => 0

/-- A TMA group site's offset in its group: the wait, the elections, the elected lane's arrival
and copies. -/
def gOff : Loader.Site → Nat
  | .te _ e => 2 + 3 * e.val
  | .ta _ => 3
  | .tc _ c => 6 + 3 * c.val
  | _ => 0

/-- The packet a state is in: its commits so far, less one at the arrival (which follows the
packet's commit). -/
def idx (s : Loader.Site) (n : Cls → Nat) : Nat :=
  n (.load .commit) - match s with | .arrive _ _ => 1 | _ => 0

/-- The slot of packet `k ≥ 2`. -/
def slot (p : Params) (k : Nat) : Nat := slotOf p ((k - 2) / 2)

/-- **The time of a loader state** with ghost counts `n`: the first block (packets 0 and 1 and
TMA groups 0 to 3) in the prime region; packet `k ≥ 2` in the loader band of slot `(k - 2) / 2`,
a K packet at `+128`, a V packet at `+512`, the TMA groups 4 and 5 of a warm round between them
at `+384`, group 6 before the K packet at `+0`; the drain at the end; the scheduler's passes by
the shuffles of the scans so far (a packet makes 32 others) and the pass's ballot. -/
def time (p : Params) (d : Loader.D) (n : Cls → Nat) : Nat :=
  match d.site with
  | .q0 => primeBase p
  | .q1 => primeBase p + 1
  | .uk => primeBase p + 2
  | .pgLd per _ | .pgSt per _ | .rwSt per _ =>
    match per with
    | .prime => primeBase p + 8 + pkOff d.site
    | _ => clk p (slot p (idx d.site n)) (bandL + 128 + pkOff d.site)
  | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
  | .xh per v _ | .cp per v _ _ | .commit per v | .arrive per v =>
    match per with
    | .prime => primeBase p + 8 + (if v then 256 else 0) + pkOff d.site
    | _ => clk p (slot p (idx d.site n)) (bandL + (if v then 512 else 128) + pkOff d.site)
  | .tw t | .te t _ | .ta t | .tc t _ =>
    if t.val < 4 then primeBase p + 136 + 16 * t.val + gOff d.site
    else if t.val < 6 then
      clk p (slot p (idx d.site n)) (bandL + 384 + 16 * (t.val - 4) + gOff d.site)
    else clk p (slot p (idx d.site n)) (bandL + gOff d.site)
  | .dw j => doneBase p + 2 * j.val
  | .dq => doneBase p + 6
  | .de => doneBase p + 8
  | .da => doneBase p + 10
  | .exit => doneBase p + 12
  | .setmax => scanBase
  | s => passTime (if late s then endBase p else scanBase)
      (n .shfl - 32 * n (.load .commit) + Out.ballots (toE s)) (Out.coll (toE s))

/-- The loader's first block: its packets 0 and 1 and the TMA groups 0 to 3. -/
def prime : Loader.Site → Bool
  | .pgLd .prime _ | .pgSt .prime _ | .rwSt .prime _ | .slot .prime _ | .ptP .prime _ _
  | .ptR .prime _ _ | .ptS .prime _ _ | .lw .prime _ _ | .xl .prime _ _ | .xh .prime _ _
  | .cp .prime _ _ _ | .commit .prime _ | .arrive .prime _ => true
  | .tw t | .te t _ | .ta t | .tc t _ => decide (t.val < 4)
  | _ => false

/-- The loader's pipeline sites: the warm and steady packets and the TMA groups 4 to 6. -/
def pipe : Loader.Site → Bool
  | .pgLd per _ | .pgSt per _ | .rwSt per _ | .slot per _ | .ptP per _ _ | .ptR per _ _
  | .ptS per _ _ | .lw per _ _ | .xl per _ _ | .xh per _ _ | .cp per _ _ _ | .commit per _
  | .arrive per _ => per != .prime
  | .tw t | .te t _ | .ta t | .tc t _ => decide (4 ≤ t.val)
  | _ => false

/-- The time before which every loader state short of packet `i` is: the pipeline's base for
the first block, else the slot after packet `i`'s. -/
def bound (p : Params) (i : Nat) : Nat :=
  if i < 2 then pipeBase p else clk p (slotOf p ((i - 2) / 2) + 1) 0

theorem pipeBase_le_bound (p : Params) (i : Nat) : pipeBase p ≤ bound p i := by
  unfold bound clk; split_ifs <;> omega

theorem bound_mono (p : Params) {i i' : Nat} (h : i ≤ i') : bound p i ≤ bound p i' := by
  unfold bound
  have hs := slotOf_le (p := p) (show (i - 2) / 2 ≤ (i' - 2) / 2 by omega)
  split_ifs
  · exact le_rfl
  · unfold clk; omega
  · omega
  · have := Nat.mul_le_mul_left span (Nat.succ_le_succ hs)
    unfold clk
    simp only [Nat.succ_eq_add_one] at this
    omega

theorem pkOff_lt (s : Loader.Site) : pkOff s < 128 := by
  cases s <;> simp only [pkOff] <;> (try split_ifs) <;> omega

theorem gOff_lt (s : Loader.Site) : gOff s < 16 := by
  cases s <;> simp only [gOff] <;> omega

end Ld


namespace Ld

/-- The loader's bound for ring index `i` is at most the start of slot `i / 2`. -/
theorem bound_le (p : Params) (i : Nat) : bound p i ≤ clk p (i / 2) 0 := by
  unfold bound
  split_ifs with h
  · unfold clk; omega
  · have : slotOf p ((i - 2) / 2) + 1 ≤ i / 2 := by
      have := slotOf_le_bmax p ((i - 2) / 2)
      unfold slotOf; omega
    unfold clk
    have := Nat.mul_le_mul_left span this
    omega

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **A state of the loader's first block is more than one before the pipeline.** -/
theorem time_prime {p : Params} {d : Loader.D} {n : Cls → Nat} (h : prime d.site = true) :
    time p d n + 1 < pipeBase p := by
  obtain ⟨site, v, k⟩ := d
  have h1 := pkOff_lt site
  have h2 := gOff_lt site
  unfold pipeBase
  cases site <;> simp only [prime, Bool.false_eq_true, decide_eq_true_eq] at h
  all_goals first
    | (rename_i per _; cases per <;> simp only [prime, Bool.false_eq_true] at h <;>
        simp only [time] <;> (try split_ifs) <;> omega)
    | (rename_i per _ _; cases per <;> simp only [prime, Bool.false_eq_true] at h <;>
        simp only [time] <;> split_ifs <;> omega)
    | (rename_i per _ _ _; cases per <;> simp only [prime, Bool.false_eq_true] at h <;>
        simp only [time] <;> split_ifs <;> omega)
    | (simp only [time]; split_ifs <;> omega)

set_option linter.unusedSimpArgs false in
/-- **A pipeline state of the loader in packet `k ≤ i` is more than one before `bound p i`.** -/
theorem time_pipe {p : Params} {d : Loader.D} {n : Cls → Nat} {i : Nat}
    (h : pipe d.site = true) (hk : 2 ≤ idx d.site n) (hki : idx d.site n ≤ i) :
    time p d n + 1 < bound p i := by
  have hi : ¬ i < 2 := by omega
  have hs : slot p (idx d.site n) < slotOf p ((i - 2) / 2) + 1 :=
    Nat.lt_succ_of_le (slotOf_le (by omega))
  have h1 := pkOff_lt d.site
  have h2 := gOff_lt d.site
  have key : ∀ o, o + 1 < span → clk p (slot p (idx d.site n)) o + 1 <
      clk p (slotOf p ((i - 2) / 2) + 1) 0 := fun o ho => by
    have h := clk_lt_of_slot (p := p) (o' := 0) hs ho
    simp only [clk] at h ⊢
    omega
  simp only [bound, hi, ↓reduceIte]
  obtain ⟨site, v, k⟩ := d
  cases site <;> simp only [pipe, Bool.false_eq_true, decide_eq_true_eq] at h
  all_goals (try (rename_i per _; cases per <;> simp at h))
  all_goals simp only [time, bandL] at h1 h2 key ⊢
  all_goals (try split_ifs) <;>
    first
      | (with_reducible refine key _ ?_; simp only [span]; omega)
      | omega

end Ld

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
