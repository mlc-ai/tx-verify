-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Places
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Mma.Sim
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Glue
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Time
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Time
public import Lemmas.Kernel.Progress.Rank
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The time table of tml-fa4's thread machine

The progress descent ranks a pending thread by the time of its machine state
(`Sched.Timed`, `Sched.rank`). Here the machine is the glued, counted thread machine
`Proof.thread p L g`, so a time may read the ghost counts. A CTA runs one tile, and its timeline
is phase-major (`DECISIONS.md`, "The time table", and lane 1a's redesign):

* the startup, at the pc of its site (`startTime`, below 180);
* the entry of every role (the register request) at `scanBase`, the first warp barrier just after;
* the first scan of every role, at `scanBase + 2 c` for its `c`-th warp collective and one less
  between collectives (`passTime`), `c` the thread's shuffles so far and the pass's ballot;
* the prime region (`primeBase p`, 1024 wide): the request's reads of the loader and softmax
  warps and the loader's first block (packets 0 and 1 and TMA groups 0 to 3: the Q stages and
  the first Bias block);
* the pipeline, slot `s` and offset `o` at `clk p s o` (slots 4096 wide), each slot split into
  bands: the MMA warp at `[0, 512)` (`Mm.pipeT`: place `q` at `2 q`), softmax stage 0's score
  part `bandS 0`, the correction's stage-0 part `bandC 0`, softmax stage 1's score part
  `bandS 1` (opened by its closing credit poll of the previous round), the correction's stage-1
  part `bandC 1`, the softmax stages' P parts `bandP 0`, `bandP 1`, the loader `bandL`;
* the tail after every slot (`tailBase p`, slot `bmax p + 1`): the output warp's stores;
* the second scan, at `endBase p + 2 c` as in the first scan, with `c` the collectives of the
  scans (the pipeline's shuffles and ballots are not among them);
* the end (`doneBase p`): the last polls, barrier 2, the loader's drain, the returns; without a
  tile the last polls, barrier 2 and the returns are before the pipeline (`endT`).

The slot of a role state is a ghost count, clamped to `bmax p` so that every pipeline time is
before the tail: softmax round `u` (its S-full polls) in slot `u`, the correction's generation
`q` on its named barrier of stage `st` in slot `q` (its rescale round `q`, the final stage in slot
`U`, the tile's rounds), the loader's packet `k ≥ 2` in slot `(k - 2) / 2`, the MMA warp's
place by its round (`Mm.pipeT`). The waits the descent uses have their blocker earlier:

Waiter, wait, and its blocker (earlier):
* MMA poll of ring index `i` (K/V full): a loader lane short of packet `i`, in an earlier slot;
* MMA Q polls `clk 0 2`, `clk 0 18`: a loader lane before TMA group 0 or 2, in the prime region,
  or the group's open copy or byte balance (`Protocol/Q/Lag.lean`);
* loader wait for packet `k ≥ 3` (ring empty): the MMA release of index `k - 3`, in an earlier
  slot or in band M of the same slot;
* softmax round `u`'s S-full poll: the MMA warp's QK commit of round `u`, band M of slot `u`;
* MMA P-full and second-P polls of round `u`: softmax round `u` and correction round `u`, slot `u`;
* correction sync of round `q`, stage `st`: softmax stage `st`'s arrival of round `q`, `bandS st`
  of slot `q`;
* softmax stage 0's closing credit poll of round `u` (192): correction credit arrival `u` (`free`,
  then round `u`'s stage-1 part);
* softmax stage 1's closing credit poll of round `u` (200): correction credit arrival `u` (round
  `u + 1`'s stage-0 part, or `farr0`), slot `u + 1`;
* softmax Bias poll of round `u ≥ 1`: the loader's TMA groups of warm round `u - 1` (or group 6),
  slot `u - 1`;
* loader TMA groups 4, 5 of warm round `j`, group 6 (Bias empty): softmax round `j`'s Bias
  arrival, `bandS` of slot `j`;
* correction final sync of stage `st`: softmax stage `st`'s final arrival;
* correction O-final poll: the MMA warp's tail commit, band M of slot `U`;
* output ready poll, loader drain: the correction's final stage and the MMA releases, before the
  tail;
* register requests: every lane without one is at or before `scanBase`.

The order lemmas below (`clk_lt_of_slot`, `clk_lt_of_off`, `prime_lt_clk`, `clk_lt_tail`) give
each inequality from the bands and slots; the classes that use them are E1
(`Protocol/KV/Lag.lean`, `Protocol/Q/Lag.lean`), E2, E3, E4 and the correction field.
`Progress/Order.lean` states them by wait. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow

noncomputable section

/-! ### The startup -/

/-- A startup state is at the pc of its site: the startup's code runs forward from pc 25 to the
CTA barrier at pc 173 (an exit state `enter r` is never a state of the glued machine). -/
def startTime (s : Startup.D) : Nat := s.site.pc

/-! ### The thread machine -/

/-- The time of a role's state with ghost counts `n`: each role's table (the MMA warp's allocation
prefix before its first barrier); a stub has the first scan's base. -/
def roleTime (p : Params) (L : Launch) (g : Nat) :
    (i : Role) → (frag p L g i).D → (Cls → Nat) → Nat
  | .epilogue, d, n => Out.time p d n
  | .mma, .inl s, _ => Mm.startT s
  | .mma, .inr ⟨_, d⟩, n => Mm.time p d n
  | .correction, d, n => Cr.time p d.scheduler n
  | .softmax, d, n => Sm.time p L g d.scheduler n
  | .loader _, d, n => Ld.time p d n
  | .stub _, _, _ => scanBase

/-- **The time of a state of the thread machine.** -/
def time (p : Params) (L : Launch) (g : Nat) : (thread p L g).D → Nat
  | (.inl s, _) => startTime s
  | (.inr ⟨i, d⟩, n) => roleTime p L g i d n

/-- **tml-fa4's time table**: the thread machine and the time of its states. -/
def timed (p : Params) (L : Launch) : Sched.Timed kernel Assumptions.all L :=
  ⟨thread p L, time p L⟩

/-! ### Lower bounds -/

theorem scanBase_le_doneBase (p : Params) : scanBase ≤ doneBase p := endT_ge p true 0

/-- Every loader state is after every startup state. -/
theorem Ld.time_ge (p : Params) (d : Loader.D) (n : Cls → Nat) : scanBase - 1 ≤ Ld.time p d n := by
  have hs := scanBase_le_primeBase p
  have ht := scanBase_le_doneBase p
  simp only [Ld.time]
  split <;> (try split) <;> (try split_ifs) <;>
    first
      | omega
      | exact le_clk _ _ _
      | exact (passTime_ge _ _ _).trans' (by have := scanBase_le_endBase p; omega)

/-- Every role state is after every startup state. -/
theorem roleTime_ge {p : Params} {L : Launch} {g : Nat} (i : Role) (d : (frag p L g i).D)
    (n : Cls → Nat) : scanBase - 1 ≤ roleTime p L g i d n := by
  have hs := scanBase_le_primeBase p
  have ht := scanBase_le_tailBase p
  have hd := scanBase_le_doneBase p
  have scan : ∀ (a b : Prop) [Decidable a] [Decidable b] (late : Bool) (c : Nat) (coll : Bool),
      scanBase - 1 ≤ if a then scanBase else if b then scanBase + 3 else
        passTime (if late then endBase p else scanBase) c coll := by
    intro a b _ _ late c coll
    have := scan_pass_ge p late c coll
    split_ifs at this ⊢ <;> omega
  cases i with
  | epilogue =>
    simp only [roleTime, Out.time]
    split_ifs
    · omega
    · omega
    all_goals first | exact scan_pass_ge p true _ _ | exact scan_pass_ge p false _ _
  | mma =>
    rcases d with d | ⟨_, d⟩
    · cases d <;> simp only [roleTime, Mm.startT] <;> omega
    · simp only [roleTime, Mm.time, Mm.pipeT]
      split
      · exact le_clk _ _ _
      · split
        · exact (Nat.sub_le _ _).trans (endT_ge p _ _)
        · split
          · omega
          · exact scan_pass_ge p _ _ _
  | correction =>
    simp only [roleTime, Cr.time]
    split
    · exact le_clk _ _ _
    · split
      · exact (Nat.sub_le _ _).trans (endT_ge p _ _)
      · exact scan _ _ _ _ _
  | loader b => exact Ld.time_ge p d n
  | stub r => simp [roleTime]
  | softmax =>
    simp only [roleTime, Sm.time]
    split
    · exact le_clk _ _ _
    · split
      · omega
      · split
        · exact (Nat.sub_le _ _).trans (endT_ge p _ _)
        · exact scan _ _ _ _ _

theorem time_minj {p : Params} {L : Launch} {g : Nat} {d : Mma.D} {n : Cls → Nat} :
    (timed p L).time g (Mma.minj p L g d n) = Mm.time p d n := rfl

theorem time_inj {p : Params} {L : Launch} {g : Nat} {d : Epilogue.D} {n : Cls → Nat} :
    (timed p L).time g (Epilogue.inj p L g d n) = Out.time p d n := rfl

theorem time_start {p : Params} {L : Launch} {g : Nat} {s : Startup.D} {n : Cls → Nat} :
    (timed p L).time g (.inl s, n) = startTime s := rfl

/-- Every startup state that is not an exit is earlier than the first scan. -/
theorem startTime_lt {s : Startup.D} (hx : ∀ r, s.site ≠ .enter r) : startTime s < scanBase := by
  simp only [startTime, scanBase]
  cases hs : s.site with
  | sh j => fin_cases j <;> decide
  | elect j => fin_cases j <;> decide
  | init n => fin_cases n <;> decide
  | fence => decide
  | bar => decide
  | enter r => exact absurd hs (hx r)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
