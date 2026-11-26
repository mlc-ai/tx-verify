-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Trace
public import Kernels.FlashKdaFwd.Proof.Values.Ends.Contract

@[expose] public section

/-! # The value layer's contract for the carry loads

`Proof/Values/Ends/Contract.lean: CarryRef L X` is what the value layer takes from this phase:

* `load`: the event at the `j`-th carry-load site (`Values.Ends.carrySite j`, `j < 128`) of a
  compute thread is a read of four bytes at the swizzled address of the thread's base pointer
  (`shared_mem + 4 * laneOff tid`) plus the constant of the instruction
  (`Values.Ends.carryConst j`), with at most five `bar.sync 0` before it;
* `first`: a compute thread at the `j`-th of these sites (`j ≤ 128`; the 128th is the proxy
  fence after the loads) before its event `k` was at the first of them before its event
  `k - j`: the loads and the fence are consecutive events.

This file proves both fields for the followed states of the phase:

* `carry_load`: field `load` at a state of the invariant (`Inv P X g k1 k d`);
* `carry_first`: field `first` at a state of the invariant, given the entry state at `k1`;
* `carryRef_of`: the structure `CarryRef L X`, from the one fact that the chain of the phases
  supplies: a followed state of a compute thread at a carry site (a load site `load_31` to
  `load_158`, or the fence `fenceProxy_1`) is a state of the CarryLoad phase (`AtCarry`).

The value layer's vocabulary is this phase's: `carrySite` is `ldSite` (`ldSite_eq`),
`carryConst j` is the generated constant `kOf j` (`kOf_carryConst`, both tables come from the
same instructions), `swzAddr` is `Conversion.swzN`, and the base pointer
`L.sharedBase + 4 * laneOff (g % L.block)` is `Conversion.carryBase P g` (`ldAddr_eq`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion (swzN carryBase)
open PTX.Kernels.FlashKdaFwd.Proof.Values.Ends (carrySite carryConst laneOff swzAddr CarryRef)
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Before)

noncomputable section
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {e : Event}

/-- The site of a carry load, in the value layer's name. -/
theorem ldSite_eq (j : Nat) : ldSite j = carrySite j := rfl

/-- The constants of this phase's table are the value layer's. -/
theorem kOf_carryConst : ∀ j < 128, kOf j = carryConst j := by decide +kernel

/-- **The address of carry load `j`, in the value layer's terms**: the swizzled address of
`shared_mem + 4 * laneOff tid` plus the constant of the load. -/
theorem ldAddr_eq (hpre : Pre P L mem0) {j : Nat} (hj : j < 128) :
    ldAddr P g j = swzAddr (L.sharedBase + 4 * laneOff (g % L.block) + carryConst j) := by
  have hb : L.sharedBase + 4 * laneOff (g % L.block) = carryBase P g := by
    rw [hpre.sharedBase, block_mod hpre]
    unfold laneOff carryBase warp lane tid
    omega
  rw [hb, ← kOf_carryConst j hj]
  rfl

/-- **The number of events of the phase before a state of the invariant at the carry site
`j`** (`j ≤ 128`) of a compute thread is `j`. -/
theorem done_of_site {pos : Pos} {d : D} {j : Nat} (hr : RefAt P g pos d) (hc : tid g < 128)
    (hj : j ≤ 128) (hs : d.site = carrySite j) : done g pos = j := by
  have hs' : pos.site = ldSite j := hr.site.symm.trans hs
  cases pos with
  | ld j' =>
    rcases Nat.lt_or_ge j 128 with hlt | hge
    · exact ldSite_inj j'.isLt hlt hs'
    · obtain rfl : j = 128 := by omega
      exact absurd hs' (ldSite_ne_fence j'.isLt)
  | fence =>
    rcases Nat.lt_or_ge j 128 with hlt | hge
    · exact absurd hs'.symm (ldSite_ne_fence hlt)
    · simp only [done, hc, ↓reduceIte]
      omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **`CarryRef.load` at a state of the invariant**: the event at the `j`-th carry-load site
is a read of the four bytes at the swizzled address of the thread's base pointer plus the
constant of the load, in the thread's own block, with five `bar.sync 0` before it. -/
theorem carry_load {k1 k : Nat} {d : D} (j : Fin 128)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hI : Inv P X g k1 k d)
    (hs : d.site = carrySite j.val) (he : X.get (g, k) = some e) :
    ∃ a bs, e = ⟨d.site.pc, .rd a bs⟩ ∧ a.size = 4 ∧
      a.loc = ⟨.shared, g / L.block,
        swzAddr (L.sharedBase + 4 * laneOff (g % L.block) + carryConst j.val)⟩ ∧
      bar0Before X (g, k) ≤ 5 := by
  obtain ⟨pos, hr, hev, -⟩ := event_at hpre hX hg he hσ hI
  have hbar : bar0Before X (g, k) = 5 := by
    obtain ⟨_, -, hl, -⟩ := hI
    exact congrArg Startup.Led.bars hl
  cases pos with
  | ld j' =>
    obtain rfl : j' = j := Fin.ext (ldSite_inj j'.isLt j.isLt (hr.site.symm.trans hs))
    obtain ⟨bs, -, rfl⟩ := hev
    refine ⟨{ loc := ⟨.shared, cta g, ldAddr P g j'.val⟩, size := 4 }, bs, ?_, rfl, ?_,
      by omega⟩
    · rw [hr.site]
      show _ = Event.mk (ldSite j'.val).pc _
      rw [ldSite_pc j'.val j'.isLt]
    · show Loc.mk .shared (cta g) (ldAddr P g j'.val) = _
      rw [ldAddr_eq hpre j'.isLt, block_div hpre]
  | fence =>
    exact absurd (hr.site.symm.trans hs).symm (ldSite_ne_fence j.isLt)

omit hpre hX hg in
/-- **`CarryRef.first` at a state of the invariant**: a compute thread at the carry site `j`
before its event `k` entered the phase `j` events earlier, at the first carry load. -/
theorem carry_first {k1 k j : Nat} {s1 d : D} (hc : tid g < 128) (hj : j ≤ 128)
    (hσ1 : Frame.stateAt (code L) X g k1 = some (some s1)) (hin : In P X g k1 s1)
    (hI : Inv P X g k1 k d) (hs : d.site = carrySite j) :
    j ≤ k ∧ ∃ d0, Frame.stateAt (code L) X g (k - j) = some (some d0) ∧
      d0.site = carrySite 0 := by
  obtain ⟨pos, hr, -, hd⟩ := hI
  have hdone := done_of_site hr hc hj hs
  have hk : k - j = k1 := by omega
  refine ⟨by omega, s1, by rw [hk]; exact hσ1, ?_⟩
  have h0 := hin.1.site
  simp only [hc, ↓reduceIte] at h0
  exact h0

end

/-- **A followed state of a compute thread at a carry site is a state of the CarryLoad
phase**: the thread is launched, it entered the phase at an event `k1` (a followed state with
the entry condition), and the state has the invariant. The chain of the phases proves it
(`Ref/Assembly`): a state at one of these sites is in no other phase. -/
def AtCarry (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k d j, j ≤ 128 → g % L.block < 128 → Frame.stateAt (code L) X g k = some (some d) →
    d.site = carrySite j →
    g < L.threads ∧ ∃ k1 s1, Frame.stateAt (code L) X g k1 = some (some s1) ∧
      In P X g k1 s1 ∧ Inv P X g k1 k d

/-- **The value layer's contract `CarryRef`**, from the invariant of the phase and the fact
that the carry sites are reached only inside it. -/
theorem carryRef_of (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hat : AtCarry P L X) : CarryRef L X where
  load := by
    intro g k d e j hc hσ hs he
    obtain ⟨hg, k1, s1, -, -, hI⟩ := hat g k d j.val (by omega) hc hσ hs
    exact carry_load hpre hX hg j hσ hI hs he
  first := by
    intro g k d j hc hj hk hσ hs
    obtain ⟨hg, k1, s1, hσ1, hin, hI⟩ := hat g k d j hj hc hσ hs
    exact carry_first (by rw [← block_mod hpre]; exact hc) hj hσ1 hin hI hs

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
