-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.DirectMem
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsValues

@[expose] public section

/-!
# No sixteen-byte write of a compute thread before its first matrix event

A *compute thread* is a thread with index below 128 in its thread block. A *matrix event* is
the event of a warp-wide matrix instruction (`ldmatrix`, `stmatrix`, `movmatrix`, `mma.sync`);
`WarpMatrix.ordinal X g k` counts the matrix events of thread `g` before position `k` of its
trace.

The value layer's read-back of the rows of the bfloat16 state copy (`Values/AccRows.lean`)
identifies the last write of a row as the row write of an `stmatrix` of the tile loop. For that
it must exclude every earlier write of sixteen bytes by the same thread. This file proves the
exclusion, by one case split over the phases of the thread's run (`Assembly.Stage`) and the
closed-form event of each phase:

* the startup phase and the CarryLoad phase make no write;
* the Conversion phase writes two bytes at a time (one bfloat16 element);
* the epilogue writes four bytes at a time (one word of the final state);
* a write of the tile loop is the row write of an `stmatrix`, the second event of the
  instruction: the instruction's own matrix event comes before it (`wr_mat`).

`earlyWrite` is the statement for one event, `earlyWrites` the form the value layer consumes.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

namespace TileHyps

/-- At the row write of an `stmatrix` (position `n` of a tile) the thread has made at least one
matrix event of the tile: the instruction's own. -/
theorem wr_mat : ∀ n < 268, Compute.Proto.isWr (Compute.skOf n) = true →
    1 ≤ Compute.matOf n := by decide +kernel

/-- **A write of a compute thread before its first matrix event is not a write of sixteen
bytes.** -/
theorem earlyWrite (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {k : Nat} {e : Event} {a : Acc} {bs : List Byte} (hc : tid g < 128)
    (he : X.get (g, k) = some e) (hk : e.kind = .wr a bs)
    (h0 : WarpMatrix.ordinal X g k = 0) : a.size ≠ 16 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he fun f h => by rw [hk] at h; cases h
  cases hst with
  | startup hI =>
    rcases Startup.event_at hpre hX hg he hσ with ⟨pos, hr, -, hev⟩ | h
    · rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Startup.Ev] at hev
      · obtain ⟨inst, ld, rfl⟩ := hev
        cases hk
      · obtain ⟨v, ok, rfl⟩ := hev
        cases hk
      · subst hev
        cases hk
      · subst hev
        cases hk
      · subst hev
        cases hk
      · obtain ⟨i, hi, bs', hbs, rfl⟩ := hev
        cases hk
      · subst hev
        cases hk
      · subst hev
        cases hk
      · obtain ⟨ok, rfl⟩ := hev
        cases hk
    · exact absurd h hI.inv.not_left
  | conversion _ _ hI =>
    obtain ⟨pos, hr, -, -, hev⟩ := Conversion.event_at hpre hX hg he hσ hI
    cases pos with
    | fence =>
      rw [show e = _ from hev] at hk
      cases hk
    | ld j u =>
      obtain ⟨bs', -, rfl⟩ := hev
      cases hk
    | st j u =>
      rcases hev with ⟨v', -, rfl⟩ | ⟨f, -, rfl⟩
      · cases hk
        exact (by decide : (2 : Nat) ≠ 16)
      · cases hk
    | bar j =>
      rw [show e = _ from hev] at hk
      cases hk
  | carryLoad _ _ hI =>
    obtain ⟨pos, hr, hev, -⟩ := CarryLoad.event_at hpre hX hg he hσ hI
    cases pos with
    | ld j =>
      obtain ⟨bs', -, rfl⟩ := hev
      cases hk
    | fence =>
      rw [show e = _ from hev] at hk
      cases hk
  | compute _ _ _ _ hI =>
    obtain ⟨pos, hR, hled, -, -⟩ := hI
    have hev := Compute.Proto.ev_at hpre hX hR hσ he
    cases pos with
    | entry =>
      rw [show e = _ from hev] at hk
      cases hk
    | tile t n =>
      have hn : n < 268 := hR.facts.pos
      have hmat := Compute.Vals.mats_tile hled
      rcases Compute.Proto.pos_cases hn with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h2, h264⟩
      · obtain ⟨ok, rfl⟩ := Compute.Proto.evAt_0.mp hev
        cases hk
      · obtain ⟨ok, rfl⟩ := Compute.Proto.evAt_1.mp hev
        cases hk
      · rw [Compute.Proto.evAt_264.mp hev] at hk
        cases hk
      · rw [Compute.Proto.evAt_265.mp hev] at hk
        cases hk
      · rw [Compute.Proto.evAt_266.mp hev] at hk
        cases hk
      · rw [Compute.Proto.evAt_267.mp hev] at hk
        cases hk
      · rw [Compute.Proto.evAt_body h2 h264] at hev
        by_cases ha : (Compute.Proto.addrOf n).2.2 = 0
        · rw [ite_eq_left ha] at hev
          rcases hev with ⟨op, own, recv, h⟩ | ⟨f, h⟩
          · rw [hk] at h
            cases h
          · rw [hk] at h
            cases h
        · rw [ite_eq_right ha] at hev
          rcases hev with ⟨bs', h, -⟩ | ⟨bs', -, hwr⟩
          · rw [hk] at h
            cases h
          · have := wr_mat n hn hwr
            omega
  | producer hr _ _ _ _ =>
    have := (warp_eq4_iff g).mp hr
    omega
  | store hr _ _ _ _ _ =>
    have := (warp_eq5_iff g).mp hr
    omega
  | epilogue past hj _ hI =>
    obtain ⟨pos, hr, hon, -, -, -, hex⟩ := Epilogue.event_at hpre hX hg he hσ (hI hub)
    cases pos with
    | st j =>
      rcases hex with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩
      · cases hk
        exact (by decide : (4 : Nat) ≠ 16)
      · cases hk
    | ts i =>
      rw [show e = _ from hex] at hk
      cases hk
    | bar7 =>
      rw [show e = _ from hex] at hk
      cases hk
    | fence =>
      rw [show e = _ from hex] at hk
      cases hk
    | bar8 =>
      rw [show e = _ from hex] at hk
      cases hk
    | commit =>
      rw [show e = _ from hex] at hk
      cases hk
    | bwait =>
      rw [show e = _ from hex] at hk
      cases hk
    | bar9 =>
      rw [show e = _ from hex] at hk
      cases hk
    | exit =>
      rw [show e = _ from hex] at hk
      cases hk

/-- **No lane of a compute warp writes sixteen bytes before its first matrix event**: the form
of `earlyWrite` for lane `l` of the compute warp `w` of thread block `c`. -/
theorem earlyWrites (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ c w, c < L.grid → w < 4 → ∀ l < 32, ∀ k pc a bs,
      WarpMatrix.ordinal X (c * L.block + 32 * w + l) k = 0 →
      X.get (c * L.block + 32 * w + l, k) = some ⟨pc, .wr a bs⟩ → a.size ≠ 16 := by
  intro c w _ hw l hl k pc a bs h0 he
  refine earlyWrite hpre hX ?_ he rfl h0
  rw [hpre.block]
  unfold tid
  omega

end TileHyps

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
