-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefLoop

@[expose] public section

/-! # The index warp's reference invariant is kept by every step

`ref_step`: from a state with `Ref`, an event of the state's shape that the machine follows
leads to a state with `Ref` for the bumped counts (an undefined-behaviour event bumps the class
`ub`, after which `Ref` asks nothing). `ref_init`: the first state with no counts. The loads,
shuffles, stores and the barrier count nothing on the ring (`body_quiet`); a successful poll
counts one on the slot's `coordFree` (`body_poll`); an arrival counts one on the slot's
`coordReady` and the block's end starts block `i + 1` with the next slot and parity
(`body_arrive`). The loops' counters of the next state (`Ctr`) come from `RefLoop.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem loc_inj {f f' : MbarFam} (h : MbarRow.loc L g f = MbarRow.loc L g f') : f = f' := by
  simp only [MbarRow.loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
  exact MbarFam.off_inj h

/-- A class the event's kind is not in keeps its count. -/
theorem bump_eq {e : Event} {c : Cnt} (h : kindOf e ≠ some c) (n : Cnt → Nat) :
    Code.bump cls n e c = n c := by
  simp [Code.bump, cls, h]

/-- The class the event's kind is in, at a pc of the role, counts one more. -/
theorem bump_self {e : Event} {c : Cnt} (hin : inRole e = true) (h : kindOf e = some c)
    (n : Cnt → Nat) : Code.bump cls n e c = n c + 1 := by
  simp [Code.bump, cls, h, hin]

/-- Every site but the exit is at a pc of the role. -/
theorem site_inRole (s : IxSite) (h : s ≠ .exit) : 2332 ≤ s.pc ∧ s.pc ≤ 2586 := by
  cases s <;> first | exact absurd rfl h | decide

/-- After undefined behaviour the invariant asks nothing. -/
theorem ref_ub {d' : D} {n : Cnt → Nat} {e : Event} {f : Fault} (hin : inRole e = true)
    (hk : e.kind = .ub f) : Ref P L g d' (Code.bump cls n e) := by
  intro h
  have := bump_self (c := .ub) hin (by simp [kindOf, hk]) n
  omega

/-- An event in no class of the ring: the body at the same block. -/
theorem body_quiet {d' : D} {n : Cnt → Nat} {e : Event} {i : Nat}
    (hq : ∀ l, kindOf e ≠ some (.acq l) ∧ kindOf e ≠ some (.arrive l))
    (hpre : preSite d'.site = true → i = 0) (hsl : d'.c.slot = MbarRow.slot4 i)
    (hpa : d'.c.par = decide (i / 4 % 2 = 1)) (hc : RingCounts L g n i (incW d'.site))
    (hct : Ctr P L g d'.site d'.c i) (hst : StEq L g d' (Code.bump cls n e) i) :
    Body P L g d' (Code.bump cls n e) := by
  refine ⟨i, hpre, hsl, hpa, fun s => ?_, hct, hst⟩
  rw [bump_eq (hq _).1, bump_eq (hq _).2]
  exact hc s

/-- A successful poll of the block's `coordFree`. -/
theorem body_poll {d' : D} {n : Cnt → Nat} {e : Event} {i : Nat} (hin : inRole e = true)
    (hk : kindOf e = some (.acq (MbarRow.loc L g (.coordFree (MbarRow.slot4 i)))))
    (hpre : preSite d'.site = false) (hsl : d'.c.slot = MbarRow.slot4 i)
    (hpa : d'.c.par = decide (i / 4 % 2 = 1)) (hw : incW d'.site = 1)
    (hc : RingCounts L g n i 0) (hct : Ctr P L g d'.site d'.c i)
    (hst : StEq L g d' (Code.bump cls n e) i) : Body P L g d' (Code.bump cls n e) := by
  refine ⟨i, by simp [hpre], hsl, hpa, fun s => ?_, hct, hst⟩
  obtain ⟨h1, h2⟩ := hc s
  rw [hw, ring_succ]
  refine ⟨?_, by rw [bump_eq (by rw [hk]; simp), h2]⟩
  by_cases hs : MbarRow.slot4 i = s
  · subst hs
    rw [bump_self hin hk, h1]; simp
  · have hne : kindOf e ≠ some (.acq (MbarRow.loc L g (.coordFree s))) := by
      rw [hk]; intro h
      simp only [Option.some.injEq, Cnt.acq.injEq] at h
      exact hs (MbarFam.coordFree.inj (loc_inj h))
    rw [bump_eq hne, h1]
    simp [hs]

/-- The block's arrival on its `coordReady`, and the next block. -/
theorem body_arrive {d' : D} {n : Cnt → Nat} {e : Event} {i : Nat} (hin : inRole e = true)
    (hk : kindOf e = some (.arrive (MbarRow.loc L g (.coordReady (MbarRow.slot4 i)))))
    (hpre : preSite d'.site = false) (hsl : d'.c.slot = MbarRow.slot4 (i + 1))
    (hpa : d'.c.par = decide ((i + 1) / 4 % 2 = 1)) (hw : incW d'.site = 0)
    (hc : RingCounts L g n i 1) (hct : Ctr P L g d'.site d'.c (i + 1))
    (hst : StEq L g d' (Code.bump cls n e) (i + 1)) : Body P L g d' (Code.bump cls n e) := by
  refine ⟨i + 1, by simp [hpre], hsl, hpa, fun s => ?_, hct, hst⟩
  obtain ⟨h1, h2⟩ := hc s
  rw [hw, Nat.add_zero, ring_succ]
  refine ⟨by rw [bump_eq (by rw [hk]; simp), h1, ring_succ], ?_⟩
  by_cases hs : MbarRow.slot4 i = s
  · subst hs
    rw [bump_self hin hk, h2]; simp
  · have hne : kindOf e ≠ some (.arrive (MbarRow.loc L g (.coordReady s))) := by
      rw [hk]; intro h
      simp only [Option.some.injEq, Cnt.arrive.injEq] at h
      exact hs (MbarFam.coordReady.inj (loc_inj h))
    rw [bump_eq hne, h2]
    simp [hs]

/-- **The first state has the invariant** with no counts. -/
theorem ref_init (hp : Pre P L m) : Ref P L g (ofC (ixFirst P L g)) (fun _ => 0) := by
  intro _
  obtain ⟨h1, h2, h3⟩ := zero_first P L g
  change incW (ixFirst P L g).1 = 0 at h3
  refine ⟨0, fun _ => rfl, h1, h2, fun s => ?_, ctr_first hp g, ?_⟩
  · simp only [h3, Nat.add_zero, ringUses_zero s.isLt, and_self]
  · refine ⟨?_, IxSite.elems_pos _, ?_⟩
    · show 0 = _ + stDone L g (ixFirst P L g).1 0
      rw [stDone_incW h3]; rfl
    · intro hb
      rcases hb with hb | hb <;> (change (ixFirst P L g).1 = _ at hb; rw [hb] at h3
                                  exact absurd h3 (by decide))

/-! ### The machine's transitions -/

theorem ncNext_some {f : BitVec 64 → D} {bs : List (Option Byte)} {d' : D}
    (h : Code.ncNext f bs = some (some d')) : ∃ x, d' = f x := by
  unfold Code.ncNext at h
  split at h
  · exact ⟨_, (Option.some.inj (Option.some.inj h)).symm⟩
  · cases h
  · cases h

/-- An element of an index pair: the same site and words, or the state after the pair. -/
theorem ldNext_cases (d : D) (y : BitVec 64) (n : BitVec 64 → BitVec 64 → D) :
    (ldNext d y n).site = d.site ∧ (ldNext d y n).c = d.c ∨ ∃ y0 y1, ldNext d y n = n y0 y1 := by
  unfold ldNext; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨_, _, rfl⟩

theorem stNext_cases (d n : D) :
    (stNext d n).site = d.site ∧ (stNext d n).c = d.c ∨ stNext d n = n := by
  unfold stNext; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr rfl

theorem afterSt_cases (b a : IxSite) : afterSt L g b a = b ∨ afterSt L g b a = a := by
  unfold afterSt; split
  · exact .inr rfl
  · exact .inl rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
