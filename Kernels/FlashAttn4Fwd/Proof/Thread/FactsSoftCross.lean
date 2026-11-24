-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsAccessRoles

@[expose] public section

/-! # The softmax parts of the cross-warp premises

A softmax thread's accesses are its statistics-word stores (`soft_wr`): 4 bytes at
`+332 + 4 tid`, above the base word and below the ring regions (`LowAccessLow`, `BaseFree`). Its
arrivals name the leader's P-ready barriers of its stage and its polls its CTA's credit and S-full
barriers of its stage (`SyncNamed`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- The footprint of a softmax thread's access: its statistics word. -/
theorem soft_access_range {g k : Nat} {a : Acc} {w : Bool} {l : Loc} (hw : warpOf L g < 8)
    (h : X.Access (g, k) a w) (hc : a.Covers l) :
    L.sharedBase + 332 ≤ l.addr ∧ l.addr < L.sharedBase + 1356 := by
  obtain ⟨-, -, h1, h2⟩ := hc
  rcases h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
  · exfalso
    obtain ⟨d, t, ins, o, -, -, -, -, -, -, hev⟩ :=
      soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
    obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
    cases site <;> simp [Softmax.Ev] at hev
  swap
  · exfalso
    obtain ⟨d, t, ins, o, -, -, -, -, -, -, hev⟩ :=
      soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
    obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
    cases site <;> simp [Softmax.Ev] at hev
  · obtain ⟨d, -, -, -, hl, hs, -⟩ := soft_wr hpre hX ht hw he
    rw [hl] at h1 h2
    rw [hs] at h2
    have hb := hpre.block
    simp only [Softmax.sb, Softmax.tidOf] at h1 h2
    simp only [warpOf] at hw
    constructor <;> omega

/-- **`LowAccessLow`, softmax part.** -/
theorem lowAccessLow_soft {g k : Nat} {a : Acc} {w : Bool} {l : Loc} (hw : warpOf L g < 8)
    (h : X.Access (g, k) a w) (hc : a.Covers l) : l.addr < L.sharedBase + 68608 := by
  have := soft_access_range hpre hX ht hw h hc
  omega

/-- **`BaseFree`, softmax part.** -/
theorem baseFree_soft {g k : Nat} {a : Acc} {w : Bool} {l : Loc} (hw : warpOf L g < 8)
    (h : X.Access (g, k) a w) (hc : a.Covers l) (_h1 : L.sharedBase + 328 ≤ l.addr)
    (h2 : l.addr < L.sharedBase + 332) : False := by
  have := soft_access_range hpre hX ht hw h hc
  omega

/-- **`SyncNamed`, softmax part.** -/
theorem syncNamed_soft {g k pc : Nat} {m : Loc} {kd : Kind} (hw : warpOf L g < 8)
    (he : X.get (g, k) = some ⟨pc, kd⟩)
    (hk : (∃ tx c rel sc, kd = .arrive m tx c rel sc) ∨ (∃ p ok acq sc, kd = .wait m p ok acq sc)) :
    ∃ (b : FBar) (c : Nat), m = b.loc L c ∧ c / 2 = ctaOf L g / 2 ∧ ∀ i st, b ≠ .spare i st := by
  have hst : Softmax.stOf L g < 2 := by simp only [Softmax.stOf]; omega
  rcases hk with ⟨tx, c, rel, sc, rfl⟩ | ⟨p, ok, acq, sc, rfl⟩
  · obtain ⟨d, -, -, -, -, -, -, hs⟩ := soft_arrive hpre hX ht hw he
    rcases hs with ⟨lp, -, rfl⟩ | ⟨lp, -, rfl⟩
    · refine ⟨.pReady ⟨_, hst⟩, 2 * (ctaOf L g / 2), ?_, by omega, by simp⟩
      rw [← pReadyBar_eq]; rfl
    · refine ⟨.pReady2 ⟨_, hst⟩, 2 * (ctaOf L g / 2), ?_, by omega, by simp⟩
      rw [← pReady2Bar_eq]; rfl
  · obtain ⟨d, -, -, -, -, hs⟩ := soft_wait hpre hX ht hw he
    rcases hs with ⟨w, -, rfl, -⟩ | ⟨lp, -, rfl, -⟩
    · refine ⟨.stats ⟨_, hst⟩, ctaOf L g, ?_, rfl, by simp⟩
      rw [← statsBar_eq]; rfl
    · refine ⟨.sFull ⟨_, hst⟩, ctaOf L g, ?_, rfl, by simp⟩
      rw [← sFullBar_eq]; rfl

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
