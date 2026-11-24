-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmNxt
public import Kernels.InklingRelDecode.Proof.Thread.SmStretch

@[expose] public section

/-! # The masked lanes of the softmax region's bias loads

Where a lane's mask is false the 64 guarded loads of a group are skipped: each guarded load is a
local step that keeps every fact (`Seg.skip`), and each zero fill finds its destination zero
already. The skip of the preloads (`seg_skipPre`, pcs 680 to 806, mask `%p85` false) and of the
loop's loads (`seg_skipNxt`, pcs 1124 to 1250, mask `%p92` false) are chained by induction on the
index. The words of a skipped group are zero, so the state with the group's count set to 64 and
its words set to the zero half-word has the same register values (`valueOf_skipPre`,
`valueOf_skipNxt`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat}

theorem live_skipPre : ∀ j < 64,
    ∀ r ∈ Flow.live (680 + 2 * j + 1), r ∈ Flow.live (680 + 2 * j) := by decide +kernel
theorem live_skipNxt : ∀ j < 64,
    ∀ r ∈ Flow.live (1124 + 2 * j + 1), r ∈ Flow.live (1124 + 2 * j) := by decide +kernel

/-- A piece with its end counter written differently. -/
theorem seg_end {n s b b' : Nat} {F G : List (Nat × Value)}
    (h : Seg kernel asms L g n s F b G) (hb : b = b') : Seg kernel asms L g n s F b' G :=
  hb ▸ h

/-- Two states with the same value table have the same facts at every counter. -/
theorem factsAt_congr {d d' : D} (h : valueOf L g d' = valueOf L g d) (pc : Nat) :
    factsAt L g pc d' = factsAt L g pc d := by
  simp only [factsAt, h]

/-- A state at a skipped group of preloads has the same values as the state with 64 zero words. -/
theorem valueOf_skipPre (d : D) (hcw : d.cw = 0) :
    valueOf L g { d with cw := 64, w := fun _ => z16 } = valueOf L g d := by
  funext r
  exact valueOf_congr (L := L) (g := g) (d := d) (d' := { d with cw := 64, w := fun _ => z16 })
    rfl rfl rfl rfl (by funext k; simp [D.wd, hcw]) rfl rfl rfl rfl r

/-- A state at a skipped group of loop loads has the same values as the state with 64 zero words. -/
theorem valueOf_skipNxt (d : D) (hcv : d.cv = 0) :
    valueOf L g { d with cv := 64, v := fun _ => z16 } = valueOf L g d := by
  funext r
  exact valueOf_congr (L := L) (g := g) (d := d) (d' := { d with cv := 64, v := fun _ => z16 })
    rfl rfl rfl rfl rfl (by funext k; simp [D.vd, hcv]) rfl rfl rfl r

/-! ### The preloads -/

/-- `mov.u16 %rs(265 + j), %rs18` where the destination holds the zero half-word already. -/
theorem seg_fillP (d : D) {j : Nat} (hj : j < 63) (hz : d.wd (j + 1) = z16) :
    Seg kernel asms L g 1 (681 + 2 * j) (factsAt L g (681 + 2 * j) d) (681 + 2 * j + 1)
      (factsAt L g (681 + 2 * j + 1) d) := by
  obtain ⟨hl0, hl1⟩ := live_mov j hj
  refine seg_one (r := 264 + j) (v := z16) (movAt_spec (movAt_pre j hj)) rfl ?_ ?_ hl1
  · intro t h
    have h0 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) hl0)
    have e0 : valueOf L g d 199 = z16 := by sm_vals
    rw [e0] at h0
    exact exec_mov16 (segFree (by rw [h.1]; exact emu_pre j hj)) h0
  · rw [show 264 + j = 263 + (j + 1) by omega, valueOf_pre d (by omega : j + 1 < 64)]
    exact hz

/-- The guarded preload `j` is skipped where `%p85` is false. -/
theorem seg_skipLoadP (d : D) (h85 : valueOf L g d 85 = .pred false) {j : Nat} (hj : j < 64) :
    Seg kernel asms L g 1 (680 + 2 * j) (factsAt L g (680 + 2 * j) d) (681 + 2 * j)
      (factsAt L g (681 + 2 * j) d) := by
  obtain ⟨a, hc, -⟩ := loadAt_spec (loadAt_pre j hj)
  have hp : (85, Value.pred false) ∈ factsAt L g (680 + 2 * j) d := by
    have := Flow.mem_factsFrom (val := valueOf L g d) (live_pre j hj)
    rwa [h85] at this
  have h := Seg.skip (K := kernel) (A := asms) (L := L) (g := g) hc hp rfl
  exact seg_cast (h.weaken_end fun R hR => Flow.holds_factsFrom_mono hR (live_skipPre j hj))
    rfl (by omega)

/-- Preload `j` is skipped, and the zero fill of the next destination runs. -/
theorem seg_skipStepP (d : D) (h85 : valueOf L g d 85 = .pred false) (hcw : d.cw = 0) {j : Nat}
    (hj : j < 63) :
    Seg kernel asms L g 2 (680 + 2 * j) (factsAt L g (680 + 2 * j) d) (680 + 2 * (j + 1))
      (factsAt L g (680 + 2 * (j + 1)) d) := by
  have h1 := seg_skipLoadP (L := L) (g := g) d h85 (j := j) (by omega)
  have h2 := seg_fillP (L := L) (g := g) d (j := j) hj (by simp [D.wd, hcw])
  have h2' := seg_end (h2.weaken_end fun R hR => Flow.holds_factsFrom_mono hR (live_after j hj))
    (by omega : 681 + 2 * j + 1 = 680 + 2 * (j + 1))
  exact Seg.of_len (h1.comp h2') rfl

/-- **Every guarded preload is skipped** where `%p85` is false: from preload 0 to the end of the
group. -/
theorem seg_skipPreFrom (d : D) (h85 : valueOf L g d 85 = .pred false) (hcw : d.cw = 0) :
    ∀ m, m ≤ 63 →
      Seg kernel asms L g (2 * m) 680 (factsAt L g 680 d) (680 + 2 * m)
        (factsAt L g (680 + 2 * m) d) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih =>
    exact fun hm => Seg.of_len ((ih (by omega)).comp (seg_skipStepP d h85 hcw (j := m) (by omega)))
      (by omega)

/-- **The preloads of a masked lane** (pcs 680 to 806): all skipped, to the setup at pc 807. -/
theorem seg_skipPre (d : D) (h85 : valueOf L g d 85 = .pred false) (hcw : d.cw = 0) :
    Seg kernel asms L g 127 680 (factsAt L g 680 d) 807 (factsAt L g 807 d) := by
  have h1 := seg_skipPreFrom d h85 hcw 63 (le_refl 63)
  have h2 := seg_skipLoadP d h85 (j := 63) (by omega)
  exact Seg.of_len (h1.comp (seg_cast h2 rfl (by omega))) rfl

/-! ### The loop's loads -/

/-- The guarded load `j` of the loop is skipped where `%p92` is false. -/
theorem seg_skipLoadN (d : D) (h92 : valueOf L g d 92 = .pred false) {j : Nat} (hj : j < 64) :
    Seg kernel asms L g 1 (1124 + 2 * j) (factsAt L g (1124 + 2 * j) d) (1125 + 2 * j)
      (factsAt L g (1125 + 2 * j) d) := by
  obtain ⟨a, hc, -⟩ := loadAt_spec (loadAt_nxt j hj)
  have hp : (92, Value.pred false) ∈ factsAt L g (1124 + 2 * j) d := by
    have := Flow.mem_factsFrom (val := valueOf L g d) (live_nxt j hj)
    rwa [h92] at this
  have h := Seg.skip (K := kernel) (A := asms) (L := L) (g := g) hc hp rfl
  exact seg_cast (h.weaken_end fun R hR => Flow.holds_factsFrom_mono hR (live_skipNxt j hj))
    rfl (by omega)

/-- Loop load `j` is skipped, and the zero fill of the next destination runs. -/
theorem seg_skipStepN (d : D) (h92 : valueOf L g d 92 = .pred false) (hcv : d.cv = 0) {j : Nat}
    (hj : j < 63) :
    Seg kernel asms L g 2 (1124 + 2 * j) (factsAt L g (1124 + 2 * j) d) (1124 + 2 * (j + 1))
      (factsAt L g (1124 + 2 * (j + 1)) d) := by
  have h1 := seg_skipLoadN (L := L) (g := g) d h92 (j := j) (by omega)
  have h2 := seg_fillN (L := L) (g := g) d (j := j) hj (by simp [D.vd, hcv])
  have h2' := seg_end (h2.weaken_end fun R hR => Flow.holds_factsFrom_mono hR (live_afterN j hj))
    (by omega : 1125 + 2 * j + 1 = 1124 + 2 * (j + 1))
  exact Seg.of_len (h1.comp h2') rfl

/-- **Every guarded loop load is skipped** where `%p92` is false. -/
theorem seg_skipNxtFrom (d : D) (h92 : valueOf L g d 92 = .pred false) (hcv : d.cv = 0) :
    ∀ m, m ≤ 63 →
      Seg kernel asms L g (2 * m) 1124 (factsAt L g 1124 d) (1124 + 2 * m)
        (factsAt L g (1124 + 2 * m) d) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih =>
    exact fun hm => Seg.of_len ((ih (by omega)).comp (seg_skipStepN d h92 hcv (j := m) (by omega)))
      (by omega)

/-- **The loop loads of a masked lane** (pcs 1124 to 1256): all skipped, to the `s_ready` poll. -/
theorem seg_skipNxt (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) (hi : d.i ≤ d.e.r26)
    (h92 : valueOf L g d 92 = .pred false) (hcv : d.cv = 0) :
    Seg kernel asms L g 133 1124 (factsAt L g 1124 d) 1257 (factsAt L g 1257 d) := by
  have h1 := seg_skipNxtFrom d h92 hcv 63 (le_refl 63)
  have h2 := seg_skipLoadN d h92 (j := 63) (by omega)
  have h3 := (h1.comp (seg_cast h2 rfl (by omega))).comp (seg_toWaitS d hT hok hi)
  exact Seg.of_len h3 rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
