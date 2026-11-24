-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaExit
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaWarp
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsAccessRoles
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsBar2
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsTmemAlloc
public import Kernels.FlashAttn4Fwd.Proof.Interface.Output

@[expose] public section

/-! # The named barriers and accesses of warps 12-15

* **Named barriers.** Only warps 0-12 make named-barrier events (`Cross.bar_warp13`), and warp
  12's are its two `bar.sync 2, 416` (`mma_bar_event`): the part of `StatsFacts.bar_form` for
  warps 12-15.
* **Accesses.** Only warps 0-12 access memory (`Cross.access_warp13`). Warp 12's accesses are of
  the four bytes of the base word at `+328` (`mma_access`), and a softmax thread's are its 4-byte
  stores of its statistics word, below `+1356` (`soft_wr`). Neither reaches the statistics words
  at `+332` (warp 12) or the staging buffers at `+3072`: the parts of
  `StatsFacts.stats_access` for warps 12-15 and of `OutputFacts.staging_access` for the warps
  other than 8-11. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- `StatsFacts.bar_form`, warps 12-15: warp 12's named-barrier events are `bar.sync 2, 416`,
and warps 13-15 make none. -/
theorem StatsFacts_bar_form_high :
    ∀ {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads → 12 ≤ warpOf L g →
      X.get (g, i) = some ⟨pc, .bar id cnt m⟩ → (id = 2 ∧ cnt = some 416) ∨
        (cnt = some 64 ∧ ((warpOf L g < 8 ∧ id = warpOf L g + 3 ∧ m = .arrive) ∨
          (8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ (id = warpOf L g - 5 ∨ id = warpOf L g - 1) ∧
            m = .sync))) := by
  intro g i pc id cnt m _ hw he
  have h13 := Cross.bar_warp13 hpre hX ht he
  rcases mma_bar_event hpre hX ht (by omega) he rfl with ⟨h, -⟩ | ⟨h, -⟩ <;>
    simp only [Event.mk.injEq, Kind.bar.injEq] at h <;> exact .inl ⟨h.2.1, h.2.2.1⟩

/-- A memory access of warp 12 covers only bytes below `+332`. -/
theorem mma_access_lt {g k : Nat} {a : Acc} {w : Bool} {l : Loc} (hw : warpOf L g = 12)
    (hA : X.Access (g, k) a w) (hc : a.Covers l) : l.addr < L.sharedBase + 332 := by
  obtain ⟨hloc, hsz⟩ := mma_access hpre hX ht hw hA
  obtain ⟨-, -, -, h⟩ := hc
  rw [hloc, hsz] at h
  simp only [Mma.baseAt] at h
  omega

/-- `StatsFacts.stats_access`, warps 12-15: none of their accesses covers a statistics word. -/
theorem StatsFacts_stats_access_high :
    ∀ {g i : Nat} {a : Acc} {w : Bool} {l : Loc}, g < L.threads → 12 ≤ warpOf L g →
      X.Access (g, i) a w → a.Covers l → InStatsArea L l →
        (warpOf L g < 8 ∧ SoftStore L X g i a w) ∨
          (8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ ∃ st < 2, CorrLoad L X g i a w st) := by
  intro g i a w l _ hw hA hc hin
  have h13 := Cross.access_warp13 hpre hX ht hA
  have hlt := mma_access_lt hpre hX ht (by omega) hA hc
  exact absurd hin.2.1 (by omega)

/-- A memory access of a softmax thread covers only bytes below `+1356`. -/
theorem soft_access_lt {g k : Nat} {a : Acc} {w : Bool} {l : Loc} (hw : warpOf L g < 8)
    (hA : X.Access (g, k) a w) (hc : a.Covers l) : l.addr < L.sharedBase + 1356 := by
  rcases Cross.access_rw hX hA with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩
  · exfalso
    obtain ⟨d, t, ins, o, -, -, -, -, -, -, hev⟩ :=
      soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
    obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
    cases site <;> simp [Softmax.Ev] at hev
  · obtain ⟨d, -, -, -, hl, hsz, -⟩ := soft_wr hpre hX ht hw he
    obtain ⟨-, -, -, h⟩ := hc
    rw [hl, hsz] at h
    have hb := hpre.block
    simp only [Softmax.sb, Softmax.tidOf] at h
    simp only [warpOf] at hw
    omega

/-- `OutputFacts.staging_access`, warps other than 8-11: none of their accesses covers a staging
byte. -/
theorem OutputFacts_staging_access_other :
    ∀ {g i : Nat} {a : Acc} {w : Bool} {l : Loc}, g < L.threads →
      ¬ (8 ≤ warpOf L g ∧ warpOf L g < 12) → X.Access (g, i) a w → a.Covers l →
      InStaging L l →
        8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ w = true ∧ ∃ st < 2, CorrStage L X g i a st := by
  intro g i a w l _ hw hA hc hin
  exfalso
  have h13 := Cross.access_warp13 hpre hX ht hA
  have h1 := hin.2.1
  by_cases h8 : warpOf L g < 8
  · have := soft_access_lt hpre hX ht h8 hA hc
    omega
  · have := mma_access_lt hpre hX ht (by omega) hA hc
    omega

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
