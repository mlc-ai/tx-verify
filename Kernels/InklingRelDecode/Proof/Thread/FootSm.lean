-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSAll

@[expose] public section

/-!
# The footprint of the softmax region's shared store

`Sm.Site.store10` is the one shared store of the softmax region: a warp's minimum of the rescale
factors is written to `sharedBase + 212992 + 4 (warp % 4)` of the thread's CTA, four bytes, and the
four minima are read back after `bar.sync 0, 128`. **These four words overlap the pair
`(num_pre, num_iters)` of the prologue** (`[sharedBase + 212992, sharedBase + 213000)`: warp 0's
word is `num_pre`, warp 1's is `num_iters`) **and extend past it** (`[sharedBase + 213000,
sharedBase + 213008)` is in no region of `Safety.Regions`). `shape_store10_foot` is the footprint;
`store10_range` is that it lies in `[sharedBase + 212992, sharedBase + 213008)`.

The value stored is the minimum the machine keeps (`D.stg.cm4`), which the footprint does not
need.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- **A shared 32-bit store through a register writes its four bytes at the register's
address.** The same as `EvD.fires_st_reg` without the value of the source: a continuing event is a
write at `a + 4 j` of the thread's CTA, whatever the stored bytes are. -/
theorem fires_st_reg_loc {A : List Assumption} {pc : Nat} {t : TState} {vec base a j : Nat}
    {srcs : List Opnd} {u : TState} (hsub : t.sub = j) (hr : t.regs base = some (b32 a))
    (ha : a < 2 ^ 32) (hj : j < srcs.length) (hl : srcs.length = vec)
    (hvec : vec = 1 ∨ vec = 2 ∨ vec = 4)
    (hf : Fires pc (eventTmpl A L g t (.mem (sstoreV vec base srcs))) e (some u)) :
    ∃ bs, e = ⟨pc, .wr (wordAcc ⟨.shared, g / L.block, a + 4 * j⟩ j) bs⟩ := by
  have hrule : (sstoreV vec base srcs).rule = some .threadAccess := by
    unfold sstoreV
    rcases hvec with rfl | rfl | rfl <;> simp [MemAccess.rule, memTypeOk, DType.width, hl]
  have hloc : (sstoreV vec base srcs).locSpace? = some .shared := by
    unfold sstoreV; rfl
  rw [eventTmpl, memTmpl_store hrule hloc rfl rfl rfl] at hf
  have hww : (sstoreV vec base srcs).elem.width = 32 := rfl
  have hoff : (sstoreV vec base srcs).addr.off = 0 := rfl
  have hsrc : (sstoreV vec base srcs).srcs = srcs := rfl
  rw [hww, hoff, hsrc] at hf
  change Fires pc (storeTmpl L g t .shared 32 base 0 srcs) e (some u) at hf
  unfold storeTmpl at hf
  rw [effAddr_b32 hr ha] at hf
  have ho : srcs[j]? = some srcs[j] := List.getElem?_eq_getElem hj
  simp only [bind, Except.bind, hsub, elemAcc] at hf
  have hv8 : ¬ (32 / 8 = 0) := by decide
  by_cases hal : a % (32 / 8 * srcs.length) = 0
  · simp only [hv8, hal, ne_eq, not_true_eq_false, false_or, ↓reduceIte, pure, Except.pure,
      ho, Loc.at] at hf
    rcases hrv : readValue L g t 32 srcs[j] with f | v
    · simp only [hrv, Fires] at hf
      exact absurd hf.2 (by simp)
    · simp only [hrv] at hf
      rcases hsv : storeValue 32 v with f | v'
      · simp only [hsv, Fires] at hf
        exact absurd hf.2 (by simp)
      · simp only [hsv, Fires] at hf
        exact ⟨v'.toBytes, by rw [hf.1]; rfl⟩
  · simp only [hv8, hal, ne_eq, not_false_eq_true, false_or, ↓reduceIte, throw, throwThe,
      MonadExceptOf.throw, Fires] at hf
    exact absurd hf.2 (by simp)

theorem store10_code : kernel.code[2250]? = some ⟨none, .mem (sstoreV 1 1533 [.reg 1534])⟩ :=
  Flow.code_store_10

/-- **The softmax region's shared store.** The write of the four bytes at
`sharedBase + 212992 + 4 (warp % 4)` of the thread's CTA. -/
theorem shape_store10_foot (hS : SharedOk L) (hF : Fired L g d e (some u))
    (hs : d.site = .store10) :
    ∃ bs, e = ⟨evPc d.site, .wr (wordAcc ⟨.shared, g / L.block,
      L.sharedBase + 212992 + g % L.block / 32 % 4 * 4⟩) bs⟩ := by
  have hpc : d.site.pc = 2250 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact store10_code) hF
  rw [hpc] at hf
  have hr : t.regs 1533 =
      some (b32 ((L.sharedBase + 212992 + g % L.block / 32 % 4 * 4) % 2 ^ 32)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  have hsub : t.sub = 0 := by
    have h2 := h.2.1
    exact h2
  have hlt : L.sharedBase + 212992 + g % L.block / 32 % 4 * 4 < 2 ^ 32 := by
    have := hS.2
    omega
  have hmod : (L.sharedBase + 212992 + g % L.block / 32 % 4 * 4) % 2 ^ 32 =
      L.sharedBase + 212992 + g % L.block / 32 % 4 * 4 := Nat.mod_eq_of_lt hlt
  rw [hmod] at hr
  obtain ⟨bs, he⟩ := fires_st_reg_loc (vec := 1) (srcs := [.reg 1534]) hsub hr hlt (by simp)
    rfl (by simp) hf
  exact ⟨bs, by rw [he, evPc, hpc]; simp⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
