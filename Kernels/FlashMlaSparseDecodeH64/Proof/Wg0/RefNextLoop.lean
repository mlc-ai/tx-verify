-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Nc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefBar

@[expose] public section

/-! # Warpgroup 0's reference invariant: the block's end, and every step

`next_arrS`: the arrival on the softmax-ready slot ends block `r`: the words become block
`r + 1`'s (`cnt_next`, `words_next`, `bi_next`), or, after the last block, the epilogue's with the
last block's score ring. `core_step` joins the sites; `ref_step` is the invariant's step. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem next_arrS : StepRef P L g w .arrS := by
  w0_arr_step
  simp only [Site.reg, Site.idx, Control.D.words, RefAt] at hJ
  obtain ⟨r, hl, ha, hr⟩ := hJ
  obtain ⟨h64, hR, hrR, hbi, hcnt, hvs, hpv, hsl, hps⟩ := hl
  dsimp only at h64 hR hrR hbi hcnt hvs hpv hsl hps
  subst hbi hcnt hvs hpv hsl hps
  obtain ⟨he, hc, hn1⟩ := cnt_next hrR hR
  obtain ⟨hv, hp, hs, hq⟩ := words_next r
  have hacq : ∀ l, Code.bump cls n e (.acq l) = acqCnt (objs L g) (r + 1) 0 none l := fun l => by
    rw [(hb l).1, ha l, acq_next]
  have harr : ∀ l, Code.bump cls n e (.arrive l) = arrCnt (objs L g) true (r + 1) 0 l :=
    fun l => by
      rw [(hb l).2, hr l, arr_next, so_eq]
  by_cases hlast : r + 1 = rounds l0 l1
  · simp only [advance, he, decide_eq_true hlast, ↓reduceIte, hc, hn1] at hn
    simp only [hlast, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ↓reduceIte] at hn
    obtain rfl := some_some_eq hn
    simp only [Site.reg, Site.idx, Control.D.words, RefAt, EpiOk, ← hlast, Nat.add_sub_cancel]
    refine ⟨?_, hacq, harr⟩
    constructor <;> trivial
  · simp only [advance, he, hlast, decide_false, Bool.false_eq_true, ↓reduceIte, hc, hn1, ne_eq,
      not_false_eq_true, decide_true, hv, hp, hs, hq, bi_next (by omega : r < 2 ^ 26)] at hn
    obtain rfl := some_some_eq hn
    simp only [Site.reg, Site.idx, Control.D.words, RefAt]
    exact ⟨r + 1, ⟨h64, hR, by dsimp only; omega, rfl, rfl, rfl, rfl, rfl, rfl⟩, hacq, harr⟩

/-- **`RefCore` is kept by every step** on an event of the state's kind that is not undefined
behaviour. -/
theorem core_step (hb : scmp .ge .s (r2W L g) (pw P.b) = false) {d d' : D} {n : Cnt → Nat}
    {e : Event} (hpc : inRole e = true)
    (hu : ∀ f, e.kind ≠ .ub f) (hJ : RefCore L g d n) (hev : EvK P L g w d e)
    (hn : succ P L g w d e = some (some d')) : RefCore L g d' (Code.bump cls n e) := by
  have h : StepRef P L g w d.site := by
    cases hs : d.site.mb
    · exact next_plain hb hs
    · revert hs
      cases d.site <;> intro hs <;> simp only [Site.mb, Bool.false_eq_true] at hs
      · exact next_arrL
      · exact next_wv
      · exact next_wq
      · exact next_arrV
      · exact next_arrS
      · exact next_wsv
  exact h d n e d' rfl hpc hu hJ hev hn

/-- Every site but the return is in the role's code. -/
theorem Site.pc_lt (s : Site) (hs : s ≠ .exit) : 103 ≤ s.pc ∧ s.pc < 1842 := by
  cases s with
  | sld a k => revert a k; decide
  | pst k | pld k => revert k; decide
  | ost c | rld c | rldw c | rst c | rstw c | old c | oldw c | ofpx c | obar c | oel c
    | otma c => revert c; decide
  | ost2 c k => revert c k; decide
  | exit => exact absurd rfl hs
  | _ => exact ⟨by decide, by decide⟩

/-- An event the machine follows is at a pc of the role. -/
theorem inRole_of_next {d d' : D} {e : Event} (hpc : e.pc = d.site.pc)
    (hn : succ P L g w d e = some (some d')) : inRole e = true := by
  have hx : d.site ≠ .exit := by
    intro h
    simp [succ, h] at hn
  have := Site.pc_lt _ hx
  simp only [inRole, hpc, decide_eq_true_eq]
  omega

/-- **The reference invariant is kept by every step** the machine follows. -/
theorem ref_step {m : Mem0} (hp : Pre P L m) {d d' : D} {n : Cnt → Nat} {e : Event}
    (hJ : Ref P L g d n) (hev : Ev P L g w d e) (hok : LenOk P L g d e)
    (hn : succ P L g w d e = some (some d')) :
    Ref P L g d' (Code.bump cls n e) := by
  intro h0
  have hn0 : n .ub = 0 := by
    simp only [Code.bump] at h0
    omega
  have hpc := inRole_of_next hev.1 hn
  by_cases hu : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hu
    simp [Code.bump, cls, hpc, kindOf, hf] at h0
  · obtain ⟨hc, hl, hB⟩ := hJ hn0
    have hb := batch_in hp g
    exact ⟨core_step hb hpc (fun f h => hu ⟨f, h⟩) hc hev.2 hn, launch_step hp hl hok hn,
      bar_step hb hpc (fun f h => hu ⟨f, h⟩) hc hB hev.2 hn⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
