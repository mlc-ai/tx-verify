-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.FootSm
public import Kernels.InklingRelDecode.Proof.Thread.SmStgD
public import Kernels.InklingRelDecode.Proof.Thread.SmFlt

@[expose] public section

/-!
# The scratch words of the softmax region: event shapes and the order of the sites

What the memory argument of the scratch words needs from the softmax region's machine:

* `shape_bar22`, `shape_bar23`, `shape_bar24`: `bar.sync 0, 128` (as `shape_bar20`);
* `shape_store10_val`: the shared store writes the bytes of the stored minimum `D.stg.cm4`;
* `rank`: a number of each state, `64 i` plus the place of its site in the loop; `next_rank`: a
  successor's rank is at least the state's (the loop counter rises only at `bar21` and `arrive`,
  to a site at the loop's top);
* `prev_shfl11`, `prev_ldL`, `prev_bar23`: the state before `shfl11` is at `ldL`, before `ldL` at
  `bar23`, before `bar23` at `store10`, all of the same iteration.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-! ### Event shapes -/

theorem shape_bar22 (hb : L.block ≠ 128) (hF : Fired L g d e (some u)) (hs : d.site = .bar22) :
    e = ⟨evPc d.site, .bar 0 (some 128) .sync⟩ := by
  have hpc : d.site.pc = 2241 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_bar_22) hF
  rw [hpc] at hf
  rw [fires_barSyncN_128 hb hf, evPc, hpc]

theorem shape_bar23 (hb : L.block ≠ 128) (hF : Fired L g d e (some u)) (hs : d.site = .bar23) :
    e = ⟨evPc d.site, .bar 0 (some 128) .sync⟩ := by
  have hpc : d.site.pc = 2251 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_bar_23) hF
  rw [hpc] at hf
  rw [fires_barSyncN_128 hb hf, evPc, hpc]

theorem shape_bar24 (hb : L.block ≠ 128) (hF : Fired L g d e (some u)) (hs : d.site = .bar24) :
    e = ⟨evPc d.site, .bar 0 (some 128) .sync⟩ := by
  have hpc : d.site.pc = 2326 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_bar_24) hF
  rw [hpc] at hf
  rw [fires_barSyncN_128 hb hf, evPc, hpc]

/-- **The softmax region's shared store, with its bytes**: the write of the stored minimum
`D.stg.cm4` at `sharedBase + 212992 + 4 (warp % 4)` of the thread's CTA. -/
theorem shape_store10_val (hS : SharedOk L) (hF : Fired L g d e (some u))
    (hs : d.site = .store10) :
    ∃ v, storeValue 32 d.stg.cm4 = .ok v ∧ e = ⟨evPc d.site, .wr (wordAcc ⟨.shared, g / L.block,
      L.sharedBase + 212992 + g % L.block / 32 % 4 * 4⟩ 0) v.toBytes⟩ := by
  have hpc : d.site.pc = 2250 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact store10_code) hF
  rw [hpc] at hf
  have hr : t.regs 1533 =
      some (b32 ((L.sharedBase + 212992 + g % L.block / 32 % 4 * 4) % 2 ^ 32)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  have hv : t.regs 1534 = some d.stg.cm4 := by
    rw [reg_at h (by rw [hpc]; decide +kernel), valueOf_cm4]
  have hsub : t.sub = 0 := h.2.1
  have hlt : L.sharedBase + 212992 + g % L.block / 32 % 4 * 4 < 2 ^ 32 := by
    have := hS.2
    omega
  have hmod : (L.sharedBase + 212992 + g % L.block / 32 % 4 * 4) % 2 ^ 32 =
      L.sharedBase + 212992 + g % L.block / 32 % 4 * 4 := Nat.mod_eq_of_lt hlt
  rw [hmod] at hr
  obtain ⟨v, hsv, he⟩ := fires_st_reg (vec := 1) (srcs := [.reg 1534]) (o := .reg 1534) rfl hsub
    hr hlt (by simp) (readValue_reg hv) (by simp) (by simp) hf
  exact ⟨v, hsv, by rw [he, evPc, hpc]; simp⟩

/-! ### The order of the sites -/

/-- The place of a site in the loop. -/
def Site.ord : Site → Nat
  | .setMaxReg => 0 | .bar0 => 1 | .pre _ => 2 | .nxt _ => 3 | .waitS => 4 | .shfl4 => 5
  | .ldS => 6 | .waitLd => 7 | .shfl5 => 8 | .shfl6 => 9 | .waitO => 10 | .bar22 => 11
  | .shfl7 => 12 | .shfl8 => 13 | .shfl9 => 14 | .shfl10 => 15 | .store10 => 16 | .bar23 => 17
  | .ldL => 18 | .shfl11 => 19 | .shfl12 => 20 | .ldO => 21 | .waitLdO => 22 | .bar24 => 23
  | .stO => 24 | .waitStO => 25 | .bar20 => 26 | .tmemSt => 27 | .tmemWait => 28 | .bar21 => 29
  | .arrive => 30

/-- The rank of a state: its iteration, then its site's place in the loop. -/
def D.rank (d : D) : Nat := 64 * d.i + d.site.ord

theorem afterSetup_rank {d d' : D} (h : afterSetup L g d = some (some d')) :
    d'.i = d.i ∧ (d'.site = .nxt 0 ∨ d'.site = .waitS) := by
  unfold afterSetup at h
  split at h
  · cases h
  · split at h <;> (simp only [Option.some.injEq] at h; subst h; simp)

theorem toBar20_rank {d d' : D} (h : toBar20 d = some (some d')) :
    d'.i = d.i ∧ d'.site = .bar20 := by
  unfold toBar20 at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · cases h

/-- **A successor's rank is at least the state's.** -/
theorem next_rank {d d' : D} (hn : next L g d e = some (some d')) : d.rank ≤ d'.rank := by
  unfold D.rank
  unfold next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all [Site.ord, D.afterSum]; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       simp_all [Site.ord, D.afterMax, D.afterMaxT]; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all [Site.ord, D.afterSum]; omega)
    | (obtain ⟨h1, h2 | h2⟩ := afterSetup_rank hn <;> simp_all [Site.ord] <;> omega)
    | (obtain ⟨h1, h2⟩ := toBar20_rank hn
       try simp only [D.afterSum] at h1
       rw [h1, h2]
       simp_all [Site.ord])
    | (obtain ⟨h1, h2⟩ := toBar20_rank hn
       try simp only [D.afterSum] at h1
       rw [h1, h2]
       simp_all [Site.ord]
       omega)
    | (unfold afterArrive at hn
       obtain ⟨h1, h2 | h2⟩ := afterSetup_rank hn <;> simp_all [Site.ord] <;> omega)

/-! ### The states before the load of the scratch word -/

theorem prev_shfl11 {d d' : D} (hn : next L g d e = some (some d')) (hs : d'.site = .shfl11) :
    d.site = .ldL ∧ d'.i = d.i := by
  unfold next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       simp_all [D.afterSum, D.afterMax, D.afterMaxT]; done)
    | (obtain ⟨-, h2 | h2⟩ := afterSetup_rank hn <;> simp_all; done)
    | (obtain ⟨-, h2⟩ := toBar20_rank hn; simp_all; done)
    | (unfold afterArrive at hn; obtain ⟨-, h2 | h2⟩ := afterSetup_rank hn <;> simp_all)

theorem prev_ldL {d d' : D} (hn : next L g d e = some (some d')) (hs : d'.site = .ldL) :
    d.site = .bar23 ∧ d'.i = d.i := by
  unfold next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       simp_all [D.afterSum, D.afterMax, D.afterMaxT]; done)
    | (obtain ⟨-, h2 | h2⟩ := afterSetup_rank hn <;> simp_all; done)
    | (obtain ⟨-, h2⟩ := toBar20_rank hn; simp_all; done)
    | (unfold afterArrive at hn; obtain ⟨-, h2 | h2⟩ := afterSetup_rank hn <;> simp_all)

theorem prev_bar23 {d d' : D} (hn : next L g d e = some (some d')) (hs : d'.site = .bar23) :
    d.site = .store10 ∧ d'.i = d.i := by
  unfold next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn
       simp_all [D.afterSum, D.afterMax, D.afterMaxT]; done)
    | (obtain ⟨-, h2 | h2⟩ := afterSetup_rank hn <;> simp_all; done)
    | (obtain ⟨-, h2⟩ := toBar20_rank hn; simp_all; done)
    | (unfold afterArrive at hn; obtain ⟨-, h2 | h2⟩ := afterSetup_rank hn <;> simp_all)

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
