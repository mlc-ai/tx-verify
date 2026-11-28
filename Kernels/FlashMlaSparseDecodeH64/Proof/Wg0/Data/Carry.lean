-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.CarryBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.ScalStore

@[expose] public section

/-! # The carried statistics along the trace

`CarryW sc l d`: at a state of the chain after the set-up, the carried words of the block in
progress (`d.b.m`, `d.b.l`, `d.b.mx`: `%r2492`, `%r2497`, `%r2427`) read as the statistics after
the blocks finished since the arrival at pc `w0ArrLPc` (`w0Carry`), the true maximum as an
extended real. `carryW_step`: one event keeps it. At `arrL` the words restart (`mI`, `lI`,
`mxI`); at `arrS` the block's value (`w0_block`, from the words `InvW` gives and the valid rows
`W0Valid`) becomes the carry; elsewhere the words stay. The carried sum is also a scalar word
(`Scal`), so its bytes rebuild to itself. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem f32Value_mI : (f32Value 4048155338).isSome = true := by
  simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.width, FVal.num]

theorem w0_rd_mI : Rd mI (w0M0 : EReal) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp f32Value_mI
  have h : valFloat .f32 mI = .ok (q : ℝ) := valFloat_b32 (by norm_num) hq
  have hc : Clean mI := ⟨rfl, fun _ _ _ => by simp [mI], fun w x hx => by
    simp only [mI, w32, Value.bits.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    simp [BitVec.toNat_ofNat]⟩
  unfold w0M0
  rw [show Value.bits 32 (BitVec.ofNat 64 4048155338) = mI from rfl, w0F_of_valFloat h]
  exact rd_of_valFloat hc h

theorem w0_rd_lI : Rd lI ((0 : ℝ) : EReal) := by
  have h : valFloat .f32 lI = .ok 0 := valFloat_zero
  have hc : Clean lI := ⟨rfl, fun _ _ _ => by simp [lI], fun w x hx => by
    simp only [lI, w32, Value.bits.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    simp⟩
  exact rd_of_valFloat hc h

theorem w0_rd_mxI : Rd mxI ⊥ := rd_negInf

/-- The carried statistics of a state (valid rows). -/
def CarryW (sc : ℝ) (l : List Event) (d : D) : Prop :=
  d.ok = true → earlyS d.c.site = false →
    Rd d.b.m ((w0Carry sc (w0Fin l).1).1 : EReal) ∧ Rd d.b.l ((w0Carry sc (w0Fin l).1).2 : EReal) ∧
      Rd d.b.mx (w0MxCarry sc (w0Fin l).1) ∧ Scal d.b.l

theorem isStart_early {s : Site} (h : isStart s = true) : earlyS s = true := by
  cases s <;> simp [isStart, earlyS] at h ⊢

/-- A block's end (`arrS`): the carry moves to the next block's start. -/
theorem carryW_arrS {sc : ℝ} {l : List Event} {d : D} {c' : Control.D} {e : Event}
    (hx : Rd (.bits 32 (scX L)) (sc : EReal)) (hI : InvW l d) (hC : CarryW sc l d)
    (hs : d.c.site = .arrS) (hpc : e.pc = d.c.site.pc) (hv : W0Valid sc (l ++ [e])) :
    CarryW sc (l ++ [e]) (dataNext L d c' e) := by
  have hp : e.pc = w0ArrSPc := by rw [hpc, hs]; rfl
  intro hok _
  simp only [dataNext, hs] at hok ⊢
  obtain ⟨hm, hl, hmx, -⟩ := hC hok (by rw [hs]; rfl)
  have hfin : w0Fin (l ++ [e]) = ((w0Fin l).1 ++ [(w0Fin l).2], []) := by
    rw [w0Fin_snoc]; simp [hp]
  have hw : W0Ok sc (w0Words (w0Fin l).2) :=
    hv.now.1 _ (by rw [hfin]; simp)
  have hb : BlkIs d.b (w0Words (w0Fin l).2) := by
    rw [w0Fin_snd]
    exact ⟨hI.hi, hI.mw, hI.pw, hI.pm, hI.vt⟩
  obtain ⟨h1, h2, -, h4⟩ := w0_block hw hx hb hm hl hmx
  rw [hfin, w0Carry_snoc]
  have e1 : ∀ r' ∈ [2951, 467, 3243, 2950, 2955, 2885, 2880],
      lookupD (wF (scX L) .arrS d.b) r' = blkOst (scX L) d.b r' := by
    intro r' hr'
    unfold wF wcls
    exact lookupD_factsFrom hr'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1 2950 (by decide)]; exact h1
  · rw [e1 2955 (by decide)]; exact h2
  · rw [e1 2885 (by decide), w0MxCarry_snoc]; exact h4
  · rw [e1 2955 (by decide)]; exact scal_blkOst_l _ _

/-- **One event keeps the carried statistics.** -/
theorem carryW_step {sc : ℝ} {l : List Event} {d : D} {c' : Control.D} {e : Event}
    (hx : Rd (.bits 32 (scX L)) (sc : EReal)) (hI : InvW l d) (hC : CarryW sc l d)
    (hpc : e.pc = d.c.site.pc) (_hc : Control.succ P L g w d.c e = some (some c'))
    (hv : W0Valid sc (l ++ [e])) : CarryW sc (l ++ [e]) (dataNext L d c' e) := by
  by_cases hs : d.c.site = .arrS
  · exact carryW_arrS hx hI hC hs hpc hv
  intro hok hearly
  rw [dataNext_eq hs] at hok hearly ⊢
  simp only at hok hearly ⊢
  have hsucc : succOk d.c c' = true := (Bool.and_eq_true_iff.mp hok).2
  have h1 : (isStart d.c.site || d.ok) = true := (Bool.and_eq_true_iff.mp hok).1
  by_cases harr : d.c.site = .arrL
  · have hp : e.pc = w0ArrLPc := by rw [hpc, harr]; rfl
    have hn : ¬ e.pc = w0ArrSPc := by rw [hp]; unfold w0ArrLPc w0ArrSPc; decide
    have hne : ¬ (w0ArrLPc = w0ArrSPc) := by unfold w0ArrLPc w0ArrSPc; decide
    have hfin : (w0Fin (l ++ [e])).1 = [] := by
      rw [w0Fin_snoc]; simp [hp, hne]
    obtain ⟨a, b, c⟩ := record_arrL (e := e) (b := d.b) harr
    rw [hfin, a, b, c]
    exact ⟨w0_rd_mI, w0_rd_lI, w0_rd_mxI, scal_bits _ _⟩
  · have hn200 : ¬ e.pc = w0ArrLPc := fun h => harr (site_pc_200 (hpc ▸ h))
    have hn1122 : ¬ e.pc = w0ArrSPc := fun h => hs (site_pc_1122 (hpc ▸ h))
    have hfin : (w0Fin (l ++ [e])).1 = (w0Fin l).1 := by
      rw [w0Fin_snoc]; simp [hn1122, hn200]
    have he : earlyS d.c.site = false := (succOk_back hsucc hearly).resolve_right harr
    have hok' : d.ok = true := by
      rcases Bool.or_eq_true_iff.mp h1 with h | h
      · rw [isStart_early h] at he; cases he
      · exact h
    obtain ⟨a, b, c⟩ := record_stats (e := e) (b := d.b) harr
    rw [hfin, a, b, c]
    exact hC hok' he

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
