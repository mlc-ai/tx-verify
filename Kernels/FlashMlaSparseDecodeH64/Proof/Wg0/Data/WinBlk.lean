-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EpiRd
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.RescaleCond
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StrictEpi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WinCanon
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.CondBlkA
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.CondEs0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.CondEs1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.CondEs2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.CondEs3

@[expose] public section

/-! # The conditions of the windows at the sink, the mask, the stores of the peer packs

The fields `w156`, `w289`, `w403` to `w475` of `WinCond`, from the typed words of the event and
the valid block behind the state (`WCtx.canon`). -/

/-! # The conditions of the epilogue's runs at their stages

`w0k_<run>`: the run's condition (no outcome is a fault) at the facts the run starts from, given
the words the valid trace gives (`W0EpiOk`): the carried statistics, the sink word and the raw
sink load, the peer's row-sum word, the accumulator words. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

/-- The condition of output chunk `c`'s run. -/
def EsCond (c : Fin 4) (V : Nat → Value) : Prop :=
  match c with
  | 0 => es0_cond V
  | 1 => es1_cond V
  | 2 => es2_cond V
  | 3 => es3_cond V

/-- The sink run: the raw word reads as a number. -/
theorem w0k_sk (x : BitVec 64) (sk v : Value) {y : EReal} (hv : Rd v y) :
    sk_cond (lookupD (s_sink x sk v)) :=
  sk_cond_of_reads _ (by simpa [s_sink, f_set, lookupD, List.lookup] using hv)

/-- The first run of the epilogue (pcs 1147-1153). -/
theorem w0k_e1 (W : Nat → Value) {ps : Nat} {r : EReal} {m l : ℝ}
    (h452 : W 452 = .bits 16 (BitVec.ofNat 64 ps)) (hr : Rd (W 2885) r) (hm : Rd (W 2950) m)
    (hl : Rd (W 2955) l) : e1_cond W :=
  e1_cond_of_reads W h452 hr hm.1.1 hl.1.1

/-- The final sum (pc 1158). -/
theorem w0k_e3 (V : Nat → Value) (pe : Value) {r : EReal} {m l p : ℝ}
    (hr : Rd (V 2885) r) (hm : Rd (V 2950) m) (hl : Rd (V 2955) l) (hp : Rd pe p) :
    e3_cond (f_ex1 V pe) :=
  e3_cond_of_reads _ (w0e_e1 V hr hm hl).2 hp

/-- The sum is a real and the maximum reads as a number at the facts of the final sum. -/
theorem w0k_ew (V : Nat → Value) (pe : Value) {r : EReal} {m l p : ℝ}
    (hr : Rd (V 2885) r) (hm : Rd (V 2950) m) (hl : Rd (V 2955) l) (hp : Rd pe p) :
    lookupD (f_ew V pe) 482 = .float .f32 (w0ESum r l + p) ∧
      Rd (lookupD (f_ew V pe) 481) (w0EMax r m) :=
  ⟨w0e_e3_eq (f_ex1 V pe) (a := w0ESum r l) (w0e_e1 V hr hm hl).2 hp, (w0e_e1 V hr hm hl).1⟩

/-- The logarithm run (pcs 1162-1166). -/
theorem w0k_e4 (V : Nat → Value) (pe : Value) {r : EReal} {m l p : ℝ}
    (hr : Rd (V 2885) r) (hm : Rd (V 2950) m) (hl : Rd (V 2955) l) (hp : Rd pe p)
    (hl0 : 0 ≤ l) (hp0 : 0 ≤ p) : e4_cond (lookupD (f_ew V pe)) := by
  obtain ⟨h482, h481⟩ := w0k_ew V pe hr hm hl hp
  have h0 : 0 ≤ w0ESum r l := by unfold w0ESum; split_ifs <;> first | exact le_rfl | exact hl0
  exact e4_cond_of_reads _ h482 h481 (by positivity)

/-- The zero-sum test (pcs 1189-1190). -/
theorem w0k_e5 (V : Nat → Value) (pe : Value) {r : EReal} {m l p : ℝ}
    (hr : Rd (V 2885) r) (hm : Rd (V 2950) m) (hl : Rd (V 2955) l) (hp : Rd pe p) :
    e5_cond (lookupD (f_ew V pe)) := by
  obtain ⟨h482, -⟩ := w0k_ew V pe hr hm hl hp
  exact e5_cond_of_reads _ (by rw [h482]; exact rd_float _)

/-- The factor's run on a non-zero sum (pcs 1192-1196). -/
theorem w0k_e6 (V : Nat → Value) (pe : Value) {r : EReal} {m l p : ℝ} {sk : EReal}
    (hr : Rd (V 2885) r) (hm : Rd (V 2950) m) (hl : Rd (V 2955) l) (hk : Rd (V 2880) sk)
    (hp : Rd pe p) (hl0 : 0 ≤ l) (hp0 : 0 ≤ p) (hrp : r = ⊥ → p = 0)
    (hne : w0ESum r l + p ≠ 0) : e6_cond (lookupD (f_ew V pe)) := by
  obtain ⟨h482, h481⟩ := w0k_ew V pe hr hm hl hp
  have h0 : 0 ≤ w0ESum r l := by unfold w0ESum; split_ifs <;> first | exact le_rfl | exact hl0
  have hr' : r ≠ ⊥ := fun h => hne (by simp [w0ESum, h, hrp h])
  have h481' : Rd (lookupD (f_ew V pe) 481) (w0EMax r m) := h481
  have hm' : Rd (lookupD (f_ew V pe) 481) m := by simpa [w0EMax, hr'] using h481'
  exact e6_cond_of_reads _ (s := w0ESum r l + p) (by rw [h482]; exact rd_float _) hm' hk
    (by positivity) hne

/-- The factor word's pair (pc 1199). -/
theorem w0k_e7 (V : Nat → Value) (pe : Value) {r : EReal} {m l p : ℝ} {sk : EReal}
    (hr : Rd (V 2885) r) (hm : Rd (V 2950) m) (hl : Rd (V 2955) l) (hk : Rd (V 2880) sk)
    (hp : Rd pe p) (hl0 : 0 ≤ l) (hp0 : 0 ≤ p) (hrp : r = ⊥ → p = 0) :
    e7_cond (lookupD [(2956, f_zj V pe)]) := by
  obtain ⟨h482, h481⟩ := w0k_ew V pe hr hm hl hp
  have h0 : 0 ≤ w0ESum r l := by unfold w0ESum; split_ifs <;> first | exact le_rfl | exact hl0
  have hzj : Rd (f_zj V pe) ((w0Fac (w0ESum r l + p) sk m : ℝ) : EReal) := by
    refine w0e_zj (lookupD (f_ew V pe)) (by rw [h482]; exact rd_float _) (fun hne => ?_) hk
      (by positivity)
    have hr' : r ≠ ⊥ := fun h => hne (by simp [w0ESum, h, hrp h])
    simpa [w0EMax, hr'] using h481
  exact e7_cond_of_reads _ (by simpa [lookupD] using hzj.1.1)

/-- The chunk's output run: the words the load returned and the factor pair. -/
theorem w0k_es (c : Fin 4) (V : Nat → Value) (pe : Value) (o : List Value) {r : EReal}
    {m l p : ℝ} {sk : EReal} {O : Nat → ℝ}
    (hr : Rd (V 2885) r) (hm : Rd (V 2950) m) (hl : Rd (V 2955) l) (hk : Rd (V 2880) sk)
    (hp : Rd pe p) (hl0 : 0 ≤ l) (hp0 : 0 ≤ p) (hrp : r = ⊥ → p = 0) (ho : o.length = 64)
    (hO : ∀ i < 64, Rd (o.getD i (.pred false)) (O i)) :
    EsCond c (lookupD (f_ow c.val V pe o)) := by
  have hc := w0e_fac V pe hr hm hl hk hp hl0 hp0 hrp
  have hc' : pairRead (lookupD (f_ow c.val V pe o) 3577) =
      some (.ok ((w0Fac (w0ESum r l + p) sk m : ℝ), (w0Fac (w0ESum r l + p) sk m : ℝ))) := by
    unfold f_ow
    rw [lk_head_mem (by simp only [f_fac, Gen.e7_facts1, List.map_cons, List.map_nil]; decide)]
    exact hc
  have hOw := ow_rd c V pe o ho hO
  fin_cases c
  · exact es0_cond_of_reads _ O hOw hc'
  · exact es1_cond_of_reads _ O hOw hc'
  · exact es2_cond_of_reads _ O hOw hc'
  · exact es3_cond_of_reads _ O hOw hc'

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}

/-- The word a read event at pc 289 leaves as the block's mask word. -/
theorem wmw_at (seg : List Event) {e : Event} {x : Acc} {bs : List (Option Byte)} {v : Value}
    (hp : e.pc = 289) (hk : e.kind = .rd x bs) (hv : rebuild 3 bs = .ok v) :
    (w0Words (seg ++ [e])).mw = v := by
  simp [w0Words, w0Last_snoc, hp, w0RdVal, hk, hv, Except.toOption]

/-- The word a read event at pc 572 leaves as the peer's row maximum. -/
theorem wpm_at (seg : List Event) {e : Event} {x : Acc} {bs : List (Option Byte)} {v : Value}
    (hp : e.pc = 572) (hk : e.kind = .rd x bs) (hv : rebuild 3 bs = .ok v) :
    (w0Words (seg ++ [e])).pm = v := by
  simp [w0Words, w0Last_snoc, hp, w0RdVal, hk, hv, Except.toOption]

/-- **pc 156**: the sink load's word reads as a number. -/
theorem wc_156 (c : WCtx L g sc l d e) : d.c.site = .sink →
    ∀ x bs, e.kind = .nc x bs → ∃ y, rebuild 3 bs = .ok (.bits 32 y) ∧ Gen.sk_cond (lookupD
    (s_sink (scX L) d.b.sk (.bits 32 y))) := by
  intro hs x bs hk
  have hp : e.pc = 156 := by rw [c.hpc, hs]; rfl
  obtain ⟨bits, q, hb, hq, hr⟩ := c.hpay.sink x bs hk hp
  refine ⟨BitVec.ofNat 64 bits, hr, w0k_sk _ _ _ (y := ((q : ℝ) : EReal)) ?_⟩
  have h : valFloat .f32 (b32 bits) = .ok (q : ℝ) := valFloat_b32 (by omega) hq
  have hc : Clean (b32 bits) := ⟨rfl, fun _ _ _ => by simp [b32], fun w x hx => by
    simp only [b32, Value.bits.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    simp [BitVec.toNat_ofNat]
    omega⟩
  exact rd_of_valFloat hc h

/-- **pc 289**: the mask word is a 32-bit word and the peer packs' words are valid. -/
theorem wc_289 (c : WCtx L g sc l d e) : d.c.site = (.vm) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (Gen.mask_cond (lookupD (s_vm (scX
    L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (v)))) ∧ (Gen.pk394_cond (lookupD
    (m_vm (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (v)))) := by
  intro hs x bs hk
  have hp : e.pc = 289 := by rw [c.hpc, hs]; rfl
  obtain ⟨n, hn, hr⟩ := c.hpay.mask x bs hk hp
  obtain ⟨w', hw', hE, hlo, hhi, -, -, -⟩ := c.canon (by omega) (by omega)
  have h3 := hE.mw
  have hne : (w0Words ((w0Fin l).2 ++ [e])).mw ≠ .pred false := by
    rw [wmw_at _ hp hk hr]; nofun
  have hmw := h3.resolve_left hne
  rw [wmw_at _ hp hk hr] at hmw
  refine ⟨_, hr, ?_, ?_⟩
  · rw [hmw, hhi]; exact w0k_mask hw' _ _ _ _ _ _
  · rw [hmw, hhi, hlo]; exact w0k_pk394 hw' _ _ _ _ _

/-- **pc 403**. -/
theorem wc_403 (c : WCtx L g sc l d e) : d.c.site = (.pst 0) →
    Gen.pk404_cond (lookupD (f_pst0 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw))) := by
  intro hs
  have hp : e.pc = 403 := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, hhi, hmw, -, -⟩ := c.canon (by omega) (by omega)
  rw [hlo, hhi, hmw (by omega)]
  exact w0k_pk404 hw' _ _ _ _ _

/-- **pc 413**. -/
theorem wc_413 (c : WCtx L g sc l d e) : d.c.site = (.pst 1) →
    Gen.pk414_cond (lookupD (f_pst1 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw))) := by
  intro hs
  have hp : e.pc = 413 := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, hhi, hmw, -, -⟩ := c.canon (by omega) (by omega)
  rw [hlo, hhi, hmw (by omega)]
  exact w0k_pk414 hw' _ _ _ _ _

/-- **pc 423**. -/
theorem wc_423 (c : WCtx L g sc l d e) : d.c.site = (.pst 2) →
    Gen.pk424_cond (lookupD (f_pst2 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw))) := by
  intro hs
  have hp : e.pc = 423 := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, hhi, hmw, -, -⟩ := c.canon (by omega) (by omega)
  rw [hlo, hhi, hmw (by omega)]
  exact w0k_pk424 hw' _ _ _ _ _

/-- **pc 433**. -/
theorem wc_433 (c : WCtx L g sc l d e) : d.c.site = (.pst 3) →
    Gen.pk434_cond (lookupD (f_pst3 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw))) := by
  intro hs
  have hp : e.pc = 433 := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, hhi, hmw, -, -⟩ := c.canon (by omega) (by omega)
  rw [hlo, hhi, hmw (by omega)]
  exact w0k_pk434 hw' _ _ _ _ _

/-- **pc 443**. -/
theorem wc_443 (c : WCtx L g sc l d e) : d.c.site = (.pst 4) →
    Gen.pk444_cond (lookupD (f_pst4 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw))) := by
  intro hs
  have hp : e.pc = 443 := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, hhi, hmw, -, -⟩ := c.canon (by omega) (by omega)
  rw [hlo, hhi, hmw (by omega)]
  exact w0k_pk444 hw' _ _ _ _ _

/-- **pc 453**. -/
theorem wc_453 (c : WCtx L g sc l d e) : d.c.site = (.pst 5) →
    Gen.pk454_cond (lookupD (f_pst5 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw))) := by
  intro hs
  have hp : e.pc = 453 := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, hhi, hmw, -, -⟩ := c.canon (by omega) (by omega)
  rw [hlo, hhi, hmw (by omega)]
  exact w0k_pk454 hw' _ _ _ _ _

/-- **pc 463**. -/
theorem wc_463 (c : WCtx L g sc l d e) : d.c.site = (.pst 6) →
    Gen.pk464_cond (lookupD (f_pst6 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw))) := by
  intro hs
  have hp : e.pc = 463 := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, hhi, hmw, -, -⟩ := c.canon (by omega) (by omega)
  rw [hlo, hhi, hmw (by omega)]
  exact w0k_pk464 hw' _ _ _ _ _

/-- **pc 475**. -/
theorem wc_475 (c : WCtx L g sc l d e) : d.c.site = (.bar1) →
    Gen.pk476_cond (lookupD (f_pst7 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw))) := by
  intro hs
  have hp : e.pc = 475 := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, hhi, hmw, -, -⟩ := c.canon (by omega) (by omega)
  rw [hlo, hhi, hmw (by omega)]
  exact w0k_pk476 hw' _ _ _ _ _ _

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
