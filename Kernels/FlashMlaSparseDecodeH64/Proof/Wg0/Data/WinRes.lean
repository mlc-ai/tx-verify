-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.ExitWin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.FacWin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumBlockFull
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.RescaleCond
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepEld
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WinBlk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RescaleFacts

@[expose] public section

/-! # The conditions of the windows of the rescale

The fields `w711` (the scale factor) and `w717` to `w1020` (the four chunks' products) of
`WinCond`, from the block the state has finished (`BlkIs`) and the accumulator words it loaded. -/

/-! # The conditions of the windows at the peer reads, the maximum exchange and the vote

The fields `w477` to `w512` (the peer pairs' sums and the row maximum), `w572` (the exchange)
and `w578` (the vote) of `WinCond`. -/

/-! # The conditions of the runs of a valid block: row maximum, exchange, vote, probabilities

At the stage each run starts from, given the words of a valid block and the statistics the block
starts from read as numbers (`w0_block_full`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

variable {sc : ℝ} {w : W0Words} {x : BitVec 64} {m l mx sk : Value} {lo : List Value}
  {mR lR : ℝ} {r0 : EReal}

/-- The condition of the row-maximum run. -/
theorem w0k_rmax (hw : W0Ok sc w) (hx : Rd (.bits 32 x) (sc : EReal)) (hm : Rd m (mR : EReal))
    (hl : Rd l (lR : EReal)) (hmx : Rd mx r0) :
    rmax_cond (lookupD (f_pld8 x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7))) := by
  obtain ⟨-, hr, -, -, -⟩ := w0_block_full hw hx hm hl hmx
  exact hr

/-- The condition of the maximum-exchange run. -/
theorem w0k_mld (hw : W0Ok sc w) (hx : Rd (.bits 32 x) (sc : EReal)) (hm : Rd m (mR : EReal))
    (hl : Rd l (lR : EReal)) (hmx : Rd mx r0) :
    mld_cond (lookupD (s_mld x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)) := by
  obtain ⟨-, -, hmld, -, -⟩ := w0_block_full hw hx hm hl hmx
  exact hmld

/-- The condition of the vote's run. -/
theorem w0k_vt (hw : W0Ok sc w) (hx : Rd (.bits 32 x) (sc : EReal)) (hm : Rd m (mR : EReal))
    (hl : Rd l (lR : EReal)) (hmx : Rd mx r0) :
    vt_cond (lookupD (f_vh x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm)) := by
  obtain ⟨-, -, -, hvt, -⟩ := w0_block_full hw hx hm hl hmx
  exact hvt

/-- The condition of the probabilities' run. -/
theorem w0k_pw (hw : W0Ok sc w) (hx : Rd (.bits 32 x) (sc : EReal)) (hm : Rd m (mR : EReal))
    (hl : Rd l (lR : EReal)) (hmx : Rd mx r0) :
    pw_cond (lookupD (f_join x m l mx sk lo w.hi w.mw (w.pw 0) (w.pw 1) (w.pw 2) (w.pw 3)
      (w.pw 4) (w.pw 5) (w.pw 6) (w.pw 7) w.pm w.vt)) := by
  obtain ⟨-, -, -, -, hpw⟩ := w0_block_full hw hx hm hl hmx
  exact hpw

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}

/-- The carried statistics of a state of the loop read as numbers. -/
theorem WCtx.carry (c : WCtx L g sc l d e) (hs : innerSite d.c.site = true)
    (he : earlyS d.c.site = false) :
    Rd d.b.m ((w0Carry sc (w0Fin l).1).1 : EReal) ∧ Rd d.b.l ((w0Carry sc (w0Fin l).1).2 : EReal) ∧
      Rd d.b.mx (w0MxCarry sc (w0Fin l).1) := by
  obtain ⟨h1, h2, h3, -⟩ := c.hC (c.hOk hs) he
  exact ⟨h1, h2, h3⟩

/-- A split word of the default is no finite number. -/
theorem w0Fin_split_pred : ¬ W0Fin (splitValue 64 (.pred false)).1 := by
  intro h
  obtain ⟨x, hx⟩ := h
  simp only [splitValue, valFloat] at hx
  rw [bitsAsFloat_eq (by intro f h; cases h)] at hx
  simp [Value.bitPattern] at hx

/-- **The pair a second read completes**: the pair `(a0, v)` is the valid block's pair `k`. -/
theorem WCtx.pair (c : WCtx L g sc l d e) {k : Nat} (hk : k < 8) (hp : e.pc = 477 + 5 * k)
    (hs : d.c.site = .pld ⟨k, hk⟩) (hel : d.c.el ≠ 0) {x : Acc} {bs : List (Option Byte)}
    (hkd : e.kind = .rd x bs) :
    ∃ v w', rebuild 3 bs = .ok v ∧ W0Ok sc w' ∧ d.b.lo = w'.lo ∧ d.b.hi = w'.hi ∧
      d.b.mw = w'.mw ∧ (∀ j < k, d.b.pw j = w'.pw j) ∧ (d.c.a0, v) = w'.pw k := by
  obtain ⟨v, hr, hf1, -⟩ := c.hpay.peer x bs hkd ⟨k, hk, hp⟩
  obtain ⟨w', hw', hE, hlo, hhi, hmw, hpw, -⟩ := c.canon (by omega) (by omega)
  have hel1 : d.c.el = 1 := by
    have h2 := c.hel
    rw [hs] at h2
    change d.c.el < 2 at h2
    omega
  have hpar := (c.hI.par ⟨k, hk⟩).mpr ⟨hs, hel1⟩
  obtain ⟨e0, hl0, ha0⟩ := c.hI.a0 ⟨k, hk⟩ hs hel1
  have hw : (w0Words ((w0Fin l).2 ++ [e])).pw k = (d.c.a0, v) := by
    simp only [w0Words, hk, ite_true, w0Peer_eq_pf, w0Pf_snoc]
    have hc : e.pc = 477 + 5 * k ∧ (w0RdVal e).isSome = true :=
      ⟨hp, by simp [w0RdVal, hkd, hr]⟩
    simp only [hc, and_self, ite_true]
    rw [w0Fin_snd]
    rw [w0PeerOf_odd_snoc _ _ e0 hpar hl0]
    simp [w0RdVal, hkd, hr, ha0, Except.toOption]
  have hne : (d.c.a0, v) ≠ ((.pred false, .pred false) : Value × Value) := by
    intro h
    have hv : v = .pred false := (Prod.mk.inj h).2
    rw [hv] at hf1
    exact w0Fin_split_pred hf1
  have h4 := hE.pw k hk
  rw [hw] at h4
  exact ⟨v, w', hr, hw', hlo, hhi, hmw (by omega), fun j hj => hpw j (by omega) (by omega),
    h4.resolve_left hne⟩

/-- **pc 477**. -/
theorem wc_477 (c : WCtx L g sc l d e) : d.c.site = (.pld 0) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum0_cond (lookupD
    (s_pld0 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw)
    (d.c.a0, v)))) := by
  intro hs x bs hk
  have hp : e.pc = 477 := by rw [c.hpc, hs]; rfl
  obtain ⟨v, hr, -⟩ := c.hpay.peer x bs hk ⟨0, by norm_num, by omega⟩
  refine ⟨v, hr, fun hel => ?_⟩
  obtain ⟨v', w', hr', hw', hlo, hhi, hmw, hpw, hpair⟩ := c.pair (k := 0) (by norm_num)
    (by omega) hs hel hk
  obtain rfl : v' = v := Except.ok.inj (hr'.symm.trans hr)
  rw [hhi, hmw, hpair]
  exact w0k_sum0 hw' _ _ _ _ _ _

/-- **pc 482**. -/
theorem wc_482 (c : WCtx L g sc l d e) : d.c.site = (.pld 1) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum1_cond (lookupD
    (s_pld1 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
    (d.c.a0, v)))) := by
  intro hs x bs hk
  have hp : e.pc = 482 := by rw [c.hpc, hs]; rfl
  obtain ⟨v, hr, -⟩ := c.hpay.peer x bs hk ⟨1, by norm_num, by omega⟩
  refine ⟨v, hr, fun hel => ?_⟩
  obtain ⟨v', w', hr', hw', hlo, hhi, hmw, hpw, hpair⟩ := c.pair (k := 1) (by norm_num)
    (by omega) hs hel hk
  obtain rfl : v' = v := Except.ok.inj (hr'.symm.trans hr)
  rw [hhi, hmw, hpw 0 (by norm_num), hpair]
  exact w0k_sum1 hw' _ _ _ _ _ _

/-- **pc 487**. -/
theorem wc_487 (c : WCtx L g sc l d e) : d.c.site = (.pld 2) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum2_cond (lookupD
    (s_pld2 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
      (d.b.pw 1)
    (d.c.a0, v)))) := by
  intro hs x bs hk
  have hp : e.pc = 487 := by rw [c.hpc, hs]; rfl
  obtain ⟨v, hr, -⟩ := c.hpay.peer x bs hk ⟨2, by norm_num, by omega⟩
  refine ⟨v, hr, fun hel => ?_⟩
  obtain ⟨v', w', hr', hw', hlo, hhi, hmw, hpw, hpair⟩ := c.pair (k := 2) (by norm_num)
    (by omega) hs hel hk
  obtain rfl : v' = v := Except.ok.inj (hr'.symm.trans hr)
  rw [hhi, hmw, hpw 0 (by norm_num), hpw 1 (by norm_num), hpair]
  exact w0k_sum2 hw' _ _ _ _ _ _

/-- **pc 492**. -/
theorem wc_492 (c : WCtx L g sc l d e) : d.c.site = (.pld 3) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum3_cond (lookupD
    (s_pld3 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2)
    (d.c.a0, v)))) := by
  intro hs x bs hk
  have hp : e.pc = 492 := by rw [c.hpc, hs]; rfl
  obtain ⟨v, hr, -⟩ := c.hpay.peer x bs hk ⟨3, by norm_num, by omega⟩
  refine ⟨v, hr, fun hel => ?_⟩
  obtain ⟨v', w', hr', hw', hlo, hhi, hmw, hpw, hpair⟩ := c.pair (k := 3) (by norm_num)
    (by omega) hs hel hk
  obtain rfl : v' = v := Except.ok.inj (hr'.symm.trans hr)
  rw [hhi, hmw, hpw 0 (by norm_num), hpw 1 (by norm_num), hpw 2 (by norm_num), hpair]
  exact w0k_sum3 hw' _ _ _ _ _ _

/-- **pc 497**. -/
theorem wc_497 (c : WCtx L g sc l d e) : d.c.site = (.pld 4) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum4_cond (lookupD
    (s_pld4 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3)
    (d.c.a0, v)))) := by
  intro hs x bs hk
  have hp : e.pc = 497 := by rw [c.hpc, hs]; rfl
  obtain ⟨v, hr, -⟩ := c.hpay.peer x bs hk ⟨4, by norm_num, by omega⟩
  refine ⟨v, hr, fun hel => ?_⟩
  obtain ⟨v', w', hr', hw', hlo, hhi, hmw, hpw, hpair⟩ := c.pair (k := 4) (by norm_num)
    (by omega) hs hel hk
  obtain rfl : v' = v := Except.ok.inj (hr'.symm.trans hr)
  rw [hhi, hmw, hpw 0 (by norm_num), hpw 1 (by norm_num), hpw 2 (by norm_num), hpw 3 (by
    norm_num), hpair]
  exact w0k_sum4 hw' _ _ _ _ _ _

/-- **pc 502**. -/
theorem wc_502 (c : WCtx L g sc l d e) : d.c.site = (.pld 5) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum5_cond (lookupD
    (s_pld5 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4)
    (d.c.a0, v)))) := by
  intro hs x bs hk
  have hp : e.pc = 502 := by rw [c.hpc, hs]; rfl
  obtain ⟨v, hr, -⟩ := c.hpay.peer x bs hk ⟨5, by norm_num, by omega⟩
  refine ⟨v, hr, fun hel => ?_⟩
  obtain ⟨v', w', hr', hw', hlo, hhi, hmw, hpw, hpair⟩ := c.pair (k := 5) (by norm_num)
    (by omega) hs hel hk
  obtain rfl : v' = v := Except.ok.inj (hr'.symm.trans hr)
  rw [hhi, hmw, hpw 0 (by norm_num), hpw 1 (by norm_num), hpw 2 (by norm_num), hpw 3 (by
    norm_num), hpw 4 (by norm_num), hpair]
  exact w0k_sum5 hw' _ _ _ _ _ _

/-- **pc 507**. -/
theorem wc_507 (c : WCtx L g sc l d e) : d.c.site = (.pld 6) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → Gen.sum6_cond (lookupD
    (s_pld6 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5)
    (d.c.a0, v)))) := by
  intro hs x bs hk
  have hp : e.pc = 507 := by rw [c.hpc, hs]; rfl
  obtain ⟨v, hr, -⟩ := c.hpay.peer x bs hk ⟨6, by norm_num, by omega⟩
  refine ⟨v, hr, fun hel => ?_⟩
  obtain ⟨v', w', hr', hw', hlo, hhi, hmw, hpw, hpair⟩ := c.pair (k := 6) (by norm_num)
    (by omega) hs hel hk
  obtain rfl : v' = v := Except.ok.inj (hr'.symm.trans hr)
  rw [hhi, hmw, hpw 0 (by norm_num), hpw 1 (by norm_num), hpw 2 (by norm_num), hpw 3 (by
    norm_num), hpw 4 (by norm_num), hpw 5 (by norm_num), hpair]
  exact w0k_sum6 hw' _ _ _ _ _ _

/-- **pc 512**. -/
theorem wc_512 (c : WCtx L g sc l d e) : d.c.site = (.pld 7) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ (d.c.el ≠ 0 → (Gen.sum7_cond
    (lookupD (s_pld7 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw)
    (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.c.a0, v))))
    ∧ (Gen.rmax_cond (lookupD (f_pld8 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo)
    (d.b.hi) (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw
    6) (d.c.a0, v))))) := by
  intro hs x bs hk
  have hp : e.pc = 512 := by rw [c.hpc, hs]; rfl
  obtain ⟨v, hr, -⟩ := c.hpay.peer x bs hk ⟨7, by norm_num, by omega⟩
  refine ⟨v, hr, fun hel => ?_⟩
  obtain ⟨v', w', hr', hw', hlo, hhi, hmw, hpw, hpair⟩ := c.pair (k := 7) (by norm_num)
    (by omega) hs hel hk
  obtain rfl : v' = v := Except.ok.inj (hr'.symm.trans hr)
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  rw [hhi, hmw, hpw 0 (by norm_num), hpw 1 (by norm_num), hpw 2 (by norm_num), hpw 3 (by
    norm_num), hpw 4 (by norm_num), hpw 5 (by norm_num), hpw 6 (by norm_num), hpair]
  exact ⟨w0k_sum7 hw' _ _ _ _ _ _, w0k_rmax hw' c.hx hm hl hmx⟩

/-- **pc 572**: the peer's row maximum is the valid block's. -/
theorem wc_572 (c : WCtx L g sc l d e) : d.c.site = (.mld) →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ Gen.mld_cond (lookupD (s_mld (scX L)
    (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi) (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw
    2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7) (v))) := by
  intro hs x bs hk
  have hp : e.pc = 572 := by rw [c.hpc, hs]; rfl
  obtain ⟨v, hr, hcl, hv⟩ := c.hpay.peerMax x bs hk hp
  obtain ⟨w', hw', hE, hlo, hhi, hmw, hpw, -⟩ := c.canon (by omega) (by omega)
  have hne : (w0Words ((w0Fin l).2 ++ [e])).pm ≠ .pred false := by
    rw [wpm_at _ hp hk hr]
    rcases hv with h | rfl
    · exact w0Fin_ne_pred h
    · nofun
  have hpm := hE.pm.resolve_left hne
  rw [wpm_at _ hp hk hr] at hpm
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  refine ⟨v, hr, ?_⟩
  rw [hhi, hmw (by omega), hpm, hpw 0 (by norm_num) (by omega), hpw 1 (by norm_num) (by omega),
    hpw 2 (by norm_num) (by omega), hpw 3 (by norm_num) (by omega),
    hpw 4 (by norm_num) (by omega), hpw 5 (by norm_num) (by omega),
    hpw 6 (by norm_num) (by omega), hpw 7 (by norm_num) (by omega)]
  exact w0k_mld hw' c.hx hm hl hmx

/-- **pc 578**: the vote's windows. -/
theorem wc_578 (c : WCtx L g sc l d e) : d.c.site = .vote →
    ∀ m p r, e.kind = .voteMode .any m p r → voteCond (scX L) d.b r := by
  intro hs m p r hk
  have hp : e.pc = 578 := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, hhi, hmw, hpw, hpm⟩ := c.canon (by omega) (by omega)
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  have hw'' : W0Ok sc { w' with vt := r } :=
    ⟨hw'.scale, hw'.hiLen, hw'.hi, hw'.loLen, hw'.lo, hw'.mask, hw'.peer, hw'.pm⟩
  unfold voteCond
  rw [hhi, hmw (by omega), hpm (by omega), hpw 0 (by norm_num) (by omega),
    hpw 1 (by norm_num) (by omega), hpw 2 (by norm_num) (by omega),
    hpw 3 (by norm_num) (by omega), hpw 4 (by norm_num) (by omega),
    hpw 5 (by norm_num) (by omega), hpw 6 (by norm_num) (by omega),
    hpw 7 (by norm_num) (by omega)]
  exact ⟨fun _ => w0k_vt hw' c.hx hm hl hmx, w0k_pw hw'' c.hx hm hl hmx⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}

theorem datum_finite {fmt : FloatFmt} {v : Value} {x : ℝ}
    (h : Assumption.readEReal.ofDatum (classify fmt v) = some (.ok (x : EReal))) :
    (classify fmt v).bind FVal.finite = .ok x := by
  cases hc : classify fmt v with
  | error e => rw [hc] at h; simp [Assumption.readEReal.ofDatum] at h
  | ok f =>
    rw [hc] at h
    cases f with
    | zero neg =>
      simp [Assumption.readEReal.ofDatum, pure, Except.pure] at h
      have h' : (0 : ℝ) = x := by exact_mod_cast h
      simp [Except.bind, FVal.finite, h', pure, Except.pure]
    | fin q =>
      simp [Assumption.readEReal.ofDatum, pure, Except.pure] at h
      simp [Except.bind, FVal.finite, h, pure, Except.pure]
    | inf neg =>
      simp [Assumption.readEReal.ofDatum, pure, Except.pure] at h
      split_ifs at h <;> simp at h
    | nan n => simp [Assumption.readEReal.ofDatum] at h

/-- A word that reads as the real `x` reads as the number `x`. -/
theorem valFloat_of_rd {v : Value} {x : ℝ} (h : Rd v (x : EReal)) : valFloat .f32 v = .ok x := by
  have hr := h.2.1
  cases v with
  | float f y =>
    by_cases hf : f = .f32
    · subst hf
      simp [Assumption.readEReal, pure, Except.pure] at hr
      simp [valFloat, hr, pure, Except.pure]
    · simp only [Assumption.readEReal, hf, ↓reduceIte] at hr
      simp only [valFloat, hf, ↓reduceIte, bitsAsFloat]
      exact datum_finite hr
  | _ =>
    simp only [Assumption.readEReal] at hr
    simp only [valFloat, bitsAsFloat]
    exact datum_finite hr

theorem okF_of_rd {v : Value} {x : ℝ} (h : Rd v (x : EReal)) : OkF v x :=
  ⟨h.1, valFloat_of_rd h⟩

/-- **The block behind a site of the rescale or the epilogue's start**: the state's block is that
of a valid block. -/
theorem WCtx.blkIs (c : WCtx L g sc l d e) (h1 : 572 < e.pc) (h2 : e.pc < 1122) :
    ∃ w, W0Ok sc w ∧ BlkIs d.b w := by
  obtain ⟨w', hw', -, hlo, hhi, hmw, hpw, hpm⟩ := c.canon (by omega) h2
  have hmw' := hmw (by omega)
  have hpm' := hpm h1
  have hpw' : ∀ j < 8, d.b.pw j = w'.pw j := fun j hj => hpw j hj (by omega)
  refine ⟨{ lo := w'.lo, hi := d.b.hi, mw := d.b.mw, pw := d.b.pw, pm := d.b.pm, vt := d.b.vt },
    ⟨hw'.scale, ?_, ?_, hw'.loLen, hw'.lo, ?_, ?_, ?_⟩, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  · simpa [hhi] using hw'.hiLen
  · simpa [hhi] using hw'.hi
  · simpa [hmw'] using hw'.mask
  · intro k hk
    simpa [hpw' k hk] using hw'.peer k hk
  · simpa [hpm'] using hw'.pm

/-- **pc 711**: the scale factor. -/
theorem wc_711 (c : WCtx L g sc l d e) : d.c.site = .rsf → rsfCond (scX L) d.b := by
  intro hs
  have hp : e.pc = 711 := by rw [c.hpc, hs]; rfl
  obtain ⟨w, hw, hb⟩ := c.blkIs (by omega) (by omega)
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  refine ⟨?_, w0k_alpha c.hx hb (fun _ => hw) hm hl hmx⟩
  obtain ⟨s, hf, -⟩ := blk_alpha c.hx hb (fun _ => hw) hm hl hmx
  change (blkA (scX L) d.b).bytes = 4
  rcases hf with ⟨y, hy⟩ | ⟨r, hr⟩
  · simp [hy, Value.bytes]
  · simp [hr, Value.bytes, FloatFmt.bytes]

/-- The accumulator words a state has loaded are 64 numbers. -/
theorem WCtx.acc (c : WCtx L g sc l d e) (h : w0EpiO (w0Fin l).2 ≠ []) :
    d.b.o.length = 64 ∧ ∃ O : Nat → ℝ, ∀ i < 64, Rd (d.b.o.getD i (.pred false)) (O i) := by
  have hv' : W0Valid sc l := by simpa using c.hv.take (j := l.length)
  obtain ⟨-, -, h3, -⟩ := hv'.epi
  rw [w0Fin_snd] at h
  rw [c.hE.o]
  exact h3.resolve_left h

theorem WCtx.accOk (c : WCtx L g sc l d e) (h : w0EpiO (w0Fin l).2 ≠ []) :
    d.b.o.length = 64 ∧ ∀ v ∈ d.b.o, ∃ r : ℝ, OkF v r := by
  obtain ⟨hlen, O, hO⟩ := c.acc h
  refine ⟨hlen, fun v hv => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hi' : i < 64 := by omega
  refine ⟨O i, okF_of_rd ?_⟩
  have := hO i hi'
  simpa [List.getD_eq_getElem?_getD, hi] using this

/-- **pc 717**. -/
theorem wc_717 (c : WCtx L g sc l d e) : d.c.site = (.rldw 0) →
    Gen.rs0_cond (lookupD (f_rldw0 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
    (d.b.pw 7) (d.b.pm) (d.b.vt) (d.b.o))) := by
  intro hs
  have hp : e.pc = 717 := by rw [c.hpc, hs]; rfl
  obtain ⟨w, hw, hb⟩ := c.blkIs (by omega) (by omega)
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨ho, hO⟩ := c.accOk (c.hld.acc (by simp [hp]))
  exact w0k_rs c.hx hb (fun _ => hw) hm hl hmx 0 ho hO

/-- **pc 818**. -/
theorem wc_818 (c : WCtx L g sc l d e) : d.c.site = (.rldw 1) →
    Gen.rs1_cond (lookupD (f_rldw1 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
    (d.b.pw 7) (d.b.pm) (d.b.vt) (d.b.o))) := by
  intro hs
  have hp : e.pc = 818 := by rw [c.hpc, hs]; rfl
  obtain ⟨w, hw, hb⟩ := c.blkIs (by omega) (by omega)
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨ho, hO⟩ := c.accOk (c.hld.acc (by simp [hp]))
  exact w0k_rs c.hx hb (fun _ => hw) hm hl hmx 1 ho hO

/-- **pc 919**. -/
theorem wc_919 (c : WCtx L g sc l d e) : d.c.site = (.rldw 2) →
    Gen.rs2_cond (lookupD (f_rldw2 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
    (d.b.pw 7) (d.b.pm) (d.b.vt) (d.b.o))) := by
  intro hs
  have hp : e.pc = 919 := by rw [c.hpc, hs]; rfl
  obtain ⟨w, hw, hb⟩ := c.blkIs (by omega) (by omega)
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨ho, hO⟩ := c.accOk (c.hld.acc (by simp [hp]))
  exact w0k_rs c.hx hb (fun _ => hw) hm hl hmx 2 ho hO

/-- **pc 1020**. -/
theorem wc_1020 (c : WCtx L g sc l d e) : d.c.site = (.rldw 3) →
    Gen.rs3_cond (lookupD (f_rldw3 (scX L) (d.b.m) (d.b.l) (d.b.mx) (d.b.sk) (d.b.lo) (d.b.hi)
    (d.b.mw) (d.b.pw 0) (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6)
    (d.b.pw 7) (d.b.pm) (d.b.vt) (d.b.o))) := by
  intro hs
  have hp : e.pc = 1020 := by rw [c.hpc, hs]; rfl
  obtain ⟨w, hw, hb⟩ := c.blkIs (by omega) (by omega)
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨ho, hO⟩ := c.accOk (c.hld.acc (by simp [hp]))
  exact w0k_rs c.hx hb (fun _ => hw) hm hl hmx 3 ho hO

/-- **pc 1122**: the first run of the epilogue reads the statistics the block ends with. -/
theorem wc_1122 (c : WCtx L g sc l d e) : d.c.site = .arrS →
    scmpi .ne .b (Control.advance d.c).cnt 1 = false → exitCond L d.c d.b := by
  intro hs _
  have hp : e.pc = w0ArrSPc := by rw [c.hpc, hs]; rfl
  have hfin : w0Fin (l ++ [e]) = ((w0Fin l).1 ++ [(w0Fin l).2], []) := by
    rw [w0Fin_snoc]; simp [hp]
  have hw : W0Ok sc (w0Words (w0Fin l).2) := c.hv.now.1 _ (by rw [hfin]; simp)
  have hb : BlkIs d.b (w0Words (w0Fin l).2) := by
    rw [w0Fin_snd]
    exact ⟨c.hI.hi, c.hI.mw, c.hI.pw, c.hI.pm, c.hI.vt⟩
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨h1, h2, -, h4⟩ := w0_block hw c.hx hb hm hl hmx
  have e1 : ∀ r' ∈ [2951, 467, 3243, 2950, 2955, 2885, 2880],
      lookupD (wF (scX L) .arrS d.b) r' = blkOst (scX L) d.b r' := by
    intro r' hr'
    unfold wF wcls
    exact lookupD_factsFrom hr'
  have k : ∀ key ∈ [2885, 2950, 2955],
      lookupD (exitFacts L d.c d.b) key = lookupD (wF (scX L) .arrS d.b) key := by
    intro key hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> rfl
  unfold exitCond
  have h452 : lookupD (exitFacts L d.c d.b) 452 = .bits 16 (BitVec.ofNat 64 d.c.ps.toNat) := by
    simp [exitFacts, lookupD]
  have r1 := h4
  rw [← e1 2885 (by decide), ← k 2885 (by simp)] at r1
  have r2 := h1
  rw [← e1 2950 (by decide), ← k 2950 (by simp)] at r2
  have r3 := h2
  rw [← e1 2955 (by decide), ← k 2955 (by simp)] at r3
  exact w0k_e1 _ h452 r1 r2 r3

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
