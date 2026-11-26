-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictH
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.ArrLWin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepArrS
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepKinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WinCond
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.StrictDataSites0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.StrictDataSites1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.StrictDataSites2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.StrictDataSteps0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.StrictEpiSites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.StepAt
public import Lemmas.Flow.DataStepE
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part003

@[expose] public section

/-! # The strict step of warpgroup 0's data machine at every state

`dataStepFor_wg0`: from a state of the chain, an event whose window conditions hold (`WinCond`)
and whose length loads rebuild takes the strict step (`Code.StepFor`): at a site with a data window
the window's (`sk_<pc>`), at a pure site the control machine's exact step (`stepAtP`) with the
strict data step of the site (`dsS_<pc>`, `Over.stepForE`), off the chain the control machine's. -/

/-! # The strict step of the last-store arrival (pc 200)

The arrival leaves for the loop's first head (`bar0`, pc 256) or, when the thread has no block,
for the epilogue's first barrier (`ebar0`, pc 1154). The window is exact (`arrLWinF`,
`arrLWinT`); the statistics' initial words are the block's new carried words. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- **The strict step at pc 200**. -/
theorem sk_200 (d : D) (hs : d.c.site = .arrL) (hok : d.ok = true) (e : Event) :
    (code P L g w).StepFor d e := by
  have hsucc : ∀ e, Control.succ P L g w d.c e = some (some (Control.loopEntry d.c)) := by
    intro e; simp [Control.succ, hs]
  have hrec : ∀ e, record d.c e d.b = { d.b with m := mI, l := lI, mx := mxI } := by
    intro e; simp [record, hs]
  have hso : succOk d.c (Control.loopEntry d.c) = true := by
    unfold Control.loopEntry; split <;> simp [succOk, hs]
  have hel1 : Control.elems d.c.site = 1 := by rw [hs]; rfl
  have hel : d.c.el = 0 →
      (Control.loopEntry d.c).el < Control.elems (Control.loopEntry d.c).site := by
    intro h
    unfold Control.loopEntry; split <;> simp [Control.elems, h]
  have he1 : d.c.el = 0 → (Control.loopEntry d.c).el = 0 := by
    intro h; unfold Control.loopEntry; split <;> simp [h]
  have hf : wF (scX L) d.c.site d.b = f_set (scX L) d.b.sk := by rw [hs]; rfl
  have hp : d.c.site.pc = 200 := by rw [hs]; rfl
  have hst : Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b =
      factsFrom (Control.ctlLive 200) (Control.valueOf P L g w d.c) ++ f_set (scX L) d.b.sk := by
    unfold Control.facts; rw [hp, hf]
  cases h74 : scmpi .lt .s (Control.r15 d.c.l0 d.c.l1) 64
  · have hq : (Control.loopEntry d.c).site = .bar0 := by simp [Control.loopEntry, h74]
    have key : ∀ e, (code P L g w).StepFor d e := skW_nx (pc := 200) (pc' := 256) (by rw [hs]; rfl)
      (by rw [hq]; rfl) (by rw [hs]; decide)
      (by rw [hs]; exact Flow.code_200)
      (fun {t e u} hf => by rw [hs] at hf; exact Code.fires_arrive_next hf) hel1 hok hsucc hso
      hrec he1 hel (by
      rw [hst, hq]
      exact arrLWinF (P := P) (L := L) (g := g) (w := w) d.c (scX L) d.b.sk h74)
    exact fun {t u} => key e
  · have hq : (Control.loopEntry d.c).site = .ebar0 := by simp [Control.loopEntry, h74]
    have key : ∀ e, (code P L g w).StepFor d e := skW_nx (pc := 200) (pc' := 1154) (by rw [hs]; rfl)
      (by rw [hq]; rfl) (by rw [hs]; decide)
      (by rw [hs]; exact Flow.code_200)
      (fun {t e u} hf => by rw [hs] at hf; exact Code.fires_arrive_next hf) hel1 hok hsucc hso
      hrec he1 hel (by
      rw [hst, hq]
      exact arrLWinT (P := P) (L := L) (g := g) (w := w) d.c (scX L) d.b.sk h74)
    exact fun {t u} => key e

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m0 : Mem0}

/-- The control machine's exact step at a pure site, from the invariant. -/
theorem stepAtP (hp : Pre P L m0) (d : Control.D) (hpu : Control.sitePure d.site = true)
    (hi : (Control.code P L g w).inv d) : (Control.code P L g w).StepAt d := by
  by_cases he : d.el = 0
  · exact Control.stepAtS hp d hpu he
  by_cases h1 : ∃ k, d.site = .ost k
  · obtain ⟨k, hs⟩ := h1
    exact Control.stepAt_ostS k d hs
  by_cases h2 : ∃ c k, d.site = .ost2 c k
  · obtain ⟨c, k, hs⟩ := h2
    exact Control.stepAt_ost2S c k d hs
  exfalso
  apply he
  have h : d.el < Control.elems d.site := hi
  have key : ∀ s, Control.sitePure s = true → (∀ k, s ≠ .ost k) → (∀ c k, s ≠ .ost2 c k) →
      Control.elems s = 1 := by
    intro s hs h1 h2
    cases s <;> simp_all [Control.sitePure, Control.elems]
  have := key d.site hpu (fun k hk => h1 ⟨k, hk⟩) (fun c k hk => h2 ⟨c, k, hk⟩)
  omega

/-- A site off the chain is pure. -/
theorem pure_of_off {s : Site} (h : onChain s = false) : Control.sitePure s = true := by
  cases s <;> simp_all [onChain, Control.sitePure]

/-- **The strict step at pc 103**, from the start state (its flag is not set, its facts are
the same). -/
theorem sk_103' (hp : Pre P L m0) (hg : g < L.threads ∧ g / L.block < L.grid) (d : D)
    (hs : d.c.site = .smr) (e : Event) : (code P L g w).StepFor d e := by
  obtain ⟨⟨s0, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩, b, h, ok⟩ := d
  obtain rfl : s0 = .smr := hs
  have key : (code P L g w).StepFor ⟨⟨.smr, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩, b, h,
      true⟩ e := by
    intro t u
    exact sk_103 (w := w) hp hg ⟨⟨.smr, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩, b, h, true⟩
      rfl rfl e
  cases ok
  · exact fun {t u} ins hat hi hc hf => key ins hat hi hc hf
  · exact fun {t u} ins hat hi hc hf => key ins hat hi hc hf

/-- **A pure site takes the strict step** from the control machine's and the site's data step. -/
theorem pure_step (hp : Pre P L m0) {d : D} {e : Event} {s : Site} (hs : d.c.site = s)
    (hpu : Control.sitePure s = true) (hD : d.c.site = s → DataStepE (code P L g w) (dF L) d e) :
    (code P L g w).StepFor d e :=
  (over P L g w).stepForE (fun c hc => (Control.stepAt hp c).site hc)
    (fun hi => stepAtP hp d.c (hs ▸ hpu) hi) e (hD hs)

/-- **The strict step at every state of the chain.** -/
theorem dataStepFor_wg0 (hp : Pre P L m0)
    (hg : g < L.threads ∧ g / L.block < L.grid) (d : D) (e : Event)
    (hok : onChain d.c.site = true → isStart d.c.site = false → d.ok = true)
    (hn : EvNcOk e) (W : WinCond L g d e) :
    (code P L g w).StepFor d e := by
  cases hc : onChain d.c.site
  · apply pure_step hp rfl (pure_of_off hc)
    exact fun _ => dsS_off (fun h => by simp [onChain, h] at hc) fun _ => succOk_off hc
  have hok' := hok hc
  obtain ⟨⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩, b, hist, ok⟩ := d
  cases s <;> simp only [onChain, Bool.false_eq_true] at hc
  · exact fun {t u} => sk_103' (hp := hp) (hg := hg) (d := _) (hs := rfl) (e := e)
  · exact fun {t u} => sk_156 (hp := hp)
          (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w156 rfl) (e := e)
  · apply pure_step hp rfl rfl; exact fun hs => dsS_168 _ e hs hn
  · apply pure_step hp rfl rfl; exact fun hs => dsS_181 _ e hs hn
  · apply pure_step hp rfl rfl; exact dsS_198 _ e
  · exact fun {t u} => sk_200 (d := _) (hs := rfl) (hok := hok' rfl) (e := e)
  · apply pure_step hp rfl rfl; exact dsS_256 _ e
  · apply pure_step hp rfl rfl; exact dsS_264 _ e
  · apply pure_step hp rfl rfl; exact dsS_272 _ e
  · apply pure_step hp rfl rfl; exact dsS_275 _ e
  · rename_i a k
    fin_cases k <;> cases a
    · apply pure_step hp rfl rfl; exact dsS_278 _ e
    · apply pure_step hp rfl rfl; exact dsS_283 _ e
    · apply pure_step hp rfl rfl; exact dsS_280 _ e
    · apply pure_step hp rfl rfl; exact dsS_285 _ e
  · apply pure_step hp rfl rfl; exact dsS_286 _ e
  · apply pure_step hp rfl rfl; exact dsS_287 _ e
  · exact fun {t u} => sk_289 (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w289 rfl) (e := e)
  · rename_i k
    fin_cases k
    · exact fun {t u} => sk_403 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w403 rfl) (e := e)
    · exact fun {t u} => sk_413 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w413 rfl) (e := e)
    · exact fun {t u} => sk_423 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w423 rfl) (e := e)
    · exact fun {t u} => sk_433 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w433 rfl) (e := e)
    · exact fun {t u} => sk_443 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w443 rfl) (e := e)
    · exact fun {t u} => sk_453 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w453 rfl) (e := e)
    · exact fun {t u} => sk_463 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w463 rfl) (e := e)
    · apply pure_step hp rfl rfl; exact dsS_473 _ e
  · exact fun {t u} => sk_475 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w475 rfl) (e := e)
  · rename_i k
    fin_cases k
    · exact fun {t u} => sk_477
          (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w477 rfl) (e := e)
    · exact fun {t u} => sk_482
          (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w482 rfl) (e := e)
    · exact fun {t u} => sk_487
          (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w487 rfl) (e := e)
    · exact fun {t u} => sk_492
          (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w492 rfl) (e := e)
    · exact fun {t u} => sk_497
          (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w497 rfl) (e := e)
    · exact fun {t u} => sk_502
          (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w502 rfl) (e := e)
    · exact fun {t u} => sk_507
          (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w507 rfl) (e := e)
    · exact fun {t u} => sk_512
          (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w512 rfl) (e := e)
  · apply pure_step hp rfl rfl; exact dsS_566 _ e
  · apply pure_step hp rfl rfl; exact dsS_569 _ e
  · apply pure_step hp rfl rfl; exact dsS_571 _ e
  · exact fun {t u} => sk_572 (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w572 rfl) (e := e)
  · exact fun {t u} => sk_578 (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w578 rfl) (e := e)
  · rename_i k
    fin_cases k
    · apply pure_step hp rfl rfl; exact dsS_704 _ e
    · apply pure_step hp rfl rfl; exact dsS_705 _ e
    · apply pure_step hp rfl rfl; exact dsS_706 _ e
    · apply pure_step hp rfl rfl; exact dsS_707 _ e
  · exact fun {t u} => sk_711 (d := _) (hs := rfl) (hok := hok' rfl) (hc := W.w711 rfl) (e := e)
  · rename_i k
    fin_cases k
    · apply pure_step hp rfl rfl; exact dsS_716 _ e
    · apply pure_step hp rfl rfl; exact dsS_817 _ e
    · apply pure_step hp rfl rfl; exact dsS_918 _ e
    · apply pure_step hp rfl rfl; exact dsS_1019 _ e
  · rename_i k
    fin_cases k
    · exact fun {t u} => sk_717 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w717 rfl) (e := e)
    · exact fun {t u} => sk_818 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w818 rfl) (e := e)
    · exact fun {t u} => sk_919 (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w919 rfl) (e := e)
    · exact fun {t u} => sk_1020
          (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w1020 rfl) (e := e)
  · rename_i k
    fin_cases k
    · apply pure_step hp rfl rfl; exact dsS_814 _ e
    · apply pure_step hp rfl rfl; exact dsS_915 _ e
    · apply pure_step hp rfl rfl; exact dsS_1016 _ e
    · apply pure_step hp rfl rfl; exact dsS_1117 _ e
  · rename_i k
    fin_cases k
    · apply pure_step hp rfl rfl; exact dsS_815 _ e
    · apply pure_step hp rfl rfl; exact dsS_916 _ e
    · apply pure_step hp rfl rfl; exact dsS_1017 _ e
    · apply pure_step hp rfl rfl; exact dsS_1118 _ e
  · apply pure_step hp rfl rfl; exact dsS_1119 _ e
  · apply pure_step hp rfl rfl; exact dsS_1120 _ e
  · exact fun {t u} => sk_1122 (d := _) (hs := rfl) (hok := hok' rfl) (hc := W.w1122 rfl) (e := e)
  · apply pure_step hp rfl rfl; exact dsS_1154 _ e
  · apply pure_step hp rfl rfl; exact dsS_1155 _ e
  · apply pure_step hp rfl rfl; exact dsS_1156 _ e
  · exact fun {t u} => sk_1157 (hp := hp)
          (d := _) (hs := rfl) (hok := hok' rfl) (hcd := W.w1157 rfl) (e := e)
  · apply pure_step hp rfl rfl; exact dsS_1178 _ e
  · apply pure_step hp rfl rfl; exact dsS_1184 _ e
  · exact fun {t u} => sk_1187 (hp := hp)
          (d := _) (hs := rfl) (hok := hok' rfl) (hc := W.w1187 rfl) (e := e)
  · rename_i k
    fin_cases k
    · apply pure_step hp rfl rfl; exact dsS_1201 _ e
    · apply pure_step hp rfl rfl; exact dsS_1361 _ e
    · apply pure_step hp rfl rfl; exact dsS_1519 _ e
    · apply pure_step hp rfl rfl; exact dsS_1676 _ e
  · rename_i k
    fin_cases k
    · exact fun {t u} => sk_1202
          (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w1202 rfl) (e := e)
    · exact fun {t u} => sk_1362
          (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w1362 rfl) (e := e)
    · exact fun {t u} => sk_1520
          (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w1520 rfl) (e := e)
    · exact fun {t u} => sk_1677
          (d := _) (hs := rfl) (hok := hok' rfl) (c1 := W.w1677 rfl) (e := e)
  · rename_i c k
    fin_cases c <;> fin_cases k
    · apply pure_step hp rfl rfl; exact dsS_1331 _ e
    · apply pure_step hp rfl rfl; exact dsS_1332 _ e
    · apply pure_step hp rfl rfl; exact dsS_1333 _ e
    · apply pure_step hp rfl rfl; exact dsS_1334 _ e
    · apply pure_step hp rfl rfl; exact dsS_1335 _ e
    · apply pure_step hp rfl rfl; exact dsS_1336 _ e
    · apply pure_step hp rfl rfl; exact dsS_1337 _ e
    · apply pure_step hp rfl rfl; exact dsS_1338 _ e
    · apply pure_step hp rfl rfl; exact dsS_1491 _ e
    · apply pure_step hp rfl rfl; exact dsS_1492 _ e
    · apply pure_step hp rfl rfl; exact dsS_1493 _ e
    · apply pure_step hp rfl rfl; exact dsS_1494 _ e
    · apply pure_step hp rfl rfl; exact dsS_1495 _ e
    · apply pure_step hp rfl rfl; exact dsS_1496 _ e
    · apply pure_step hp rfl rfl; exact dsS_1497 _ e
    · apply pure_step hp rfl rfl; exact dsS_1498 _ e
    · apply pure_step hp rfl rfl; exact dsS_1649 _ e
    · apply pure_step hp rfl rfl; exact dsS_1650 _ e
    · apply pure_step hp rfl rfl; exact dsS_1651 _ e
    · apply pure_step hp rfl rfl; exact dsS_1652 _ e
    · apply pure_step hp rfl rfl; exact dsS_1653 _ e
    · apply pure_step hp rfl rfl; exact dsS_1654 _ e
    · apply pure_step hp rfl rfl; exact dsS_1655 _ e
    · apply pure_step hp rfl rfl; exact dsS_1656 _ e
    · apply pure_step hp rfl rfl; exact dsS_1806 _ e
    · apply pure_step hp rfl rfl; exact dsS_1807 _ e
    · apply pure_step hp rfl rfl; exact dsS_1808 _ e
    · apply pure_step hp rfl rfl; exact dsS_1809 _ e
    · apply pure_step hp rfl rfl; exact dsS_1810 _ e
    · apply pure_step hp rfl rfl; exact dsS_1811 _ e
    · apply pure_step hp rfl rfl; exact dsS_1812 _ e
    · apply pure_step hp rfl rfl; exact dsS_1813 _ e
  · rename_i k
    fin_cases k
    · apply pure_step hp rfl rfl; exact dsS_1339 _ e
    · apply pure_step hp rfl rfl; exact dsS_1499 _ e
    · apply pure_step hp rfl rfl; exact dsS_1657 _ e
    · apply pure_step hp rfl rfl; exact dsS_1814 _ e
  · rename_i k
    fin_cases k
    · apply pure_step hp rfl rfl; exact dsS_1342 _ e
    · apply pure_step hp rfl rfl; exact dsS_1502 _ e
    · apply pure_step hp rfl rfl; exact dsS_1659 _ e
    · apply pure_step hp rfl rfl; exact dsS_1817 _ e
  · rename_i k
    fin_cases k
    · apply pure_step hp rfl rfl; exact dsS_1350 _ e
    · apply pure_step hp rfl rfl; exact dsS_1507 _ e
    · apply pure_step hp rfl rfl; exact dsS_1664 _ e
    · apply pure_step hp rfl rfl; exact dsS_1822 _ e
  · rename_i k
    fin_cases k
    · apply pure_step hp rfl rfl; exact dsS_1358 _ e
    · apply pure_step hp rfl rfl; exact dsS_1516 _ e
    · apply pure_step hp rfl rfl; exact dsS_1673 _ e
    · apply pure_step hp rfl rfl; exact dsS_1831 _ e


end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
