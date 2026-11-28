-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.PreStepB
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QRoute
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.CopyRoute
public import Lemmas.Flow.SegQOps
import Kernels.InklingRelDecode.Proof.Lib.CtlSteps

@[expose] public section

/-! # The strict tail of the last copy of a block

After the fourth copy of a block the lane leaves the preload loop for the query entry or goes on
to the next block. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- **The query site after the copy tail**: the facts of the entry at pc 316 and the site. -/
theorem qroute {m} (hp : Pre Q L m) (hw0 : w = b32 0) (c : Control.D) (v : Data.Vals)
    (hv : ∀ k, (v.q k).bytes = 2) : ∃ s : Site, querySite (g % L.block) c 0 = s ∧ s.sub = 0 ∧
      Control.Inv (g % L.block) {c with site := s} ∧ SegQ kernel Assumptions.all L g (QT proQt) 316
        ([(525, Data.scaleVal L)] ++ facts Q L g w c 316) s.pc (dFacts Q L g w (dq c v s)) := by
  obtain ⟨hi, hle, -, hsite, hoff, hon⟩ := Data.querySite_spec (g % L.block) c 0 (by omega)
  refine ⟨qSiteAt hi, hsite, ?_, ?_, qentry hp hw0 c v hv hi hle fun n hn' =>
    hoff n (by omega) hn'⟩
  · unfold qSiteAt; split <;> rfl
  · unfold qSiteAt; split
    · exact hon (by omega)
    · trivial

/-- The facts of any site hold the launch's scale: they cover the entry's facts at pc 316. -/
theorem to316 (c : Control.D) (v : Data.Vals) (s : Site) (pc : Nat)
    (hl : (ctlLive 316).isSublist (ctlLive pc) = true) :
    SegQ kernel Assumptions.all L g (QT proQt) 316 (dFactsAt Q L g w (dq c v s) pc) 316
      ([(525, Data.scaleVal L)] ++ facts Q L g w c 316) := by
  refine SegQ.sub fun q hq' => ?_
  rcases List.mem_append.mp hq' with h | h
  · rcases List.mem_singleton.mp h with rfl
    exact List.mem_append_left _ (List.mem_map.mpr ⟨.scale, by cases s <;> simp [Data.tags,
      Data.oldTags], rfl⟩)
  · exact List.mem_append_right _ (mem_facts_sub (c := c) (pc := pc) hl h)

/-- The comparison and the branch of the tail of block 0 (the last issue is at pc 231). -/
theorem tail0 (c : Control.D) (v : Data.Vals) :
    SegQ kernel Assumptions.all L g (QT proQt) 232 (dFactsAt Q L g w (dq c v (.ptc 0 3)) 231)
      (if decide (preloadN Q L g c = 1) = true then 316 else 234)
      (dFactsAt Q L g w (dq c v (.ptc 0 3)) 231) := by
  refine SegQ.comp (b := 233) (G := (63, .pred (decide (preloadN Q L g c = 1))) ::
    dFactsAt Q L g w (dq c v (.ptc 0 3)) 231) (SegQ.comp (b := 233) (G := Data.dF Q L g
    (dq c v (.ptc 0 3)) ++ ((63, .pred (decide (preloadN Q L g c = 1))) :: facts Q L g w
    (dq c v (.ptc 0 3)).c 231)) ?_ (SegQ.weaken fun R hR => ?_)) ?_
  · pre_br [525, 529, 494, 495, 683, 686, 689], Control.tail_cmp0
  · simp only [dFactsAt, holds_append, holds_cons] at hR ⊢
    tauto
  · exact SegQ.branch (qt := proQt) (decide (preloadN Q L g c = 1)) Flow.code_233
      (fun t a ha => Lib.bra_rule t a ha) (segFree (by decide)) (by split <;> decide +kernel)

/-- The same for block 1 (the last issue is at pc 273). -/
theorem tail1 (c : Control.D) (v : Data.Vals) :
    SegQ kernel Assumptions.all L g (QT proQt) 274 (dFactsAt Q L g w (dq c v (.ptc 1 3)) 273)
      (if decide (preloadN Q L g c < 3) = true then 316 else 276)
      (dFactsAt Q L g w (dq c v (.ptc 1 3)) 273) := by
  refine SegQ.comp (b := 275) (G := (72, .pred (decide (preloadN Q L g c < 3))) ::
    dFactsAt Q L g w (dq c v (.ptc 1 3)) 273) (SegQ.comp (b := 275) (G := Data.dF Q L g
    (dq c v (.ptc 1 3)) ++ ((72, .pred (decide (preloadN Q L g c < 3))) :: facts Q L g w
    (dq c v (.ptc 1 3)).c 273)) ?_ (SegQ.weaken fun R hR => ?_)) ?_
  · pre_br [525, 529, 494, 495, 703, 706, 709], Control.tail_cmp1
  · simp only [dFactsAt, holds_append, holds_cons] at hR ⊢
    tauto
  · exact SegQ.branch (qt := proQt) (decide (preloadN Q L g c < 3)) Flow.code_275
      (fun t a ha => Lib.bra_rule t a ha) (segFree (by decide)) (by split <;> decide +kernel)

/-- The two address instructions after the branch of block 0 reach the next block's barrier. -/
theorem mid0 (c : Control.D) (v : Data.Vals) :
    SegQ kernel Assumptions.all L g (QT proQt) 234 (dFactsAt Q L g w (dq c v (.ptc 0 3)) 231)
      236 (dFacts Q L g w (dq c v (.pb 1 0))) := by
  refine SegQ.comp (b := 236) (G := dFactsAt Q L g w (dq c v (.ptc 0 3)) 236) ?_
    (site_subAt c v _ _ _ _ (by decide +kernel) (by decide +kernel))
  pre_br [525, 529, 494, 495, 683, 686, 689], (Control.seg_s234.comp Control.seg_s235)

theorem mid1 (c : Control.D) (v : Data.Vals) :
    SegQ kernel Assumptions.all L g (QT proQt) 276 (dFactsAt Q L g w (dq c v (.ptc 1 3)) 273)
      278 (dFacts Q L g w (dq c v (.pb 2 0))) := by
  refine SegQ.comp (b := 278) (G := dFactsAt Q L g w (dq c v (.ptc 1 3)) 278) ?_
    (site_subAt c v _ _ _ _ (by decide +kernel) (by decide +kernel))
  pre_br [525, 529, 494, 495, 703, 706, 709], (Control.seg_s276.comp Control.seg_s277)

theorem res_sub : ∀ (b : Fin 3) (j : Fin 4), j ≠ 1 → j ≠ 3 → (Site.ptc b j).pc + 1 =
    (afterCopy ⟨.sMax, b32 0, b32 0, b32 0, false, b32 0⟩ 0 0 b j).pc ∧
    (∀ τ ∈ Data.tags (afterCopy ⟨.sMax, b32 0, b32 0, b32 0, false, b32 0⟩ 0 0 b j),
      τ ∈ Data.tags (.ptc b j)) ∧
    (ctlLive (afterCopy ⟨.sMax, b32 0, b32 0, b32 0, false, b32 0⟩ 0 0 b j).pc).isSublist
      (ctlLive (Site.ptc b j).pc) = true := by decide +kernel

theorem ac0_q (c : Control.D) (t n : Nat) (h : n = 1) :
    afterCopy c t n 0 3 = querySite t c 0 := by simp [afterCopy, h]

theorem ac0_b (c : Control.D) (t n : Nat) (h : n ≠ 1) : afterCopy c t n 0 3 = .pb 1 0 := by
  simp [afterCopy, h]

theorem ac1_q (c : Control.D) (t n : Nat) (h : n < 3) :
    afterCopy c t n 1 3 = querySite t c 0 := by simp [afterCopy, h]

theorem ac1_b (c : Control.D) (t n : Nat) (h : ¬n < 3) : afterCopy c t n 1 3 = .pb 2 0 := by
  simp [afterCopy, h]

theorem ac2_q (c : Control.D) (t n : Nat) : afterCopy c t n 2 3 = querySite t c 0 := by
  simp [afterCopy]

/-- **After the copy issue `j`**: the stretch to the site `afterCopy` names. -/
theorem ptc_res {m} (hp : Pre Q L m) (hw0 : w = b32 0) (hv : ∀ k, (v.q k).bytes = 2)
    (c : Control.D) (b : Fin 3) (j : Fin 4) (s : Site)
    (hs : s = afterCopy c (g % L.block) (preloadN Q L g c) b j) :
    SegQ kernel Assumptions.all L g (QT proQt) ((Site.ptc b j).pc + 1)
      (dFacts Q L g w (dq c v (.ptc b j))) s.pc (dFacts Q L g w (dq c v s)) := by
  subst hs
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj with rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := res_sub b 0 (by decide) (by decide)
    exact SegQ.cast_start h1 (site_subAt c v (.ptc b 0) _ _ _ h2 h3)
  · exact pxA b c v _ _ rfl rfl
  · obtain ⟨h1, h2, h3⟩ := res_sub b 2 (by decide) (by decide)
    exact SegQ.cast_start h1 (site_subAt c v (.ptc b 2) _ _ _ h2 h3)
  · obtain ⟨s, hs, -, -, qr⟩ := qroute (Q := Q) (L := L) (g := g) (w := w) hp hw0 c v hv
    have hb : b = 0 ∨ b = 1 ∨ b = 2 := by omega
    rcases hb with rfl | rfl | rfl
    · by_cases h : preloadN Q L g c = 1
      · have t0 := tail0 (Q := Q) (L := L) (g := g) (w := w) c v
        simp only [h, decide_true, ↓reduceIte] at t0
        refine SegQ.cast_start (a' := 232) rfl ?_
        rw [ac0_q c _ _ h, hs]
        exact t0.comp ((to316 c v (.ptc 0 3) 231 (by decide +kernel)).comp qr)
      · have t0 := tail0 (Q := Q) (L := L) (g := g) (w := w) c v
        simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte] at t0
        refine SegQ.cast_start (a' := 232) rfl ?_
        rw [ac0_b c _ _ h]
        exact t0.comp (mid0 c v)
    · by_cases h : preloadN Q L g c < 3
      · have t0 := tail1 (Q := Q) (L := L) (g := g) (w := w) c v
        simp only [h, decide_true, ↓reduceIte] at t0
        refine SegQ.cast_start (a' := 274) rfl ?_
        rw [ac1_q c _ _ h, hs]
        exact t0.comp ((to316 c v (.ptc 1 3) 273 (by decide +kernel)).comp qr)
      · have t0 := tail1 (Q := Q) (L := L) (g := g) (w := w) c v
        simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte] at t0
        refine SegQ.cast_start (a' := 274) rfl ?_
        rw [ac1_b c _ _ h]
        exact t0.comp (mid1 c v)
    · refine SegQ.cast_start (a' := 316) rfl ?_
      rw [ac2_q, hs]
      exact (to316 c v (.ptc 2 3) 315 (by decide +kernel)).comp qr

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
