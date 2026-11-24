-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmScN

@[expose] public section

/-! # The branches of the score stage and the rest of the mask's scalars

The mask's table (`valuesZ`) holds registers that are live only inside the stage (the facts of the
stage's first and last pcs are the state's own table: `factsZ_eq`). This file proves the head
of the stage (pcs 1299 to 1302: `%p96` and the two copies `%p179 = %p1`, `%p180 = %p2`, then the
branch), the branch on `%p97` (pc 1466) and the scalars after the mask (pcs 1756 to 1763). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-- The registers of `valuesZ`. -/
def zKeys : List Nat :=
  (List.range 60).map (98 + ·) ++
  ([96, 162, 163, 1268, 164, 165, 166, 179, 180, 97, 1010, 1011, 1901, 1018, 1139, 1015, 1014,
    1012, 1013, 1016, 1017, 158, 161, 159, 160] ++
  ((List.range 30).map (fun q => 1022 + 4 * q) ++
  ((List.range 30).map (fun q => 1021 + 4 * q) ++
  ((List.range 30).map (fun q => 1019 + 4 * q) ++ (List.range 30).map (fun q => 1020 + 4 * q)))))

theorem valuesZ_keys (d : D) : (valuesZ L g d).map Prod.fst = zKeys := by
  simp only [valuesZ, zKeys, List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def]

/-- A register outside the mask's table has the state's value. -/
theorem valueZ_off (d : D) {r : Nat} (h : r ∉ zKeys) : valueZ L g d r = valueOf L g d r := by
  unfold valueZ
  rw [lookup_none_of_not_mem _ (by rw [valuesZ_keys]; exact h)]
  rfl

/-- At a pc where no live register is in the mask's table, the two tables' facts agree. -/
theorem factsZ_eq (d : D) {pc : Nat} (h : disj (Flow.live pc) zKeys = true) :
    factsZ L g pc d = factsAt L g pc d := by
  unfold factsZ factsAt Flow.factsFrom
  refine List.map_congr_left fun r hr => ?_
  rw [valueZ_off d (disj_sound h r hr)]

theorem zoff_1299 : disj (Flow.live 1299) zKeys = true := by decide +kernel
theorem zoff_1303 : disj (Flow.live 1303) zKeys = true := by decide +kernel

/-- Signed 32-bit `<` of two words below `2 ^ 31`. -/
theorem cmp_lt_s32 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    PTX.compare .lt .s 32 (truncBits 32 (BitVec.ofNat 64 a))
      (truncBits 32 (BitVec.ofNat 64 b)) = decide (a < b) := by
  simp only [PTX.compare, toSigned32_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), ha, hb, ↓reduceIte, decide_eq_decide]
  omega

set_option hygiene false in
/-- `%p = (a < b)` of two signed words below `2 ^ 31`, in the mask's table. -/
macro "sz_lt" : tactic =>
  `(tactic| (simp only [Value.pred.injEq, scored_n, scored_e, pr96, pr166]
             rw [cmp_lt_s32 _ _ (by omega) (by omega)]
             try rfl))

theorem head_1299 (d : D) (hT : g % L.block < 128) (hok : d.e.Ok)
    (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 1 1299 (factsZ L g 1299 d) 1300 (factsZ L g 1300 d) := by
  have := hR.blk
  have := hok.nbias
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_lt

/-- `mov.pred d, a` of a register that holds a predicate. -/
theorem exec_movP {t : TState} {d a : Nat} {b : Bool} (hS : Assumption.SegFreePc asms t.pc)
    (ha : t.regs a = some (.pred b)) :
    execLocalA asms L g t (.move ⟨.scalar, .pred, [some d], [.reg a]⟩) =
      .ok (PTX.next (setReg t d (.pred b))) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, readPred, readReg, ha, bind, Except.bind,
    pure, Except.pure]

theorem valueOf_p1 (d : D) : valueOf L g d 1 = .pred (decide (half (g % L.block) ≠ 0)) := by
  sm_vals

theorem valueOf_p2 (d : D) : valueOf L g d 2 = .pred (decide (half (g % L.block) = 0)) := by
  sm_vals

theorem zkey_1 : 1 ∉ zKeys := by decide +kernel
theorem zkey_2 : 2 ∉ zKeys := by decide +kernel

theorem emu_head : ∀ k < 4, Assumptions.emuSites.contains (1300 + k) = false := by decide +kernel
theorem live_head : 1 ∈ Flow.live 1300 ∧ 2 ∈ Flow.live 1301 ∧
    subX (Flow.live 1301) (Flow.live 1300) [179] = true ∧
    subX (Flow.live 1302) (Flow.live 1301) [180] = true ∧ 96 ∈ Flow.live 1302 := by
  decide +kernel

theorem head_1300 (d : D) :
    Seg kernel asms L g 1 1300 (factsFrom (Flow.live 1300) (valueEx (valueZ L g d) [])) 1301
      (factsFrom (Flow.live 1301) (valueEx (valueZ L g d)
        [(179, .pred (decide (half (g % L.block) ≠ 0)))])) := by
  refine Seg.set1 (K := kernel) Flow.code_1300 rfl (fun t h => ?_) (subX_sound live_head.2.2.1)
  have hS : Assumption.SegFreePc asms t.pc := by
    rw [h.1]; exact segFree (by simpa using emu_head 0 (by omega))
  have hr := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d) []) live_head.1)
  rw [valueEx_nil, valueZ_off d zkey_1, valueOf_p1] at hr
  exact exec_movP hS hr

theorem head_1301 (d : D) :
    Seg kernel asms L g 1 1301
      (factsFrom (Flow.live 1301) (valueEx (valueZ L g d)
        [(179, .pred (decide (half (g % L.block) ≠ 0)))])) 1302
      (factsFrom (Flow.live 1302) (valueEx (valueZ L g d)
        [(180, .pred (decide (half (g % L.block) = 0))),
          (179, .pred (decide (half (g % L.block) ≠ 0)))])) := by
  refine Seg.set1 (K := kernel) Flow.code_1301 rfl (fun t h => ?_)
    (subX_sound live_head.2.2.2.1)
  have hS : Assumption.SegFreePc asms t.pc := by
    rw [h.1]; exact segFree (by simpa using emu_head 1 (by omega))
  have hr := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueZ L g d)
    [(179, .pred (decide (half (g % L.block) ≠ 0)))]) live_head.2.1)
  rw [valueEx_cons_ne _ _ (by decide), valueEx_nil, valueZ_off d zkey_2, valueOf_p2] at hr
  exact exec_movP hS hr

theorem valueZ_96 (d : D) : valueZ L g d 96 = .pred (pr96 d.e d.n) := by
  simp only [valueZ, valuesZ, PTX.Flow.lookupLit, Option.getD_some]

theorem valueZ_180 (d : D) : valueZ L g d 179 = .pred (pe0 d.e (g % L.block) d.n) := by
  simp only [valueZ, valuesZ, PTX.Flow.lookupLit, Option.getD_some]

theorem valueZ_181 (d : D) : valueZ L g d 180 = .pred (pe1 d.e (g % L.block) d.n) := by
  simp only [valueZ, valuesZ, PTX.Flow.lookupLit, Option.getD_some]

theorem live_head2 : subS (Flow.live 1764) (Flow.live 1302) = true := by decide +kernel
theorem live_head4 : subS (Flow.live 1303) (Flow.live 1302) = true := by decide +kernel
theorem live_head3 : disj (Flow.live 1303) [179, 180] = true := by decide +kernel
theorem emu_1302 : Assumptions.emuSites.contains 1302 = false := by decide +kernel

/-- The registers `%p96`, `%p179` and `%p180` (pcs 1299 to 1301). -/
theorem head_pre (d : D) (hT : g % L.block < 128) (hok : d.e.Ok)
    (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 3 1299 (factsZ L g 1299 d) 1302
      (factsFrom (Flow.live 1302) (valueEx (valueZ L g d)
        [(180, .pred (decide (half (g % L.block) = 0))),
          (179, .pred (decide (half (g % L.block) ≠ 0)))])) :=
  Seg.of_len (((head_1299 d hT hok hR).comp (head_1300 d)).comp (head_1301 d)) rfl

/-- The branch at pc 1302 keeps the facts of the head. -/
theorem head_bra (d : D) {pick : Bool} (hp : pr96 d.e d.n = pick) :
    Seg kernel asms L g 1 1302
      (factsFrom (Flow.live 1302) (valueEx (valueZ L g d)
        [(180, .pred (decide (half (g % L.block) = 0))),
          (179, .pred (decide (half (g % L.block) ≠ 0)))])) (if pick then 1764 else 1302 + 1)
      (factsFrom (Flow.live 1302) (valueEx (valueZ L g d)
        [(180, .pred (decide (half (g % L.block) = 0))),
          (179, .pred (decide (half (g % L.block) ≠ 0)))])) := by
  refine Seg.bra (K := kernel) Flow.code_1302 ?_ (fun t _ => localRule_bra) (segFree emu_1302)
  have := mem_factsFrom (val := valueEx (valueZ L g d)
    [(180, .pred (decide (half (g % L.block) = 0))),
      (179, .pred (decide (half (g % L.block) ≠ 0)))]) live_head.2.2.2.2
  rw [valueEx_cons_ne _ _ (by decide), valueEx_cons_ne _ _ (by decide), valueEx_nil, valueZ_96, hp]
    at this
  exact this

/-- **The head of the stage when the block has no bias** (`%p96`): from pc 1299 to pc 1764. -/
theorem head_true (d : D) (hT : g % L.block < 128) (hok : d.e.Ok)
    (hR : Rng d.e (g % L.block) d.n) (hp : pr96 d.e d.n = true) :
    Seg kernel asms L g 4 1299 (factsZ L g 1299 d) 1764 (factsZ L g 1764 d) := by
  have h := (head_pre d hT hok hR).comp (head_bra d hp)
  refine Seg.of_len (h.weaken_end fun R hF => ?_) rfl
  refine holds_of_pointwise fun r hr => ?_
  have hr' := subS_sound _ _ live_head2 r hr
  have := holds_mem hF (mem_factsFrom (val := valueEx (valueZ L g d)
    [(180, .pred (decide (half (g % L.block) = 0))),
      (179, .pred (decide (half (g % L.block) ≠ 0)))]) hr')
  rw [this]
  congr 1
  by_cases h1 : r = 180
  · subst h1
    simp only [valueEx_cons_self, valueZ_181, pe1, hp, ↓reduceIte]
  by_cases h0 : r = 179
  · subst h0
    simp only [valueEx_cons_ne _ _ h1, valueEx_cons_self, valueZ_180, pe0, hp, ↓reduceIte]
  simp only [valueEx_cons_ne _ _ h1, valueEx_cons_ne _ _ h0, valueEx_nil]

/-- **The head of the stage when the block has bias**: from pc 1299 to pc 1303. -/
theorem head_false (d : D) (hT : g % L.block < 128) (hok : d.e.Ok)
    (hR : Rng d.e (g % L.block) d.n) (hp : pr96 d.e d.n = false) :
    Seg kernel asms L g 4 1299 (factsAt L g 1299 d) 1303 (factsAt L g 1303 d) := by
  have h := (head_pre d hT hok hR).comp (head_bra d hp)
  rw [← factsZ_eq d zoff_1299, ← factsZ_eq d zoff_1303]
  refine Seg.of_len (h.weaken_end fun R hF => ?_) rfl
  refine holds_of_pointwise fun r hr => ?_
  have hr' := subS_sound _ _ live_head4 r hr
  have hn := disj_sound live_head3 r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  have := holds_mem hF (mem_factsFrom (val := valueEx (valueZ L g d)
    [(180, .pred (decide (half (g % L.block) = 0))),
      (179, .pred (decide (half (g % L.block) ≠ 0)))]) hr')
  rw [this]
  congr 1
  rw [valueEx_cons_ne _ _ hn.2, valueEx_cons_ne _ _ hn.1, valueEx_nil, valueZ_off d
    (disj_sound zoff_1303 r hr)]

theorem scal_1756 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 3 1756 (factsZ L g 1756 d) 1759 (factsZ L g 1759 d) := by
  have := hR.blk
  have hk := key_eq hR.blk
  intro t h
  sz_seg h [hk]

theorem scal_1759 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 1 1759 (factsZ L g 1759 d) 1760 (factsZ L g 1760 d) := by
  have := hR.blk
  have := hR.r23
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_lt

theorem scal_1760 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 1 1760 (factsZ L g 1760 d) 1761 (factsZ L g 1761 d) := by
  have hn := hR.blk
  intro t h
  seg_fp h using
    sz_vals
    all_goals (simp only [Value.pred.injEq]
               rw [compare_gt_s, toSigned_m1, toSigned32_ofNat]
               simp only [Nat.mod_eq_of_lt (show d.n < 2 ^ 32 by omega),
                 show d.n < 2 ^ 31 by omega, ↓reduceIte]
               simp only [decide_eq_true_eq]
               omega)

theorem scal_1761 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n)
    (hp : pr96 d.e d.n = false) :
    Seg kernel asms L g 3 1761 (factsZ L g 1761 d) 1764 (factsZ L g 1764 d) := by
  intro t h
  sz_seg h [pe0, pe1, hp, Bool.and_true, ↓reduceIte]

/-- **The scalars after the mask** (pcs 1756 to 1763), when the block has no bias but `%p96` is
false: `%p162` to `%p166`, `%p179` and `%p180`. -/
theorem scal_all (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n)
    (hp : pr96 d.e d.n = false) :
    Seg kernel asms L g 8 1756 (factsZ L g 1756 d) 1764 (factsZ L g 1764 d) :=
  Seg.of_len (((scal_1756 d hT hR).comp (scal_1759 d hT hR)).comp
    ((scal_1760 d hT hR).comp (scal_1761 d hT hR hp))) rfl

/-! ### The branch on `%p97` and the whole stretch -/

theorem zoff_1463 : disj (Flow.live 1463) zKeys = true := by decide +kernel
theorem emu_1466 : Assumptions.emuSites.contains 1466 = false := by decide +kernel
theorem live_97a : subS (Flow.live 1756) (Flow.live 1466) = true := by decide +kernel
theorem live_97b : subS (Flow.live 1467) (Flow.live 1466) = true := by decide +kernel
theorem live_97c : 97 ∈ Flow.live 1466 := by decide +kernel

theorem valueZ_97 (d : D) : valueZ L g d 97 = .pred (pr97 d.e d.n) := by
  simp only [valueZ, valuesZ, PTX.Flow.lookupLit, Option.getD_some]

/-- The branch on `%p97` at pc 1466 keeps the facts. -/
theorem bra_97 (d : D) {pick : Bool} (hp : pr97 d.e d.n = pick) :
    Seg kernel asms L g 1 1466 (factsZ L g 1466 d) (if pick then 1756 else 1466 + 1)
      (factsZ L g 1466 d) := by
  refine Seg.bra (K := kernel) Flow.code_1466 ?_ (fun t _ => localRule_bra) (segFree emu_1466)
  have := mem_factsFrom (val := valueZ L g d) live_97c
  rw [valueZ_97, hp] at this
  exact this

/-- **The stretch from the end of the scores to the scalars, when the block is fully visible**
(`%p97`): pcs 1463 to 1756, without the mask. -/
theorem seg_vis (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n)
    (hp : pr97 d.e d.n = true) :
    Seg kernel asms L g 4 1463 (factsZ L g 1463 d) 1756
      (factsZ L g 1756 d) := by
  have h := (seg_p97 d hT hR).comp (bra_97 d hp)
  exact Seg.of_len (h.weaken_end fun R hF => holds_factsFrom_mono hF
    (subS_sound _ _ live_97a)) rfl

/-- **The stretch from the end of the scores to the scalars, when part of the block is masked**
(not `%p97`): pcs 1463 to 1756. -/
theorem seg_masked (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n)
    (hp : pr97 d.e d.n = false) :
    Seg kernel asms L g 4 1463 (factsZ L g 1463 d) 1467
      (factsZ L g 1467 d) := by
  have h := (seg_p97 d hT hR).comp (bra_97 d hp)
  exact Seg.of_len (h.weaken_end fun R hF => holds_factsFrom_mono hF
    (subS_sound _ _ live_97b)) rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
