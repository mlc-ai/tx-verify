-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmStgB
public import Lemmas.Flow.FloatDat

@[expose] public section

/-! # The step of the S tile's wait (pc 1298)

After `tcgen05.wait::ld` the thread runs the score stage's first half (the head, the bias
widening, the scores, the mask and the scalars, pcs 1299 to 1764) and the row maximum (pcs 1764 to
1837) and stops at the shuffle of the row maximum (pc 1838). The machine follows every S word: the
state there is `D.afterWaitT` (the words of the columns as the unpacks give them, `D.finT`); where
an instruction of the stage faults (`D.s1Ok` fails) the thread is dead and `next` is `none`. The
pieces are those of `SmTotA` and `SmTotB` for the words that depend on the S words, and the
integer pieces of `SmScG`, `SmScZ`, `SmScP`, which hold in every state. Where the S words are
`f32` numbers the state is `D.afterWait`, the state of `D.fin` (`afterWaitT_eq`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Softmax
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-- `tcgen05.wait::ld` fires its wait and continues at the next instruction. -/
theorem fires_waitLd_next {pc : Nat} {t u : TState} {e : Event} (hb : L.block % 32 = 0)
    (hf : Fires pc (eventTmpl asms L g t .tcWaitLd) e (some u)) :
    u = PTX.next t ∧ e = ⟨pc, .tc .waitLd⟩ := by
  simp only [eventTmpl, tcTmpl, hb, ofExec, pure, Except.pure, ↓reduceIte, Fires] at hf
  exact ⟨Option.some.inj hf.2, hf.1⟩

theorem live_1838_cases : ∀ r ∈ Flow.live 1838, r = 1520 ∨ r = 179 ∨ r = 180 ∨
    ((List.range 64).any fun j => colReg j == r) = true ∨
    (r ∉ zKeys ∧ ¬ (876 ≤ r ∧ r < 940) ∧ ¬ (2447 ≤ r ∧ r < 2479) ∧ (¬ XKey r ∨ r = 506) ∧
      (r < 1415 ∨ 1521 ≤ r)) := by
  decide +kernel

theorem rm_keys : ∀ k ∈ (rmSt 74).map Prod.fst, 1415 ≤ k ∧ k < 1521 := by decide +kernel

theorem rm_none {r : Nat} (h : r < 1415 ∨ 1521 ≤ r) : (rmSt 74).lookup r = none :=
  lookup_none_of_keys _ (fun k hk => by have := rm_keys k hk; omega)

/-- The state of `D.fin` after the S tile's wait. -/
def D.afterWait (L : Launch) (g : Nat) (d : D) : D :=
  { d with site := .shfl5, stg := { d.stg with fsv := (D.fin L g d).sv } }

@[simp] theorem D.afterWaitT_site (d : D) : (D.afterWaitT L g d).site = .shfl5 := rfl

@[simp] theorem D.afterWait_site (d : D) : (D.afterWait L g d).site = .shfl5 := rfl

/-- On score words the thread's maximum (the register the shuffle of the row maximum sends) is the
value of its extended-real maximum. -/
theorem ownV_fsv {d : D} (hw : ∀ k < 64, ScoreWord (d.stg.fsv k).1) :
    (ownV fun k => (d.stg.fsv k).1) = erealValue .f32 d.ownE :=
  ownV_eq hw

/-- A register of the tree that no unpack writes holds the value of a `maxE` outcome. -/
theorem rv_max (w : Nat → Value) : ∀ c r, (rsSt c).lookup r = some none →
    ∃ vs, (rvSt w c).lookup r = some (okVal (b32 0) (maxE vs)) := by
  intro c
  induction c with
  | zero => intro r h; simp [rsSt] at h
  | succ c ih =>
    intro r h
    rcases hi : rmCode[c]? with _ | i
    · have hl : rmCode.length ≤ c := List.getElem?_eq_none_iff.mp hi
      have e1 : rmCode.take (c + 1) = rmCode.take c := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp only [rsSt, e1] at h
      simp only [rvSt, e1]
      exact ih r h
    · rw [rsSt_succ hi] at h
      rw [rvSt_succ hi]
      cases i with
      | unp a b q =>
        simp only [RI.updS, RI.updV, List.lookup] at h ⊢
        by_cases hb : r = b
        · subst hb; simp at h
        · simp only [beq_false_of_ne hb] at h ⊢
          by_cases ha : r = a
          · subst ha; simp at h
          · simp only [beq_false_of_ne ha] at h ⊢
            exact ih r h
      | mx2 d a b =>
        simp only [RI.updS, RI.updV, List.lookup] at h ⊢
        by_cases hd : r = d
        · subst hd; exact ⟨_, by simp; rfl⟩
        · simp only [beq_false_of_ne hd] at h ⊢
          exact ih r h
      | mx3 d a b e =>
        simp only [RI.updS, RI.updV, List.lookup] at h ⊢
        by_cases hd : r = d
        · subst hd; exact ⟨_, by simp; rfl⟩
        · simp only [beq_false_of_ne hd] at h ⊢
          exact ih r h

theorem rs_root : (rsSt 74).lookup (R 1059) = some none := by decide +kernel

/-- **The thread's maximum is a four-byte word**, whatever the words are. -/
theorem ownV_bytes (w : Nat → Value) : (ownV w).bytes = 4 := by
  obtain ⟨vs, hv⟩ := rv_max w 74 (R 1059) rs_root
  unfold ownV lkV
  rw [hv, Option.getD_some]
  rcases hE : maxE vs with e | v
  · rfl
  · obtain ⟨c, hc⟩ := maxE_dat hE
    exact classify_f32_bytes hc

/-! ### The facts at the shuffle -/

/-- The instruction `c` of the tree unpacks the pair `q`. -/
def unpOf (q c : Nat) : Bool :=
  match rmCode[c]? with
  | some (.unp _ _ q') => q' == q
  | _ => false

theorem rm_unp_allB : (List.range 32).all (fun q => (List.range 74).any (unpOf q)) = true := by
  decide +kernel

/-- Every pair register is unpacked by an instruction of the tree. -/
theorem rm_unp_all : ∀ q < 32, ∃ c < 74, ∃ a b, rmCode[c]? = some (.unp a b q) := by
  intro q hq
  have h := List.all_eq_true.mp rm_unp_allB q (List.mem_range.mpr hq)
  obtain ⟨c, hc, hu⟩ := List.any_eq_true.mp h
  refine ⟨c, List.mem_range.mp hc, ?_⟩
  unfold unpOf at hu
  rcases hi : rmCode[c]? with _ | i
  · simp [hi] at hu
  · cases i with
    | unp a b q' =>
      simp only [hi, beq_iff_eq] at hu
      subst hu
      exact ⟨a, b, rfl⟩
    | mx2 => simp [hi] at hu
    | mx3 => simp [hi] at hu

theorem unpackE_ok_bytes {v : Value} (h : (unpackE 64 v).toBool = true) :
    (splitValue 64 v).1.bytes = 4 ∧ (splitValue 64 v).2.bytes = 4 := by
  unfold unpackE at h
  split_ifs at h with hh
  · exact ⟨hh.2.1, hh.2.2⟩
  · cases h

/-- Where the unpacks of the tree have outcomes the words at the shuffle are the unpacked
words. -/
theorem finT_colW {d : D} (hok : D.s1Ok L g d) {k : Nat} (hk : k < 64) :
    (D.finT L g d k).1 = colW (D.s1 L g d) k := by
  obtain ⟨c, hc, a, b, hi⟩ := rm_unp_all (k / 2) (by omega)
  have hu := hok.2 c hc _ hi
  simp only [RI.okV] at hu
  obtain ⟨h0, h1⟩ := unpackE_ok_bytes hu
  have hb : (colW (D.s1 L g d) k).bytes = 4 := by
    unfold colW hW
    split_ifs
    · exact h0
    · exact h1
  simp only [D.finT, hk, ↓reduceIte, dif_pos hb]

theorem s1_frame (d : D) : (D.s1 L g d).e = d.e ∧ (D.s1 L g d).i = d.i ∧
    (D.s1 L g d).m = d.m ∧ (D.s1 L g d).l = d.l ∧ (D.s1 L g d).wd = d.wd ∧
    (D.s1 L g d).vd = d.vd ∧ (D.s1 L g d).pf = d.pf ∧ (D.s1 L g d).stg = d.stg := by
  unfold D.s1
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rv_none {w : Nat → Value} {r : Nat} (h : r < 1415 ∨ 1521 ≤ r) :
    (rvSt w 74).lookup r = none :=
  lookup_none_of_keys' (rvSt_keys w 74) (rm_none h)

/-- **The facts of the row maximum's end are the table of the state at the shuffle.** -/
theorem ovT_eq {d : D} (hok : D.s1Ok L g d) :
    ∀ r ∈ Flow.live 1838, valueEx (valueZ L g (D.s1 L g d))
      (rvSt (colW (D.s1 L g d)) 74) r = valueOf L g (D.afterWaitT L g d) r := by
  intro r hr
  have hfw : ∀ k < 64, (D.finT L g d k).1 = colW (D.s1 L g d) k := fun k hk => finT_colW hok hk
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := s1_frame (L := L) (g := g) d
  rcases live_1838_cases r hr with rfl | rfl | rfl | hw | ⟨hz, h1, h2, hx, hrm⟩
  · have hl : ∃ v, (rvSt (colW (D.s1 L g d)) 74).lookup (R 1059) = some v :=
      lookup_isSome_of_keys (rvSt_keys _ 74) (by rw [rm_root_lookup]; rfl)
    obtain ⟨v, hv⟩ := hl
    rw [show (1520 : Nat) = R 1059 by rfl, valueEx_lkV hv, valueOf_r1061]
    exact (ownV_congr fun k hk => hfw k hk).symm
  · rw [valueEx, rv_none (by omega), Option.getD_none, valueZ_180, valueOf_p180]
    simp only [D.afterWaitT, D.n, blkOf, f1, f2]
  · rw [valueEx, rv_none (by omega), Option.getD_none, valueZ_181, valueOf_p181]
    simp only [D.afterWaitT, D.n, blkOf, f1, f2]
  · obtain ⟨j, hj, hjr⟩ := List.any_eq_true.mp hw
    have hj' : j < 64 := List.mem_range.mp hj
    have hjr' : colReg j = r := by simpa using hjr
    subst hjr'
    have hv := rv_word (colW (D.s1 L g d)) 74 (colReg j) j (rs_word j hj')
    rw [valueEx, hv, Option.getD_some, valueOf_word _ hj']
    exact (hfw j hj').symm
  · rw [valueEx, rv_none hrm, Option.getD_none, valueZ_off _ hz]
    have e1 : valueOf L g (D.s1 L g d) r = valueOf L g d r :=
      valueOf_frameSv (L := L) (g := g) (d := d) (d' := D.s1 L g d) f1 f2 f3 f4 f5 f6 f7
        h1 h2 f8
    rw [e1]
    rcases hx with hx | rfl
    · exact (valueOf_nonX (L := L) (g := g) (d := d) (d' := D.afterWaitT L g d) rfl rfl rfl rfl
        rfl rfl hx).symm
    · rw [valueOf_r45, valueOf_r45]
      simp only [D.afterWaitT]

/-! ### The stage's first half -/

/-- **The score stage's first half on any S words** (pcs 1299 to 1837): the thread reaches the
shuffle of the row maximum with the tree's registers, or is dead where an instruction of the stage
faults. -/
theorem seg_stage1T (d : D) (hT : g % L.block < 128) (hok : d.e.Ok)
    (hR : Rng d.e (g % L.block) d.n) (hb : ∀ k < 64, BfOk (d.wd k)) :
    ∃ n, SegD kernel asms L g n 1299 (factsAt L g 1299 d) 1838
      (factsFrom (Flow.live 1838) (valueEx (valueZ L g (D.s1 L g d))
        (rvSt (colW (D.s1 L g d)) 74))) (D.s1Ok L g d) := by
  by_cases h96 : pr96 d.e d.n = true
  · have e : D.s1 L g d = d := by simp only [D.s1, h96, ↓reduceIte]
    rw [e, ← factsZ_eq d zoff_1299]
    refine ⟨_, (SegD.seg_comp (head_true d hT hok hR h96)
      (seg_rowmaxT (L := L) (g := g) (d1 := d))).iff ⟨fun h => ⟨fun h' => ?_, ?_⟩, fun h => ?_⟩⟩
    · rw [h96] at h'; cases h'
    · rw [e]; exact h
    · have := h.2; rw [e] at this; exact this
  · have h96' : pr96 d.e d.n = false := by simpa using h96
    have hA := head_false d hT hok hR h96'
    have hB := seg_scoresT (L := L) (g := g) d hb
    rw [factsZ_eq _ zoff_1463 |>.symm] at hB
    have hAB := SegD.seg_comp hA hB
    by_cases h97 : pr97 d.e d.n = true
    · have e : D.s1 L g d = d.scoredT 32 := by
        simp only [D.s1, h96', h97, Bool.false_eq_true, ↓reduceIte]
      rw [e]
      have hC := (seg_vis (d.scoredT 32) hT hR h97).comp (scal_all (d.scoredT 32) hT hR h96')
      refine ⟨_, ((hAB.comp_seg hC).comp (seg_rowmaxT (L := L) (g := g)
        (d1 := d.scoredT 32))).iff ⟨fun h => ⟨fun _ => h.1, ?_⟩, fun h => ⟨h.1 h96', ?_⟩⟩⟩
      · rw [e]; exact h.2
      · have := h.2; rw [e] at this; exact this
    · have h97' : pr97 d.e d.n = false := by simpa using h97
      have e : D.s1 L g d = D.maskedT L g d 32 := by
        simp only [D.s1, h96', h97', Bool.false_eq_true, ↓reduceIte]
      rw [e]
      have hC := ((((seg_masked (d.scoredT 32) hT hR h97').comp
        (seg_diffs (d.scoredT 32) hT hR)).comp (seg_preds (d.scoredT 32) hT hR)).comp
        (seg_mask32T (L := L) (g := g) d)).comp (scal_all (D.maskedT L g d 32) hT hR h96')
      refine ⟨_, ((hAB.comp_seg hC).comp (seg_rowmaxT (L := L) (g := g)
        (d1 := D.maskedT L g d 32))).iff ⟨fun h => ⟨fun _ => h.1, ?_⟩,
          fun h => ⟨h.1 h96', ?_⟩⟩⟩
      · rw [e]; exact h.2
      · have := h.2; rw [e] at this; exact this

theorem live_1299_1298 : ∀ r ∈ Flow.live 1299, r ∈ Flow.live 1298 := by decide +kernel

/-- **The wait for the S tile** (pc 1298): the thread runs the stage's first half and the row
maximum to the shuffle of the maximum (pc 1838), whatever the S words are; it is dead where an
instruction of the stage faults (`D.s1Ok`). The range of its integer arithmetic is an entry fact
(`Ent.Ok.rngBlk`, `rngPast`, `rngR23`) and its bias words are `bf16` numbers or zero
(`Inv.wf`). -/
theorem step_waitLd (hb : L.block % 32 = 0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hi : Inv L g d) (hs : d.site = .waitLd) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 1298 := by rw [hs]; rfl
  have hc' : kernel.code[1298]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_tmemWait_1)
  obtain ⟨rfl, -⟩ := fires_waitLd_next hb (hpc ▸ hf)
  have hlate : LateSite d.site := by rw [hs]; trivial
  have hbf : ∀ k < 64, BfOk (d.wd k) := fun k _ => by
    unfold D.wd
    split
    · exact hi.wf k
    · exact Or.inr rfl
  have h1 : At (PTX.next t) 1299 (factsAt L g 1299 d) :=
    at_next_live (pc := 1298) (pc' := 1299) (hpc ▸ h) rfl rfl live_1299_1298
  have hR : Rng d.e (g % L.block) d.n :=
    ⟨hi.ok.rngBlk d.i (hi.late hlate).2.2, hi.ok.rngPast, hi.ok.rngR23, hi.tid⟩
  obtain ⟨n, hseg⟩ := seg_stage1T d hi.tid hi.ok hR hbf
  by_cases hok : D.s1Ok L g d
  · have hn : next L g d e = some (some (D.afterWaitT L g d)) := by
      simp only [next, hs]
      rw [if_pos hok]
      rfl
    obtain ⟨t2, hr2, ht2⟩ := (hseg _ h1).1 hok
    have hat : At t2 (D.afterWaitT L g d).site.pc (facts L g (D.afterWaitT L g d)) :=
      ht2.mono (holds_of_pointwise fun r hr' => by
        rw [holds_mem ht2.2.2.2.2 (Flow.mem_factsFrom (val := valueEx
          (valueZ L g (D.s1 L g d)) (rvSt (colW (D.s1 L g d)) 74)) hr')]
        exact congrArg some (ovT_eq hok r hr'))
    exact .inl (.inr ⟨D.afterWaitT L g d, t2, hn, run_rtg hr2, hat,
      inv_stg (inv_late hi hlate (s := .shfl5) trivial (fun h => absurd h (by simp))) _ _
          (by exact ⟨hi.four.al, hi.four.cm1, hi.four.cm2,
            hi.four.cm3, hi.four.cm4, hi.four.ld, hi.four.m2, hi.four.sw⟩)⟩)
  · exact .inr ⟨by simp only [next, hs]; rw [if_neg hok], (hseg _ h1).2 hok⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
