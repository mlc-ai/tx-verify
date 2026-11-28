-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteJ
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.Fold
import Kernels.InklingRelDecode.Flow.Code.Part035
import Lemmas.Flow.TypedFloatJ
import Lemmas.Flow.StepsQFOp
@[expose] public section
/-! # The strict step of the last shuffle of the rescale decision (pc 2255) -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat} {i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- **The first minimum of the rescale decision** (pc 2256) is the minimum word. -/
theorem seg_rmin {F G : List (Nat × Value)} (a x : Value) (h1 : (1544, a) ∈ F) (h2 : (1545, x) ∈ F)
    (hG : ∀ p ∈ G, p = (1546, Lib.minWord a x) ∨ (p ∈ F ∧ p.1 ≠ 1546)) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 2256 F 2257 G :=
  segQ_minE (R := LateR' L g) Flow.code_2256 (by decide) (by omega) (by omega) (by omega) h1 h2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hG


theorem dat32_regs {t : TState} {pc r : Nat} {x : Value} (hr : t.regs r = some x)
    (hT : TypedF (lateQt pc) t) (hd : d32 (lateQt pc) r = true) : Dat32 x := by
  obtain ⟨y, hy, h⟩ := d32_ok hd hT
  rw [hr] at hy
  cases hy
  exact h

/-- **The comparison of the minimum word with one** (pc 2257) is the rescale decision. -/
theorem seg_rcmp {F G : List (Nat × Value)} (a x : Value) (h1 : (1544, a) ∈ F) (h2 : (1545, x) ∈ F)
    (h3 : (1546, Lib.minWord a x) ∈ F)
    (hG : ∀ p ∈ G, p = (170, Value.pred (Control.skipRescale L g a x)) ∨ (p ∈ F ∧ p.1 ≠ 170)) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 2257 F 2258 G := by
  refine SegQ.tauAll _ (segQF_set (d := 170) (tg := .old .pred)
    (v := Value.pred (Control.skipRescale L g a x)) Flow.code_2257 (by decide) (fun t ht hT => ?_)
    (fun _ _ _ => ⟨_, rfl⟩) (by decide +kernel) hG)
  obtain ⟨hpc, -, -, -, hregs⟩ := ht
  have ra := holds_mem hregs h1
  have rx := holds_mem hregs h2
  have rm := holds_mem hregs h3
  have da := dat32_regs ra hT (by decide +kernel)
  have dx := dat32_regs rx hT (by decide +kernel)
  have dm := dat32_regs rm hT (by decide +kernel)
  obtain ⟨m0, hm0, -⟩ := minE_total da dx
  have hmw : Lib.minWord a x = m0 := by simp [Lib.minWord, hm0]; rfl
  obtain ⟨r, hr⟩ := setpE_total (c := .unord .ge) (fz := false) (by decide) dm.1
    (f32Dat_bits (BitVec.ofNat 64 1065353216))
  have hr' : setpE (.unord .ge) false (Lib.minWord a x) (b32 1065353216) = .ok r := hr
  rw [Control.rescale_cmp (L := L) (g := g) hpc rm, hr']
  have hq : Control.skipRescale L g a x = r := by
    rw [Control.skipRescale_eq, hm0, ← hmw]
    simp [Except.bind, hr', Except.toOption]
  simp [Except.map, hq]

/-- The facts the rescale decision starts from: the site's, the received word. -/
noncomputable abbrev DF (e : Control.Entry) (L : Launch) (g : Nat) (i : Nat) (v : Control.Carry)
    (w : Data.Vals) (x : Value) (pc : Nat) : List (Nat × Value) :=
  (1545, x) :: (Data.dF L ⟨⟨.shfl12, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive pc)
    (Control.valueOf e L g ⟨.shfl12, i, v⟩))

theorem df_ne (x : Value) {pc : Nat} (hpc : ∀ r ∈ Control.ctlLive pc, r ≠ 1546 ∧ r ≠ 170) :
    ∀ p ∈ DF e L g i v w x pc, p.1 ≠ 1546 ∧ p.1 ≠ 170 := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp
  rcases List.mem_append.mp hp with h | h
  · have : p.1 ∈ Data.dKeys .shfl12 := by
      rw [← Data.dFS_keys L .shfl12 w]
      exact List.mem_map_of_mem h
    revert this
    simp only [Data.dKeys, Data.inRound]
    simp
    omega
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact hpc r hr

/-- **The rescale decision** (pcs 2256 to 2258) leaves its predicate among the facts. -/
theorem span12_cmp (x : Value) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 2256
      (DF e L g i v w x 2256) 2258
      ((170, Value.pred (Control.skipRescale L g (Control.valueOf e L g ⟨.shfl12, i, v⟩ 1544) x)) ::
        (1546, Lib.minWord (Control.valueOf e L g ⟨.shfl12, i, v⟩ 1544) x) ::
          DF e L g i v w x 2256) := by
  have h1 : (1544, Control.valueOf e L g ⟨.shfl12, i, v⟩ 1544) ∈ DF e L g i v w x 2256 :=
    List.mem_cons_of_mem _ (List.mem_append_right _ (mem_factsFrom (by decide +kernel)))
  refine SegQ.comp (b := 2257) (G := (1546, Lib.minWord (Control.valueOf e L g ⟨.shfl12, i, v⟩ 1544)
    x) :: DF e L g i v w x 2256) (seg_rmin _ x h1 (List.mem_cons_self ..) ?_) ?_
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inl rfl
    · exact .inr ⟨hp, (df_ne x (by decide +kernel) p hp).1⟩
  · refine seg_rcmp _ x (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (List.mem_cons_self ..) ?_
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inl rfl
    · refine .inr ⟨hp, ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · simp
      · exact (df_ne x (by decide +kernel) p hp).2

/-- The tail of a round whose rescale is skipped: the branch goes to the update. -/
theorem span12_true (x : Value)
    (hq : Control.skipRescale L g (Control.valueOf e L g ⟨.shfl12, i, v⟩ 1544) x = true) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 2256
      (DF e L g i v w x 2256) 999 (UG e L g .shfl12 i v w) := by
  refine (span12_cmp x).comp (SegQ.comp (b := 949) (G := (170, Value.pred (Control.skipRescale L g
    (Control.valueOf e L g ⟨.shfl12, i, v⟩ 1544) x)) :: (1546, Lib.minWord
    (Control.valueOf e L g ⟨.shfl12, i, v⟩ 1544) x) :: DF e L g i v w x 2256)
    (SegQ.tauAll _ (SegQF.braPS (qt := lateQt) true Flow.code_2258
    (fun _ hR => holds_mem hR (by rw [hq]; exact List.mem_cons_self ..))
    (fun t _ ha => Lib.bra_rule t _ ha) (segFree (by decide)) (by decide +kernel))) ?_)
  refine SegQ.fromFacts ?_ (upd_tail (Or.inr (Or.inl rfl)) w)
  intro p hp
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_))
  rcases List.mem_append.mp hp with h | h
  · exact List.mem_append_left _ h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact List.mem_append_right _ (mem_factsFrom
      ((by decide +kernel : ∀ r ∈ Control.ctlLive 949, r ∈ Control.ctlLive 2256) r hr))

theorem val_1611 (e : Control.Entry) (L : Launch) (g : Nat) (d : Control.D) :
    Control.valueOf e L g d 1611 = Control.basePlus (Control.basePlus e.base 256)
      ((Lib.word d.held.base).toNat % 4 * 2 ^ 21) := by
  simp [Control.valueOf]

/-- The tail of a round whose rescale is not skipped: the branch falls through to the load. -/
theorem span12_false (e0 : Control.Entry) (x : Value)
    (hq : Control.skipRescale L g
      (Control.valueOf {e0 with base := b32 0} L g ⟨.shfl12, i, v⟩ 1544) x = false) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 2256
      (DF {e0 with base := b32 0} L g i v w x 2256) 2260
      (Data.dF L ⟨⟨.shfl12, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 2260)
        (Control.valueOf {e0 with base := b32 0} L g ⟨.shfl12, i, v⟩)) := by
  refine (span12_cmp x).comp (SegQ.comp (b := 2259) (G := (170, Value.pred (Control.skipRescale L g
    (Control.valueOf {e0 with base := b32 0} L g ⟨.shfl12, i, v⟩ 1544) x)) :: (1546, Lib.minWord
    (Control.valueOf {e0 with base := b32 0} L g ⟨.shfl12, i, v⟩ 1544) x) ::
    DF {e0 with base := b32 0} L g i v w x 2256)
    (SegQ.tauAll _ (SegQF.braPS (qt := lateQt) false Flow.code_2258
    (fun _ hR => holds_mem hR (by rw [hq]; exact List.mem_cons_self ..))
    (fun t _ ha => Lib.bra_rule t _ ha) (segFree (by decide)) (by decide +kernel))) ?_)
  refine SegQ.fromFacts (F' := Data.dF L ⟨⟨.shfl12, i, v⟩, w⟩ ++ factsFrom (Control.ctlLive 2259)
    (Control.valueOf {e0 with base := b32 0} L g ⟨.shfl12, i, v⟩)) ?_ ?_
  · intro p hp
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_))
    rcases List.mem_append.mp hp with h | h
    · exact List.mem_append_left _ h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact List.mem_append_right _ (mem_factsFrom
        ((by decide +kernel : ∀ r ∈ Control.ctlLive 2259, r ∈ Control.ctlLive 2256) r hr))
  · refine SegQ.tauAll _ ?_
    simp only [Data.dF, Data.dFS, Data.inRound, Data.alphaFacts, ↓reduceIte, List.cons_append,
      List.nil_append]
    late_ctl 2259, 2260 using
      rw [val_1611]
      simp [Control.basePlus, Control.u32, Lib.word, b32, Lib.sum_bits]
      congr 1
      simp [Value.regBits, truncBits, BitVec.toNat_ofNat]
      omega

theorem start12 (x : Value) : ∀ p ∈ DF e L g i v w x 2256,
    p ∈ (1545, x) :: (Data.code e L g).facts ⟨⟨.shfl12, i, v⟩, w⟩ := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact List.mem_cons_self ..
  refine List.mem_cons_of_mem _ ?_
  rcases List.mem_append.mp hp with h | h
  · exact List.mem_append_right _ h
  · exact ctl_in (w := w) (p := 2255) (q := 2256) .shfl12 (by decide +kernel)
      (by decide +kernel) p h

/-- **The last shuffle of the rescale decision** continues at the update, or at the load. -/
theorem sstep_shfl12 (e0 : Control.Entry) (ev : Event) :
    (Data.code {e0 with base := b32 0} L g).StepForQP (QTF lateQt)
      (TauAll kernel Assumptions.all L g (LateR' L g)) LWf ⟨⟨.shfl12, i, v⟩, w⟩ ev := by
  intro t u ins hat hinv hc hQ hw hf hP
  have hr : ∀ q ∈ (Data.code {e0 with base := b32 0} L g).facts ⟨⟨.shfl12, i, v⟩, w⟩,
      q.1 ≠ 1545 := facts_ne (by dsimp only; decide +kernel) (by dsimp only; decide +kernel)
  have hsrc : (1544, Control.valueOf {e0 with base := b32 0} L g ⟨.shfl12, i, v⟩ 1544) ∈
      (Data.code {e0 with base := b32 0} L g).facts ⟨⟨.shfl12, i, v⟩, w⟩ :=
    List.mem_append_left _ (mem_factsFrom (by dsimp only; decide +kernel))
  have hbf : ∀ ev' : Event, LWf ev' → ev'.pc = (Data.code {e0 with base := b32 0} L g).pc
      ⟨⟨.shfl12, i, v⟩, w⟩ → ∀ m av bv cv recv ok, ev'.kind = .shfl m av bv cv recv ok →
      Dat32 recv := fun _ he hpc m av bv cv recv ok hk =>
    he.bfly (hpc ▸ (by change 2255 ∈ _; decide)) m av bv cv recv ok hk
  have e1 : (Data.code {e0 with base := b32 0} L g).pc ⟨⟨.shfl12, i, v⟩, w⟩ = 2255 := by
    change Site.pc .shfl12 = 2255
    decide +kernel
  have key := Code.shflOpFP (C := Data.code {e0 with base := b32 0} L g) (qt := lateQt) (Wf := LWf)
    (P := TauAll kernel Assumptions.all L g (LateR' L g)) (d := ⟨⟨.shfl12, i, v⟩, w⟩)
    (f := fun x => if Control.skipRescale L g (Control.valueOf {e0 with base := b32 0} L g
      ⟨.shfl12, i, v⟩ 1544) x then ⟨⟨.bar20, i, v⟩, updW L w⟩ else ⟨⟨.ldO, i, v⟩, w⟩)
    (r := 1545) (tr := .dat32) (Pv := Dat32) Flow.code_2255 hr hsrc
  have hn : ∀ m bv cv recv ok, Dat32 recv → (Data.code {e0 with base := b32 0} L g).next
      ⟨⟨.shfl12, i, v⟩, w⟩ ⟨2255, .shfl m (Control.valueOf {e0 with base := b32 0} L g
        ⟨.shfl12, i, v⟩ 1544) bv cv recv ok⟩ = some (some (if Control.skipRescale L g
        (Control.valueOf {e0 with base := b32 0} L g ⟨.shfl12, i, v⟩ 1544) recv then
        ⟨⟨.bar20, i, v⟩, updW L w⟩ else ⟨⟨.ldO, i, v⟩, w⟩)) := by
    intro m bv cv recv ok _
    by_cases hq : Control.skipRescale L g (Control.valueOf {e0 with base := b32 0} L g
        ⟨.shfl12, i, v⟩ 1544) recv = true
    · simp [Data.code, Data.succ, Control.next, Data.record, hq]
    · simp [Data.code, Data.succ, Control.next, Data.record, hq]
  refine key (fun hf hk => hop_bfly hf hk) hbf (fun x hx => ⟨x, rfl, hx⟩) hn rfl rfl
    (by change afterF lateQt 2255 _ = true; decide +kernel) ?_ ev ins hat hinv hc hQ hw hf hP
  intro x hx
  have hinv' : (Data.code {e0 with base := b32 0} L g).inv ⟨⟨.shfl12, i, v⟩, w⟩ := hinv
  split
  · rename_i hq
    refine ⟨rfl, rfl, Control.body_inv hinv' rfl rfl, ?_⟩
    have e2 : (Data.code {e0 with base := b32 0} L g).pc ⟨⟨.bar20, i, v⟩, updW L w⟩ = 999 := by
      change Site.pc .bar20 = 999
      decide +kernel
    rw [e1, e2]
    exact (SegQ.fromFacts (start12 x) (span12_true x hq)).comp (SegQ.weaken
      fun _ hR => holds_of_forall fun p hp => holds_mem hR
        (swap_mem (ctl_out (w := updW L w) .bar20 (by decide +kernel) p hp)))
  · rename_i hq
    refine ⟨rfl, rfl, Control.body_inv hinv' rfl rfl, ?_⟩
    have e2 : (Data.code {e0 with base := b32 0} L g).pc ⟨⟨.ldO, i, v⟩, w⟩ = 2260 := by
      change Site.pc .ldO = 2260
      decide +kernel
    rw [e1, e2]
    exact (SegQ.fromFacts (start12 x) (span12_false e0 x (by simpa using hq))).comp (SegQ.weaken
      fun _ hR => holds_of_forall fun p hp => holds_mem hR
        (swap_mem (ctl_out (w := w) .ldO (by decide +kernel) p hp)))
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
