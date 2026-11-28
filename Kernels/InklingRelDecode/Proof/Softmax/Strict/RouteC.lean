-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteB
import Kernels.InklingRelDecode.Proof.Softmax.Data.Init
import Kernels.InklingRelDecode.Proof.Softmax.Data.Constants
import Kernels.InklingRelDecode.Flow.Code
import Lemmas.Flow.BarSyncNone
@[expose] public section
/-! The strict step of the barrier before the setup -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat}

theorem bz_head {v : Control.Carry} (hT : g % L.block < 256) (ok : e.Ok) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 576
      (BF e L g v 576) 600 (BD e L g v 600) :=
  pre_typed 576 600 (((bz_576 hT ok).comp ((bz_580 hT ok).comp ((bz_584 hT ok).comp
    ((bz_585 hT ok).comp ((bz_586 hT ok).comp ((bz_587 hT ok).comp ((bz_589 hT ok).comp
    ((bz_597 hT ok).comp ((bz_598 hT ok).comp (bz_599 hT ok)))))))))).of_len (by omega))

theorem bz_600 {v : Control.Carry} (hs : ScaleOk L) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 600
      (BD e L g v 600) 601 (BF e L g v 601) := by
  obtain ⟨y, hy, h0⟩ := hs
  refine seg_div hy h0 (by simp) (List.mem_cons_of_mem _ (bf_entry 600))
    (fun p hp => ?_) (fun p hp => ?_)
  · exact List.mem_cons_of_mem _ (sub_facts (fun _ h => h) (by decide +kernel) p hp)
  · rcases List.mem_append.mp hp with h | h
    · obtain rfl : p = (525, Data.scaleVal L) := by
        simpa [Data.dF, Data.dFS, Data.entryFact] using h
      simp
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact (by decide +kernel : ∀ r ∈ Control.ctlLive 601, r ≠ 805) r hr

theorem bz_601 {v : Control.Carry} (hs : ScaleOk L) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 601
      (BF e L g v 601) 602 (PF e L g v 602) := by
  obtain ⟨y, hy, -⟩ := hs
  refine SegQ.tauAll _ (segQF_set (d := 498) (tg := .dat32) (v := Data.scaleW L)
    (OItem.instrB_eq (Lib.scale_at (L := L) (g := g)).1.1) (by decide)
    (fun t ht _ => exec_scale hy (bf_entry 601) ht)
    (fun _ _ _ => ⟨_, rfl, scaleW_float hy ▸ dat32_float _⟩) (by decide +kernel) (fun p hp => ?_))
  simp only [PF, Data.dF, Data.dFS, List.cons_append, List.nil_append, List.mem_cons] at hp
  rcases hp with rfl | rfl | h
  · exact .inr ⟨bf_entry 601, by simp [Data.entryFact]⟩
  · exact .inl rfl
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    obtain ⟨h1, h2⟩ := (by decide +kernel : ∀ r ∈ Control.ctlLive 602,
      r ∈ Control.ctlLive 601 ∧ r ≠ 498) r hr
    exact .inr ⟨List.mem_append_right _ (mem_factsFrom h1), h2⟩

theorem bz_tail {v : Control.Carry} (hT : g % L.block < 256) (ok : e.Ok) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 602
      (PF e L g v 602) 679 (PF e L g v 679) :=
  pre_typed 602 679 ((bz_602 hT ok |>.comp (bz_603 hT ok) |>.comp (bz_606 hT ok)
    |>.comp (bz_607 hT ok) |>.comp (bz_608 hT ok) |>.comp (bz_609 hT ok)
    |>.comp (bz_610 hT ok) |>.comp (bz_611 hT ok) |>.comp (bz_612 hT ok)
    |>.comp (bz_613 hT ok) |>.comp (bz_614 hT ok) |>.comp (bz_615 hT ok)
    |>.comp (bz_616 hT ok) |>.comp (bz_623 hT ok) |>.comp (bz_630 hT ok)
    |>.comp (bz_637 hT ok) |>.comp (bz_644 hT ok) |>.comp (bz_651 hT ok)
    |>.comp (bz_658 hT ok) |>.comp (bz_665 hT ok) |>.comp (bz_672 hT ok)).of_len (by omega))

/-- **The setup from the barrier to the first preload**: pcs 576 to 680. -/
theorem bar0_span {v : Control.Carry} (hT : g % L.block < 256) (ok : e.Ok) (hs : ScaleOk L) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 576
      (BF e L g v 576) 680 (PF e L g v 680) := by
  refine (bz_head hT ok).comp ((bz_600 hs).comp ((bz_601 hs).comp ((bz_tail hT ok).comp ?_)))
  refine mv_seg (p := 678) (r := 263) (by omega)
    ((fp3_of (a := 679) (b := 680) (by decide +kernel)).mono (by omega) (by omega))
    (by decide +kernel) (fun q hq => ?_) (fun q hq => ?_)
  · rcases List.mem_append.mp hq with h | h
    · have h' : q ∈ [(525, Data.scaleVal L), (498, Data.scaleW L)] := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl <;> simp
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact (by decide +kernel : ∀ r ∈ Control.ctlLive 680, r ≠ 263) r hr
  · exact sub_facts (fun _ h => h) (by decide +kernel) q hq

theorem pre_sat : ∀ j < 63, tagsSatF (lateQt (680 + 2 * j + 1)) (lateQt (680 + 2 * j)) = true := by
  decide +kernel

theorem pre_sat' : tagsSatF (lateQt 807) (lateQt 806) = true := by decide +kernel

/-- **A preload and the move after it** under a false guard keep the facts. -/
theorem pskip_pair {F : List (Nat × Value)} (j : Nat) (hj : j < 63)
    (hg : (85, Value.pred false) ∈ F)
    (hw : ∀ q ∈ F, q.1 < 263 ∨ 326 < q.1) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) (680 + 2 * j) F
      (680 + 2 * j + 2) F := by
  obtain ⟨a, hc, -⟩ := ldOk_sound (pre_ld j hj)
  refine SegQ.comp (b := 680 + 2 * j + 1) (SegQ.tauAll _ (SegQF.skipGS (qt := lateQt) hc
    (fun _ hR => holds_mem hR hg) rfl (fun _ h => h) (pre_sat j hj))) ?_
  refine mv_seg (p := 680 + 2 * j) (r := 264 + j) (by omega)
    ((fp3_of (a := 681) (b := 807) (by decide +kernel)).mono (by omega) (by omega))
    (pre_mv j hj) (fun q hq => ?_) (fun _ h => h)
  have := hw q hq
  omega

theorem pskip_upto {F : List (Nat × Value)} (hg : (85, Value.pred false) ∈ F)
    (hw : ∀ q ∈ F, q.1 < 263 ∨ 326 < q.1) :
    ∀ k ≤ 63, SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 680 F
      (680 + 2 * k) F := by
  intro k
  induction k with
  | zero => exact fun _ => SegQ.weaken fun _ h => h
  | succ k ih => exact fun hk => (ih (by omega)).comp (pskip_pair k (by omega) hg hw)

/-- **The preloads under a false guard**: the span to the setup's next stretch. -/
theorem pskip_all {F : List (Nat × Value)} (hg : (85, Value.pred false) ∈ F)
    (hw : ∀ q ∈ F, q.1 < 263 ∨ 326 < q.1) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 680 F 807 F := by
  refine (pskip_upto hg hw 63 le_rfl).comp ?_
  obtain ⟨a, hc, -⟩ := ldOk_sound pre_last_ld
  exact SegQ.tauAll _ (SegQF.skipGS (qt := lateQt) hc (fun _ hR => holds_mem hR hg) rfl
    (fun _ h => h) pre_sat')

variable {i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- **The barrier before the setup** continues at the first preload, or past the preloads. -/
theorem sstep_bar0 (hs : ScaleOk L) (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.bar0, i, v⟩, w⟩ ev := by
  refine Code.StepForQP.ofInv fun hinv => ?_
  obtain rfl : i = 0 := hinv.init (.inr rfl)
  rcases em (Control.preEnabled e (g % L.block) = true) with en | en
  · apply adv_soft (d := ⟨⟨.bar0, 0, v⟩, w⟩)
      (dn := ⟨⟨.pre 0, 0, v⟩, {w with ld := fun _ => Data.dflt}⟩) (p := 575) rfl Flow.code_575
      (fun _ hf => fires_barSync_next hf)
      (fun ev => by simp [Data.succ, Control.next, Data.record, en, Data.loopB])
      (fun hi => ⟨hi.entry, hi.thread, hi.bound, fun _ => rfl, fun _ _ => ⟨rfl, en⟩, nofun, nofun,
        fun _ _ _ h => (h _ rfl).elim⟩) (by decide +kernel) (by decide +kernel) ?_
    exact bar0_span hinv.thread hinv.entry hs
  · have hb : Data.loopB (Control.loopSite e (g % L.block) 0) := by
      rcases loopSite_cases e (g % L.block) 0 with h | h | h <;> simp [Data.loopB, h]
    apply adv_soft (d := ⟨⟨.bar0, 0, v⟩, w⟩) (dn := ⟨⟨Control.loopSite e (g % L.block) 0, 0, v⟩,
      { w with
        m := b32 4286578688, l := b32 0, cur := fun _ => Data.dflt, ld := fun _ => Data.dflt }⟩)
      (p := 575) rfl Flow.code_575 (fun _ hf => fires_barSync_next hf)
      (fun ev => by simp [Data.succ, Control.next, Data.record, en, hb])
      (fun hi => Control.loop_inv (i := 0) hi.entry hi.thread (Nat.zero_le _))
      (by decide +kernel) (by decide +kernel) ?_
    have h85 : Control.valueOf e L g ⟨.arrive, 0, v⟩ 85 = .pred false := by
      simp [Control.valueOf, Control.scalarValue, en]
    have hz : (85, Value.pred false) ∈ PF e L g v 680 :=
      List.mem_append_right _ (h85 ▸ mem_factsFrom (by decide +kernel))
    have hw : ∀ q ∈ PF e L g v 680, q.1 < 263 ∨ 326 < q.1 := by
      intro q hq
      rcases List.mem_append.mp hq with h | h
      · simp only [Data.dF, Data.dFS, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> simp [Data.entryFact]
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        exact (by decide +kernel : ∀ r ∈ Control.ctlLive 680, r < 263 ∨ 326 < r) r hr
    refine (bar0_span hinv.thread hinv.entry hs).comp ((pskip_all hz hw).comp ?_)
    refine SegQ.fromFacts (F' := PF e L g v 807) (sub_facts (fun _ h => h) (by decide +kernel))
      (SegQ.endIn (pre_route hinv.thread hinv.entry) fun p hp => ?_)
    rcases List.mem_append.mp hp with h | h
    · exact List.mem_append_left _ (dF_loop e (g % L.block) 0 _ _ _ p h)
    · exact List.mem_append_right _ h
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
