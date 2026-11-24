-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Signed
public import Lemmas.Flow.Pointer

@[expose] public section

/-! # The start of the softmax warps

After the start barrier the thread computes its warp's index in its stage (`k`, by the signed
remainder sequence), the trip count's last index `n - 1` (the signed ceiling of `sk / 128`,
whose rounding predicate is false, `sk` being a multiple of `128`), its stage's named barrier
and barrier base, and branches past the item loop when the cluster has no item
(`Work.start_branch`). Entering the loop it maps the leader CTA's P-ready barriers (`mapa` to
rank 0), sets the parities, loads the scale parameter and reaches the first statistics poll.
The stage enters the code through selections on `w > 3`: each segment that selects on it is
proved for the warp's value of the comparison (`hb`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow Work

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The state the start computes the facts of. -/
abbrev dB (s : Nat → Value) (m l : Value) : D := ⟨.statsW 0, 0, 0, s, m, l⟩

theorem tileIdx_dB (s : Nat → Value) (m l : Value) : tileIdx L (dB s m l) = 0 := by
  simp [tileIdx, Site.tile0]

theorem bar0_a (hpre : Pre P L mem0) (hw : warpOf L g < 8) (b : Bool)
    (hb : decide (3 < warpOf L g) = b) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 14 1208 (factsAt L g 1207 ⟨.bar0, 0, 0, s, m, l⟩) 1222
      (factsX L g 1222 (dB s m l) [(141, .pred b), (144, .pred false), (993, b32 (kOf L g)),
        (997, b32 (skOf L / 128))]) := by
  intro t h
  have hsk := hpre.skRange
  have hskd := hpre.skDiv128
  have hsk' := skOf_eq hpre
  cases b <;> simp at hb <;> sm_segs h hpre

/-- The trip count is `sk / 128`. -/
theorem trips_eq (hpre : Pre P L mem0) : trips L = skOf L / 128 := by
  have := hpre.skDiv128
  have := hpre.skRange
  simp only [trips, Work.n, Work.sk, skOf_eq hpre]
  omega

/-- The branch past the item loop: the cluster has no item. -/
theorem start_cmp (hpre : Pre P L mem0) (hg : g < L.threads) :
    PTX.compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 (clusterOf L g)))
      (truncBits 32 (BitVec.ofNat 64 (totOf L))) = decide ¬ 0 < items L g :=
  start_branch hpre hg

theorem bar0_b (hpre : Pre P L mem0) (hg : g < L.threads) (hw : warpOf L g < 8) (b : Bool)
    (hb : decide (3 < warpOf L g) = b) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 11 1222
      (factsX L g 1222 (dB s m l) [(141, .pred b), (144, .pred false), (993, b32 (kOf L g)),
        (997, b32 (skOf L / 128))]) 1233
      (factsX L g 1233 (dB s m l) [(145, .pred (decide ¬ 0 < items L g)),
        (403, Prologue.sb L (8 * stOf L g))]) := by
  intro t h
  have hsk := hpre.skRange
  have hskd := hpre.skDiv128
  have hskp := hpre.skPos
  have hsk' := skOf_eq hpre
  have htr := trips_eq hpre
  cases b <;> simp at hb <;> sm_segs h hpre [start_cmp hpre hg]

/-- `mapa` of a barrier of the thread's CTA to rank 0: the leader CTA's barrier. -/
theorem seg_mapa (hpre : Pre P L mem0) (hg : g < L.threads) {pc dd r off : Nat}
    {F : List (Nat × Value)} (hoff : off < 1024)
    (hc : kernel.code[pc]? = some ⟨none, .addr (.mapa false 32 dd (.reg r) (.reg 342))⟩)
    (h1 : (r, Prologue.sb L off) ∈ F) (h2 : (342, b32 0) ∈ F) (hF : ∀ p ∈ F, p.1 ≠ dd)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    Seg kernel asms L g 1 pc F (pc + 1) ((dd, leadPtr L g off) :: F) := by
  intro t hat
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hcl := hpre.cluster
  have hgr := hpre.grid
  have hv := hpre.oneDimLaunch.1
  have hcta : g / L.block < L.grid := cta_lt hg
  have hr1 : t.regs r = some (b32 (L.sharedBase + off)) := holds_mem hat.2.2.2.2 h1
  have hr2 : t.regs 342 = some (b32 0) := holds_mem hat.2.2.2.2 h2
  have hr : readBits L g t 32 (.reg 342) = .ok (BitVec.ofNat 64 0) := by
    simp only [readBits, readReg, hr2, b32, bind, Except.bind, pure, Except.pure,
      truncBits_ofNat (show 0 < 2 ^ 32 by decide) (by decide)]
  refine ⟨_, run_mapa (rv := BitVec.ofNat 64 0) (loc := ⟨.shared, g / L.block, L.sharedBase + off⟩)
    (peer := ⟨.shared, 2 * (g / L.block / 2), L.sharedBase + off⟩) hc hat
    (readSharedAddress_b32 hg hcta (by omega) hr1) hr ?_ asms_localRule_none hsf, At.set hat hF⟩
  have hX : 2 * (g / L.block / 2) < L.grid := by omega
  simp only [Launch.mapShared, Launch.peerCta, Launch.oneDim_clusterOfCta hv,
    Launch.oneDim_clusterStart hv, Launch.oneDim_clusterSizeOf hv, hcl, BitVec.toNat_ofNat,
    Nat.zero_mod]
  simp [hcta, hX, Nat.mul_comm]

/-- To the first `mapa`. -/
theorem bar0_c (hpre : Pre P L mem0) (hw : warpOf L g < 8) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 1 1234
      (factsX L g 1233 (dB s m l) [(145, .pred (decide ¬ 0 < items L g)),
        (403, Prologue.sb L (8 * stOf L g))]) 1235
      (factsX L g 1235 (dB s m l) [(403, Prologue.sb L (8 * stOf L g)),
        (1004, Prologue.sb L (144 + 8 * stOf L g))]) := by
  intro t h
  sm_segs h hpre

/-- Between the two `mapa`. -/
theorem bar0_e (hpre : Pre P L mem0) (hw : warpOf L g < 8) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 1 1236
      ((405, leadPtr L g (144 + 8 * stOf L g)) :: factsX L g 1235 (dB s m l)
        [(403, Prologue.sb L (8 * stOf L g)), (1004, Prologue.sb L (144 + 8 * stOf L g))]) 1237
      (factsX L g 1237 (dB s m l) [(1005, Prologue.sb L (160 + 8 * stOf L g))]) := by
  intro t h
  sm_segs h hpre

/-- After the second `mapa`, to the load of the scale. -/
theorem bar0_f (hpre : Pre P L mem0) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 3 1238
      ((406, leadPtr L g (160 + 8 * stOf L g)) :: factsX L g 1237 (dB s m l)
        [(1005, Prologue.sb L (160 + 8 * stOf L g))]) 1241 (factsAt L g 1241 (dB s m l)) := by
  intro t h
  sm_segs h hpre [tileIdx_dB]

/-- After the load of the scale, to the stage's selection. -/
theorem bar0_g (hpre : Pre P L mem0) (hw : warpOf L g < 8) (b : Bool)
    (hb : decide (3 < warpOf L g) = b) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 3 1242 (factsAt L g 1242 (dB s m l)) 1245
      (factsX L g 1245 (dB s m l) [(146, .pred b)]) := by
  intro t h
  cases b <;> simp at hb <;> sm_segs h hpre

/-- From the stage's selection to the first statistics poll. -/
theorem bar0_h (hpre : Pre P L mem0) (hw : warpOf L g < 8) (b : Bool)
    (hb : decide (3 < warpOf L g) = b) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 14 1245 (factsX L g 1245 (dB s m l) [(146, .pred b)]) 1259
      (factsAt L g 1259 (dB s m l)) := by
  intro t h
  cases b <;> simp at hb <;> sm_seg h hpre

/-- No item: from the branch to the tail's statistics poll. -/
theorem bar0_t (hpre : Pre P L mem0) (hw : warpOf L g < 8) (b : Bool)
    (hb : decide (3 < warpOf L g) = b) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 5 3741
      (factsX L g 1233 (dB s m l) [(145, .pred (decide ¬ 0 < items L g)),
        (403, Prologue.sb L (8 * stOf L g))]) 3746
      (factsAt L g 3746 ⟨.statsW 3, 0, 0, s, m, l⟩) := by
  have h1 : Seg kernel asms L g 1 3741
      (factsX L g 1233 (dB s m l) [(145, .pred (decide ¬ 0 < items L g)),
        (403, Prologue.sb L (8 * stOf L g))]) 3742
      (factsX L g 3742 ⟨.statsW 3, 0, 0, s, m, l⟩ [(289, .pred b)]) := by
    intro t h
    cases b <;> simp at hb <;> sm_segs h hpre
  have h2 : Seg kernel asms L g 4 3742
      (factsX L g 3742 ⟨.statsW 3, 0, 0, s, m, l⟩ [(289, .pred b)]) 3746
      (factsAt L g 3746 ⟨.statsW 3, 0, 0, s, m, l⟩) := by
    intro t h
    cases b <;> simp at hb <;> sm_segs h hpre
  exact Seg.comp h1 h2

/-- The load of the scale parameter. -/
theorem bar0_p (hpre : Pre P L mem0) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 1 1241 (factsAt L g 1241 (dB s m l)) 1242
      (factsAt L g 1242 (dB s m l)) :=
  fun _ h => ld_scale hpre Flow.code_1241 h
    (by simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some])
    (by table_decide) (by decide +kernel) (by seg_free_pc)

/-- **The start barrier**, then the first statistics poll of the first item, or the tail's
poll. -/
theorem step_bar0 (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hs : d.site = .bar0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨rfl, rfl⟩ := hi.start (.inr rfl)
  have hw8 := hi.warp
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_2)
  obtain ⟨rfl, rfl⟩ := fires_barSync_imm (by decide) (by decide) (by decide) (by decide)
    (by rw [hpre.block]; decide) hf
  have h0 : At (PTX.next t) 1208 (factsAt L g 1207 ⟨.bar0, 0, 0, s, m, l⟩) := At.next h
  have hA := Seg.comp (bar0_a hpre hw8 _ rfl s m l) (bar0_b hpre hg hw8 _ rfl s m l)
  have hB := Seg.bra (K := kernel) (A := asms) (L := L) (g := g)
    (pick := decide ¬ 0 < items L g)
    (F := factsX L g 1233 (dB s m l) [(145, .pred (decide ¬ 0 < items L g)),
      (403, Prologue.sb L (8 * stOf L g))]) Flow.code_1233
    (List.mem_map.mpr ⟨145, by table_decide, by simp [valueX]⟩)
    (fun _ _ => asms_localRule_none)
  by_cases hT : 0 < items L g
  · rw [ite_eq_right_of_eq_false _ _ (by simp [hT])] at hB
    have hm1 := seg_mapa (pc := 1235) (dd := 405) (r := 1004) (off := 144 + 8 * stOf L g)
      (F := factsX L g 1235 (dB s m l) [(403, Prologue.sb L (8 * stOf L g)),
        (1004, Prologue.sb L (144 + 8 * stOf L g))]) hpre hg (by simp only [stOf]; omega)
      Flow.code_1235
      (List.mem_map.mpr ⟨1004, by table_decide, by
        simp only [valueX, List.lookup_cons, Nat.reduceBEq, Option.getD_some]⟩)
      (List.mem_map.mpr ⟨342, by table_decide, by
        simp only [valueX, valueOf, ctrlValues, floatValues, Prologue.valueOf, Prologue.values,
          PTX.Flow.lookupLit, Option.getD_some, Option.getD_none, List.lookup_cons,
          List.lookup_nil, Nat.reduceBEq]⟩)
      (not_mem_factsFrom (by table_decide))
    have hm2 := seg_mapa (pc := 1237) (dd := 406) (r := 1005) (off := 160 + 8 * stOf L g)
      (F := factsX L g 1237 (dB s m l) [(1005, Prologue.sb L (160 + 8 * stOf L g))]) hpre hg
      (by simp only [stOf]; omega) Flow.code_1237
      (List.mem_map.mpr ⟨1005, by table_decide, by
        simp only [valueX, List.lookup_cons, Nat.reduceBEq, Option.getD_some]⟩)
      (List.mem_map.mpr ⟨342, by table_decide, by
        simp only [valueX, valueOf, ctrlValues, floatValues, Prologue.valueOf, Prologue.values,
          PTX.Flow.lookupLit, Option.getD_some, Option.getD_none, List.lookup_cons,
          List.lookup_nil, Nat.reduceBEq]⟩)
      (not_mem_factsFrom (by table_decide))
    obtain ⟨t', hr, ht'⟩ := Seg.comp hA (Seg.comp hB (Seg.comp (bar0_c hpre hw8 s m l)
      (Seg.comp hm1 (Seg.comp (bar0_e hpre hw8 s m l) (Seg.comp hm2
        (Seg.comp (bar0_f hpre s m l) (Seg.comp (bar0_p hpre s m l)
          (Seg.comp (bar0_g hpre hw8 _ rfl s m l) (bar0_h hpre hw8 _ rfl s m l))))))))) _ h0
    exact step_of_run (d' := dB s m l) (by simp [next, hT])
      ⟨hw8, fun _ => hT, fun h => by simp at h, fun h => by simp at h, fun _ => rfl,
        fun h => by simp [Site.inTrip] at h, fun h => by simp at h, hi.lBytes⟩ rfl rfl
        ⟨_, t', hr, ht'⟩
  · rw [ite_eq_left_of_eq_true _ _ (by simp [hT])] at hB
    obtain ⟨t', hr, ht'⟩ := Seg.comp hA (Seg.comp hB (bar0_t hpre hw8 _ rfl s m l)) _ h0
    exact step_of_run (d' := ⟨.statsW 3, 0, 0, s, m, l⟩) (by simp [next, hT])
      ⟨hw8, fun h => by simp [Site.inItem] at h, fun _ => ⟨by simp only; omega, rfl⟩,
        fun h => by simp at h, fun h => by simp [Site.tile0] at h,
        fun h => by simp [Site.inTrip] at h, fun h => by simp at h, hi.lBytes⟩ rfl rfl
        ⟨_, t', hr, ht'⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
