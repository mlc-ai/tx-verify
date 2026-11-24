-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Startup.Machine
public import Lemmas.Flow.Step.SiteCases
public import Lemmas.Flow.Step.Alloc
public import Lemmas.Flow.SegPieces

@[expose] public section

/-! # The startup's obligations

Every state of the startup machine other than its exits satisfies its step obligation: the
barriers, the base word's load and the relinquish by `site_cases`, the allocation's two sub-steps by
the library's `step_alloc`, `step_allocWr`, and the second barrier and the shuffle by hand (a guard
or a branch on a value the evaluation needs as a literal). -/

namespace PTX.Kernels.InklingRelDecode.Proof2.Startup
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A computed value equals the table's. -/
macro "st_close" : tactic => `(tactic| (
  try simp only [valueOf, values, Startup.table, PTX.Flow.lookupLit, Option.getD_some,
    Option.getD_none]
  all_goals first
    | rfl
    | (simp only [b32]; done)
    | fail "st_close"))

/-- A closed fact about the registers a site names. -/
macro "live_dec" : tactic =>
  `(tactic| (simp only [Site.live, Site.pc, reduceCtorEq, ↓reduceIte]; decide))

macro "st_seg" : tactic => `(tactic| (intro t h; seg_fp h using st_close))

/-- The table's thread facts. -/
theorem p3_val (d : D) : valueOf Q L g d 3 = .pred (decide (g % L.block < 32)) := rfl

theorem stepAt_alloc (d : D) (hs : d.site = .alloc) : (code Q L g).StepAt d := by
  obtain ⟨s, tm, x, bw⟩ := d
  subst hs
  refine Code.StepAt.of (fun hi => ⟨_, Flow.code_11, rfl, ?_⟩) ?_
  · exact Code.guardTrue_factsFrom (by live_dec)
      (by simp [valueOf, values, Startup.table,
      PTX.Flow.lookupLit, hi (.inl rfl)])
  · refine Code.step_alloc (dw := ⟨.allocWr, tm, x, bw⟩) (dn := ⟨.bar0, tm, x, bw⟩) Flow.code_11
      rfl rfl
      (fun h _ => by simp [code, succ, h]) (fun h _ => by simp [code, succ, h]) rfl rfl rfl rfl
      (fun hi h => hi (.inl rfl)) ⟨fun _ => ⟨0, ?_⟩, rfl, rfl, fun _ h => by simp at h⟩
    exact (Seg.refl _ _).weaken_end fun _ h =>
      holds_factsFrom_mono h (by live_dec)

theorem stepAt_allocWr (d : D) (hs : d.site = .allocWr) : (code Q L g).StepAt d := by
  obtain ⟨s, tm, x, bw⟩ := d
  subst hs
  refine Code.StepAt.of (fun hi => ⟨_, Flow.code_11, rfl, ?_⟩) ?_
  · exact Code.guardTrue_factsFrom (by live_dec)
      (by simp [valueOf, values, Startup.table,
      PTX.Flow.lookupLit, hi (.inr (.inl rfl))])
  · refine Code.step_allocWr (dn := ⟨.bar0, tm, x, bw⟩) Flow.code_11 rfl rfl
      (fun _ => by simp [code, succ]) ⟨fun _ => ⟨0, ?_⟩, rfl, rfl, fun _ h => by simp at h⟩
    exact (Seg.refl _ _).weaken_end fun _ h =>
      holds_factsFrom_mono h (by live_dec)

theorem stepAt_bar0 (d : D) (hs : d.site = .bar0) : (code Q L g).StepAt d := by
  obtain ⟨s, tm, x, bw⟩ := d
  subst hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_12, rfl, trivial⟩) ?_
  exact Code.step_issue Flow.code_12 (by intro _ _ _; advances)
    (dn := ⟨.ld0, tm, x, bw⟩) (fun _ => by simp [code, succ]) rfl rfl
    ⟨fun _ => ⟨0, (Seg.refl _ _).weaken_end fun _ h => holds_factsFrom_mono h
      (by live_dec)⟩, rfl, rfl, fun _ h => by simp at h⟩

/-- A register named at pc 14 other than the base word's is named at pc 13. -/
theorem live14_13 (r : Nat) (hr : r ∈ Flow.live 14) (hr4 : r ≠ 463) : r ∈ Flow.live 13 := by
  have : ∀ r ∈ Flow.live 14, r = 463 ∨ r ∈ Flow.live 13 := by decide
  exact (this r hr).resolve_left hr4

theorem stepAt_ld0 (d : D) (hs : d.site = .ld0) : (code Q L g).StepAt d := by
  obtain ⟨s, tm, x, bw⟩ := d
  subst hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_13, rfl, trivial⟩) ?_
  refine Code.step_load_sel (r := 463)
    (nv := fun v => some (some ⟨.bar1, (Proof.ProA.word32 v).getD 0, x, v⟩)) Flow.code_13
    rfl rfl rfl rfl
    (fun _ bs v hv => by simp only [code, succ, hv]; cases Proof.ProA.word32 v <;> rfl)
    (fun _ bs f hv => .inl (by simp [code, succ, hv]))
    rfl rfl (fun v => by simp) ?_
  have hk : ∀ r ∈ Flow.live 13,
      r ∈ [3, 462, 528, 529, 530, 531, 532, 534, 1949, 2020] := by decide
  intro v d' hv
  simp only [Option.some.injEq] at hv
  subst hv
  refine ⟨fun _ => ⟨0, (Seg.refl _ _).weaken_end fun R h => ?_⟩, rfl, rfl,
    fun _ h => by simp at h⟩
  apply holds_of_pointwise
  intro r hr
  change r ∈ Flow.live 14 at hr
  by_cases hr4 : r = 463
  · subst hr4
    exact holds_mem h (List.mem_cons_self ..)
  · have hl := live14_13 r hr hr4
    refine holds_mem h (List.mem_cons_of_mem _ ?_)
    refine List.mem_filter.mpr ⟨?_, by simpa using hr4⟩
    have hv : valueOf Q L g ⟨.bar1, (Proof.ProA.word32 v).getD 0, x, v⟩ r =
        valueOf Q L g ⟨.ld0, tm, x, bw⟩ r := by
      have := hk r hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hv]
    exact Flow.mem_factsFrom hl

/-- The facts at a program counter, with the words of a state. -/
abbrev F (Q : Params) (L : Launch) (g : Nat) (pc : Nat) (d : D) : List (Nat × Value) :=
  Flow.factsFrom (Flow.live pc) (valueOf Q L g d)

/-- `shr.u32 %r3, %r1, 5` (pc 16): the warp index. -/
theorem seg_shr (hb : g % L.block < 256) (d : D) :
    Seg kernel Assumptions.all L g 1 16 (F Q L g 16 d) 17 (F Q L g 17 d) := by
  intro t h
  seg_fp h using
    try simp only [valueOf, values, Startup.table, PTX.Flow.lookupLit, Option.getD_some]
    all_goals simp only [Startup.warpOf]
    all_goals nf_simp [PTX.compare, decide_eq_decide, ne_eq, decide_eq_false_iff_not,
      decide_eq_true_eq]
    all_goals omega

/-- The facts at pc 16 from those at 14 or 15. -/
theorem F_16 (pc : Nat) (hpc : pc = 14 ∨ pc = 15) (d : D) :
    ∀ R, Holds R (F Q L g pc d) → Holds R (F Q L g 16 d) := by
  intro R h
  refine holds_factsFrom_mono h ?_
  rcases hpc with rfl | rfl <;> decide

theorem stepAt_bar1 (hb : g % L.block < 256) (d : D) (hs : d.site = .bar1) :
    (code Q L g).StepAt d := by
  obtain ⟨s, tm, x, bw⟩ := d
  subst hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_14, rfl, trivial⟩) ?_
  by_cases hl : g % L.block < 32
  · refine Code.step_issue Flow.code_14 (by intro _ _ _; advances)
      (dn := ⟨.relinq, tm, x, bw⟩) (fun _ => by simp [code, succ, hl]) rfl rfl
      ⟨fun _ => ⟨0, (Seg.refl _ _).weaken_end fun _ h => holds_factsFrom_mono h
        (by live_dec)⟩, rfl, rfl, fun _ _ => hl⟩
  · refine Code.step_issue Flow.code_14 (by intro _ _ _; advances)
      (dn := ⟨.shfl, tm, x, bw⟩) (fun _ => by simp [code, succ, hl]) rfl rfl
      ⟨fun _ => ⟨2, ?_⟩, rfl, rfl, fun _ h => by simp at h⟩
    have hp3 : (3, Value.pred false) ∈ F Q L g 14 ⟨.bar1, tm, x, bw⟩ := by
      have h := Flow.mem_factsFrom (val := valueOf Q L g ⟨.bar1, tm, x, bw⟩)
        (show 3 ∈ Flow.live 14 by decide)
      simpa [valueOf, values, Startup.table, PTX.Flow.lookupLit, hl] using h
    exact (Seg.guardSkip Flow.code_15 hp3 rfl).comp
      ((seg_shr hb _).weaken_start (F_16 14 (.inl rfl) _))

theorem stepAt_relinq (hb : g % L.block < 256) (d : D) (hs : d.site = .relinq) :
    (code Q L g).StepAt d := by
  obtain ⟨s, tm, x, bw⟩ := d
  subst hs
  refine Code.StepAt.of (fun hi => ⟨_, Flow.code_15, rfl, ?_⟩) ?_
  · exact Code.guardTrue_factsFrom (by live_dec)
      (by simp [valueOf, values, Startup.table,
      PTX.Flow.lookupLit, hi (.inr (.inr rfl))])
  · exact Code.step_issue Flow.code_15 (fun hf => fires_tcRelinquish_next hf)
      (dn := ⟨.shfl, tm, x, bw⟩) (fun _ => by simp [code, succ]) rfl rfl
      ⟨fun _ => ⟨1, (seg_shr hb _).weaken_start (F_16 15 (.inr rfl) _)⟩, rfl, rfl,
        fun _ h => by simp at h⟩

/-! ### The shuffle and the branch on the received word -/

/-- The prologue's first data for the startup's base word. -/
abbrev dt0 (Q : Params) (L : Launch) (g : Nat) (tm : Nat) (w : Value) : Proof.ProA.Dat :=
  Proof.ProA.Dat.start (Startup.inh L g Q tm) w

theorem live17_20 : ∀ r ∈ Flow.live 20,
    r ∈ [3, 462, 463, 464, 528, 529, 530, 531, 532, 1949, 2020] := by decide

theorem sub20 : ∀ r ∈ Flow.live 20, r ∈ Flow.live 17 := by decide

/-- The startup's table agrees with the prologue's first data on the registers live at pc 20. -/
theorem bridge20 (d : D) : ∀ r ∈ Flow.live 20,
    valueOf Q L g d r = Proof.ProA.valueOf L g (dt0 Q L g d.tm d.w) r := by
  intro r hr
  have hk := live17_20 r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- ... and on the registers live at pc 27. -/
theorem bridge27 (d : D) : ∀ r ∈ Flow.live 27,
    valueOf Q L g d r = Proof.ProA.valueOf L g (dt0 Q L g d.tm d.w) r := by
  intro r hr
  rw [Startup.live27] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `setp.lt.u32 %p4, %r4, 4` (pc 18) on the received word. -/
theorem seg_p4 (d : D) (x : BitVec 64) :
    Seg kernel Assumptions.all L g 1 18 ((465, .bits 32 x) :: F Q L g 17 d) 19
      ((4, .pred (Arith32.scmpi .lt .u x 4)) :: (465, .bits 32 x) :: F Q L g 17 d) := by
  intro t h
  seg_fp h using rfl

/-- The seven parameter loads of pc 20 to 26, to the prologue's first facts. -/
theorem seg_params (hp : Pre Q L m) (tm : Nat) (w : Value) :
    Seg kernel Assumptions.all L g 7 20 (Proof.ProA.factsAt L g 20 (dt0 Q L g tm w)) 27
      (Proof.ProA.factsAt L g 27 (dt0 Q L g tm w)) := by
  have h15 : L.params (param "15") = some (dt0 Q L g tm w).pro.x15 := by
    obtain ⟨bits, -, hb, -⟩ := hp.paramScale
    simp [dt0, Proof.ProA.Dat.start, Startup.inh, hb]
  exact (Proof.ProA.seg_20_21 L g _ hp.paramStrideRel).comp
    ((Proof.ProA.seg_21_22 L g _ hp.paramStrideQ).comp ((Proof.ProA.seg_22_23 L g _ h15).comp
    ((Proof.ProA.seg_23_24 L g _ hp.paramCu).comp ((Proof.ProA.seg_24_25 L g _ hp.paramSeq).comp
    ((Proof.ProA.seg_25_26 L g _ hp.paramRel).comp (Proof.ProA.seg_26_27 L g _ hp.paramQ))))))

theorem stepAt_shfl (hp : Pre Q L m) (d : D) (hs : d.site = .shfl) : (code Q L g).StepAt d := by
  obtain ⟨s, tm, x0, bw⟩ := d
  subst hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_17, rfl, trivial⟩) ?_
  refine Code.step_shfl_sel (r := 465)
    (nv := fun v => succ L g ⟨.shfl, tm, x0, bw⟩ ⟨17, .shfl .idx (b32 0) 0 31 v true⟩)
    Flow.code_17 ?_ (fun _ _ _ _ _ _ => rfl) rfl rfl ?_ ?_
  · intro q hq he
    simp only [facts, Flow.factsFrom, List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    subst he
    exact absurd hr (by live_dec)
  · intro v
    simp only [succ]
    split <;> simp
  · intro v d' hv
    simp only [succ] at hv
    split at hv
    · rename_i x
      simp only [Option.some.injEq] at hv
      subst hv
      refine ⟨fun _ => ?_, rfl, rfl, fun _ h => by simp at h⟩
      have h18 := seg_p4 (Q := Q) (L := L) (g := g) ⟨.shfl, tm, x0, bw⟩ x
      cases hc : Arith32.scmpi .lt .u x 4 <;> rw [hc] at h18
      · -- the workers' path: pc 2331, 2332 to the dispatch loop's head
        have hb := Seg.braNot (K := kernel) (A := Assumptions.all) (L := L) (g := g)
          (pick := false)
          (F := (4, .pred false) :: (465, .bits 32 x) :: F Q L g 17 ⟨.shfl, tm, x0, bw⟩)
          Flow.code_19
          (List.mem_cons_self ..)
          (fun _ _ => Proof.ProA.asms_localRule_bra) (Startup.asms_segFreePc (by decide))
        have hw : Seg kernel Assumptions.all L g 2 2331
            ((4, .pred false) :: (465, .bits 32 x) :: F Q L g 17 ⟨.shfl, tm, x0, bw⟩) 2337
            (F Q L g 2337 ⟨.enter .worker, tm, x, bw⟩) := by
          intro t h
          seg_fp h using st_close
        simp only [Bool.false_eq_true, ↓reduceIte] at hb
        simp only [entryOf, hc, Bool.false_eq_true, ↓reduceIte, facts, Site.pc, Entry.pc]
        exact ⟨_, (h18.comp hb).comp hw⟩
      · have hb := Seg.braNot (K := kernel) (A := Assumptions.all) (L := L) (g := g)
          (pick := true)
          (F := (4, .pred true) :: (465, .bits 32 x) :: F Q L g 17 ⟨.shfl, tm, x0, bw⟩)
          Flow.code_19
          (List.mem_cons_self ..)
          (fun _ _ => Proof.ProA.asms_localRule_bra) (Startup.asms_segFreePc (by decide))
        simp only [↓reduceIte] at hb
        simp only [entryOf, hc, ↓reduceIte, facts, Site.pc, Entry.pc]
        refine ⟨_, ((h18.comp hb).comp ((seg_params hp tm bw).weaken_start ?_)).weaken_end ?_⟩
        · intro R h
          apply holds_of_pointwise
          intro r hr
          rw [← bridge20 (Q := Q) (L := L) (g := g) ⟨.shfl, tm, x0, bw⟩ r hr]
          exact holds_mem h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (Flow.mem_factsFrom (sub20 r hr))))
        · intro R h
          apply holds_of_pointwise
          intro r hr
          rw [bridge27 (Q := Q) (L := L) (g := g) ⟨.enter .dp, tm, x, bw⟩ r hr]
          exact holds_mem h (Flow.mem_factsFrom hr)
    · cases hv

end
end PTX.Kernels.InklingRelDecode.Proof2.Startup
