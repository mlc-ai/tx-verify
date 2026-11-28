-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictLib
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.SegLib
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StepKinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataSites1
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.SegFrameSet
public import Lemmas.Flow.VoteAnyS
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part008
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part009
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Loop.StepsSetup

@[expose] public section

/-! # The strict step of the rescale vote (pc 578)

The vote's result `r` is the event's; the window after it (`voteWinS`) runs under the conditions of
the factor's run (a clear vote) and of the P run, taken at the result. The control facts of the
site after the vote are the site's, with the vote's register (`%p1`) the result. -/

/-! # The strict window after the rescale vote (pcs 579 to 704)

Over the data facts alone: the moved factor and the negated vote (pcs 579-580, an exact control
piece), the branch at pc 581, the factor's run on the arm of a clear vote (`Gen.vt_run`), and the
P run to the first P store (`Gen.pw_run`). The control facts are framed over it by the caller. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
set_option maxRecDepth 100000

/-- The control code after the vote (pcs 579-580), as an exact segment. -/
theorem segS_vote (L : Launch) (g : Nat) (vt : Bool) (V : Nat → Value) :
    ∃ n, Seg kernel Assumptions.all L g n 579 ((1, .pred vt) :: factsFrom
      [109, 479, 1112, 2885, 3300, 3304, 3292, 3296, 3284, 3288,
      3276, 3280, 3268, 3272, 3260, 3264, 3252, 3256, 3242, 3247,
      467, 3243, 2950, 2955, 2880]
      V) 581
      ((110, .pred (!vt)) :: (2951, .bits 32 (BitVec.ofNat 64 1065353216)) ::
        factsFrom
      [109, 479, 1112, 2885, 3300, 3304, 3292, 3296, 3284, 3288,
      3276, 3280, 3268, 3272, 3260, 3264, 3252, 3256, 3242, 3247,
      467, 3243, 2950, 2955, 2880]
        V) := by
  seg_sym using w0_segS

/-- The P run (pc 586 to the first P store), exact under its condition. -/
theorem joinS (L : Launch) (g : Nat) (x : BitVec 64) (m l mx sk : Value) (lo hi : List Value)
    (mw : Value) (p0 p1 p2 p3 p4 p5 p6 p7 : Value × Value) (pm : Value) (vt : Bool)
    (c : Gen.pw_cond (lookupD (f_join x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt))) :
    ∃ n, Seg kernel Assumptions.all L g n 586
      (f_join x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt) 704
      (f_ost x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt) :=
  ⟨_, ((SegD.frame (H := factsFrom
      [2950, 2951, 2885, 467, 3243, 2880]
      (lookupD (f_join x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt))) rulesFrame
      (Gen.pw_run L g (lookupD (f_join x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm vt)))
      rfl (by kernel_rfl) (by kernel_rfl)
      fun _ _ => w0SegFree _).seg c).weaken_start
    (fun _ h => (holds_append _ _ _).mpr ⟨holds_lookupD (live :=
      [2950, 2951, 2955, 3242, 3243, 3247, 3252, 3256, 3260, 3264,
      3268, 3272, 3276, 3280, 3284, 3288, 3292, 3296, 3300, 3304])
      h (by kernel_rfl),
      holds_lookupD (live :=
      [2950, 2951, 2885, 467, 3243, 2880])
      h (by kernel_rfl)⟩)⟩

/-- The window after the vote's result `r`, from the facts of the site and the result to the
first P store, under the conditions of the two runs; it keeps the negated vote (`%p110`). -/
theorem voteWinS (L : Launch) (g : Nat) (x : BitVec 64) (m l mx sk : Value) (lo hi : List Value)
    (mw : Value) (p0 p1 p2 p3 p4 p5 p6 p7 : Value × Value) (pm : Value) (r : Bool)
    (c1 : r = true → Gen.vt_cond (lookupD (f_vh x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm)))
    (c2 : Gen.pw_cond (lookupD (f_join x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm r))) :
    ∃ n, Seg kernel Assumptions.all L g n 579
      ((1, .pred r) :: f_vote x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm) 704
      (f_ost x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm r ++ [(110, .pred (!r))]) := by
  obtain ⟨n1, h1⟩ := segS_vote L g r (lookupD (f_vote x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6
    p7 pm))
  obtain ⟨n3, h3⟩ := joinS L g x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm r c2
  have h0 := h1.weaken_start (F' := (1, .pred r) ::
      f_vote x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm) fun _ h =>
      (⟨h.1, holds_lookupD (live :=
      [109, 479, 1112, 2885, 3300, 3304, 3292, 3296, 3284, 3288,
      3276, 3280, 3268, 3272, 3260, 3264, 3252, 3256, 3242, 3247,
      467, 3243, 2950, 2955, 2880]) h.2 (by kernel_rfl)⟩)
  have hs : ∀ R, Holds R ((110, .pred (!r)) :: f_vh x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7
      pm) → Holds R (f_vh x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm ++ [(110, .pred (!r))]) :=
    fun _ h => (holds_append _ _ _).mpr ⟨h.2, ⟨h.1, trivial⟩⟩
  cases r
  · have h4 := Seg.frameSet (H := [(110, Value.pred (!false))]) rulesFrame
      (S := List.range' 586 118)
      (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl)
      (h3.weaken_start (F' := f_vh x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm) fun _ h =>
      (holds_append _ _ _).mpr ⟨holds_lookupD (live := [2950, 2951]) h (by kernel_rfl),
      holds_lookupD (live :=
      [2885, 3300, 3304, 3292, 3296, 3284, 3288, 3276, 3280, 3268,
      3272, 3260, 3264, 3252, 3256, 3242, 3247, 467, 3243, 2955,
      2880]) h (by kernel_rfl)⟩)
    exact ⟨n1 + (1 + _), h0.comp ((Seg.bra (target := 586) (p := 110) (pick := true)
      Flow.code_581 (by simp) (fun t _ a ha => bra_rule t a ha) (w0SegFree 581)).comp
      (h4.weaken_start hs))⟩
  · have hv := c1 rfl
    obtain ⟨n2, h2⟩ : ∃ n, Seg kernel Assumptions.all L g n 582
        (f_vh x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm) 586
        (f_join x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm true) :=
      ⟨_, ((SegD.frame (H := factsFrom
      [2885, 3300, 3304, 3292, 3296, 3284, 3288, 3276, 3280, 3268,
      3272, 3260, 3264, 3252, 3256, 3242, 3247, 467, 3243, 2955,
      2880]
      (lookupD (f_vh x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm))) rulesFrame
      (Gen.vt_run L g (lookupD (f_vh x m l mx sk lo hi mw p0 p1 p2 p3 p4 p5 p6 p7 pm)))
      rfl (by kernel_rfl) (by kernel_rfl)
      fun _ _ => w0SegFree _).seg hv).weaken_start fun _ h =>
        (holds_append _ _ _).mpr ⟨holds_lookupD (live := [479, 2950]) h (by kernel_rfl),
        holds_lookupD (live :=
      [2885, 3300, 3304, 3292, 3296, 3284, 3288, 3276, 3280, 3268,
      3272, 3260, 3264, 3252, 3256, 3242, 3247, 467, 3243, 2955,
      2880]) h (by kernel_rfl)⟩⟩
    have h4 := Seg.frameSet (H := [(110, Value.pred (!true))]) rulesFrame
      (S := List.range' 582 122)
      (by kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl) (h2.comp h3)
    exact ⟨n1 + (1 + _), h0.comp ((Seg.bra (target := 586) (p := 110) (pick := false)
      Flow.code_581 (by simp) (fun t _ a ha => bra_rule t a ha) (w0SegFree 581)).comp
      (h4.weaken_start hs))⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The conditions of the window after a vote whose result is `r`. -/
def voteCond (x : BitVec 64) (b : Blk) (r : Bool) : Prop :=
  (r = true → Gen.vt_cond (lookupD (f_vh x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1)
    (b.pw 2) (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm))) ∧
  Gen.pw_cond (lookupD (f_join x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1)
    (b.pw 2) (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm r))

/-- The value table of the state after the vote differs from the state's in the vote's registers
only. -/
theorem valueOf_vote (d : Control.D) (r : Bool) {q : Nat} (h1 : q ≠ 1) (h2 : q ≠ 110) :
    Control.valueOf P L g w { d with site := .ost 0, el := 0, vt := r } q =
      Control.valueOf P L g w d q := by
  simp only [Control.valueOf, Control.values, Control.valuesLen, List.cons_append,
    List.nil_append, List.lookup]
  simp only [beq_false_of_ne h1, beq_false_of_ne h2]
  rfl

/-- The control facts of the site after the vote, but for the negated vote, are held by those of
the vote's site. -/
theorem facts_vote (d : Control.D) (hs : d.site = .vote) (r : Bool) :
    ∀ R, Holds R (Control.facts P L g w d) →
      Holds R (factsFrom ((Control.ctlLive (Site.ost 0).pc).erase 110)
        (Control.valueOf P L g w { d with site := .ost 0, el := 0, vt := r })) := by
  intro R h
  refine holds_of_pointwise fun q hq => ?_
  have hq1 : q ≠ 1 := by
    have : ∀ q ∈ (Control.ctlLive (Site.ost 0).pc).erase 110, q ≠ 1 := by decide +kernel
    exact this q hq
  have hq110 : q ≠ 110 := by
    have : ∀ q ∈ (Control.ctlLive (Site.ost 0).pc).erase 110, q ≠ 110 := by decide +kernel
    exact this q hq
  have hl : ∀ q ∈ (Control.ctlLive (Site.ost 0).pc).erase 110,
      q ∈ Control.ctlLive Site.vote.pc := by decide +kernel
  have hq' : q ∈ Control.ctlLive d.site.pc := by rw [hs]; exact hl q hq
  rw [valueOf_vote (P := P) (L := L) (g := g) (w := w) d r hq1 hq110]
  exact holds_mem h (mem_factsFrom hq')

/-- The window after the vote, from the facts of the site and the result to those of the first
P store. -/
theorem voteWin (d : Control.D) (hs : d.site = .vote) (b : Blk) (r : Bool)
    (hc : voteCond (scX L) b r) :
    ∃ n, Seg kernel Assumptions.all L g n 579
      ((1, .pred r) :: (Control.facts P L g w d ++ wF (scX L) .vote b)) 704
      (Control.facts P L g w { d with site := .ost 0, el := 0, vt := r } ++
        wF (scX L) (.ost 0) { b with vt := r }) := by
  obtain ⟨n, h⟩ := voteWinS L g (scX L) b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1)
    (b.pw 2) (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm r hc.1 hc.2
  have h3 := Seg.frameSet (H := factsFrom ((Control.ctlLive (Site.ost 0).pc).erase 110)
    (Control.valueOf P L g w { d with site := .ost 0, el := 0, vt := r }))
    rulesFrame (S := List.range' 579 125)
    (by rw [factsFrom_keys]; kernel_rfl) (fun _ _ => w0SegFree _) (by kernel_rfl) h
  refine ⟨n, (h3.weaken_start fun R hR => ?_).weaken_end fun R hR => ?_⟩
  · have h2 := (holds_append _ _ _).mp hR.2
    exact (holds_append _ _ _).mpr ⟨⟨hR.1, h2.2⟩, facts_vote d hs r R h2.1⟩
  · rw [holds_append, holds_append] at hR
    obtain ⟨⟨hw, h110⟩, hc'⟩ := hR
    have h4 := facts_of_erase (P := P) (L := L) (g := g) (w := w)
      (c := { d with site := .ost 0, el := 0, vt := r }) (r := 110) (R := R)
      (by show 110 ∈ Control.ctlLive (Site.ost 0).pc; decide +kernel) (by exact h110.1) hc'
    exact (holds_append _ _ _).mpr ⟨h4, hw⟩

/-- **The strict step at pc 578** (the rescale vote), for an event whose result satisfies the
window's conditions. -/
theorem sk_578 (d : D) (hs : d.c.site = .vote) (hok : d.ok = true) (e : Event)
    (hcd : ∀ m p r, e.kind = .voteMode .any m p r → voteCond (scX L) d.b r) :
    (code P L g w).StepFor d e := by
  classical
  let c' : Bool → Control.D := fun r => { d.c with site := .ost 0, el := 0, vt := r }
  let Ok : Event → Prop := fun e => ∀ m p r, e.kind = .voteMode .any m p r → voteCond (scX L) d.b r
  suffices h : ((code P L g w).cut Ok).StepFor d e from
    @StepFor.of_cut _ _ _ _ (code P L g w) Ok d e h hcd
  intro t u ins hat hi hc' hf
  have hpc : d.c.site.pc = 578 := by rw [hs]; rfl
  have hn : ∀ m p r, ((code P L g w).cut Ok).next d ⟨d.c.site.pc, .voteMode .any m p r⟩ =
      if voteCond (scX L) d.b r then some (some ⟨c' r, { d.b with vt := r }, d.hist, true⟩)
      else some none := by
    intro m p r
    by_cases hcr : voteCond (scX L) d.b r
    · have hO : Ok ⟨d.c.site.pc, .voteMode .any m p r⟩ := by
        intro m' p' r' hk'
        obtain ⟨-, -, rfl⟩ : m = m' ∧ p = p' ∧ r = r' := by simpa using hk'
        exact hcr
      rw [cut_next _ _ hO]
      simp only [hcr, ↓reduceIte]
      show (Control.succ P L g w d.c _).map _ = _
      have hsu : Control.succ P L g w d.c ⟨d.c.site.pc, .voteMode .any m p r⟩ =
          some (some (c' r)) := by simp [Control.succ, hs, c']
      rw [hsu]
      show some (some (dataNext L d (c' r) _)) = _
      rw [next_on (b' := { d.b with vt := r }) (by rw [hs]; decide) hok (by simp [succOk, hs, c'])
        (by simp [record, hs])]
    · have hO : ¬ Ok ⟨d.c.site.pc, .voteMode .any m p r⟩ := fun h => hcr (h m p r rfl)
      rw [cut_next_not _ _ hO]
      simp only [hcr, ↓reduceIte]
  refine (Code.step_voteAnyS (C := (code P L g w).cut Ok) (dv := 1)
    (nv := fun r => if voteCond (scX L) d.b r then
      some (some ⟨c' r, { d.b with vt := r }, d.hist, true⟩) else some none)
    (by show kernel.code[d.c.site.pc]? = _; rw [hpc]; exact Flow.code_578) ?_ hn
    (fun r => by by_cases h : voteCond (scX L) d.b r <;> simp [h])
    (by show d.c.el = 0; exact el0_of_one (by rw [hs]; rfl) hi) (by
      show Control.D.acc d.c = []
      simp [Control.D.acc, el0_of_one (by rw [hs]; rfl) hi]) ?_).step ins hat hi hc' hf
  · intro hm
    have hm' : 1 ∈ (Control.facts P L g w d.c ++ wF (scX L) d.c.site d.b).map Prod.fst := by
      rw [facts_ok hok] at hm
      exact hm
    rw [List.map_append, List.mem_append, facts_keys hpc] at hm'
    rcases hm' with h | h
    · exact absurd h (by decide +kernel)
    · obtain ⟨q, hq, hq1⟩ := List.mem_map.mp h
      rw [hs] at hq
      exact hoff_of (F := wF (scX L) .vote d.b) (ds := [1]) (by kernel_rfl) q hq (by simp [hq1])
  · intro r d' hd
    by_cases hcr : voteCond (scX L) d.b r
    · simp only [hcr, ↓reduceIte] at hd
      obtain rfl := Option.some.inj (Option.some.inj hd)
      have he0 : d.c.el = 0 := el0_of_one (by rw [hs]; rfl) hi
      refine ⟨fun _ => ?_, rfl, by simp [Control.D.acc, c'], fun _ => Control.elems_pos _⟩
      obtain ⟨n, h⟩ := voteWin (P := P) (L := L) (g := g) (w := w) d.c hs d.b r hcr
      refine ⟨n, ?_⟩
      show Seg _ _ _ _ _ (d.c.site.pc + 1) _ (c' r).site.pc _
      have hw : wF (scX L) d.c.site d.b = wF (scX L) .vote d.b := by rw [hs]
      rw [hpc, facts_ok hok, facts_next, hw]
      exact h
    · simp only [hcr, ↓reduceIte] at hd; cases hd

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
