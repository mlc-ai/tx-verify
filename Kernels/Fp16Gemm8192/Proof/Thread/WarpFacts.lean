-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.WarpPro
public import Kernels.Fp16Gemm8192.Proof.Thread.ElectOnce
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderUnelected
public import Kernels.Fp16Gemm8192.Proof.Thread.SchedulerTime
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLead
public import Kernels.Fp16Gemm8192.Proof.Thread.RegStep

@[expose] public section

/-! # The collective sites along a thread's run

For a thread at a collective site at the end of its trace (`coll_none_fact`, `coll_before_fact`,
`coll_lane_fact`):

* it has made no event of an instance of the site: the prologue's sites are at fixed positions,
  and every election is event 1 (warp 0) or event 6 (`elect_pos`), which a thread at the role
  elections has not passed;
* its events before the site: none, the shuffle, warp 0's allocation (and lane 0's write of the
  column), or the register request;
* a lane of its warp has made an event of an instance of the site (it is past the site's
  position), or is at the site, or at a site of time at least 2 earlier, or stopped before the site
  without exiting. The lanes of a warp run the same prologue path, and the role warps' lanes without
  an election are before it (`loader_unelected_thm`, `mma_unelected_thm`, `sched_unelected_thm`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow Prologue

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ## Static facts of the sites -/

theorem Prologue.Site.vtime_le (s : Prologue.Site) : s.vtime ≤ 56 := by
  cases s <;> simp [Prologue.Site.vtime]
  omega

theorem Prologue.Site.vtime_le_of_ne (s : Prologue.Site) (h : s ≠ .roleElect) : s.vtime ≤ 54 := by
  cases s <;> simp_all [Prologue.Site.vtime]
  omega

theorem Prologue.index_pos {p : Prologue.D} (h : p.site ≠ .shfl) : 1 ≤ Prologue.index L g p := by
  obtain ⟨site, w⟩ := p
  cases site <;> simp_all [Prologue.index, Prologue.fenceIdx] <;> (try split_ifs) <;> omega

theorem Mma.vtime_ge {D : Nat} {m : Mma.D} (hx : Mma.exitOff m = none) (hs : m.site ≠ .elect) :
    64 ≤ Mma.vtime D m := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  cases site <;> simp_all [Mma.vtime, Mma.exitOff, ringAt, blockAt] <;> omega

/-! ## Events at the sites -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
include hpre hX

/-- Warp 0's event 1 is its full-mask election. -/
theorem elect_event (hg : g < L.threads) (hw : warpOf L g = 0) (h1 : 1 < (X.tr g).length) :
    ∃ inst leader, X.get (g, 1) = some ⟨Prologue.Site.elect.pc, .elect fullMask inst leader⟩ := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[1]? = some e := ⟨_, List.getElem?_eq_getElem h1⟩
  have hσ := stateAt_one hpre hX hg (by omega)
  simp only [hw, ↓reduceIte] at hσ
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  change kernel.code[Prologue.Site.elect.pc]? = some ins at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0)
  have hm : readBits L g t 32 (.reg 57) = .ok (BitVec.ofNat 64 4294967295) :=
    readBits_b32 (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom
      (show 57 ∈ Flow.live Prologue.Site.elect.pc by table_decide))) (by decide)
  obtain ⟨inst, leader, rfl⟩ := fires_elect_full hm (by decide) hf
  exact ⟨inst, leader, he⟩

/-- The state of a warp-0 thread at its warp barrier's index is the warp barrier. -/
theorem wb_state (hg : g < L.threads) (hw : warpOf L g = 0) {d : ThreadD}
    (hk : wbIdx L g ≤ (X.tr g).length) (hσ : Frame.stateAt (code L) X g (wbIdx L g) =
      some (some d)) :
    d = .inl ⟨.warpBar, 0⟩ := by
  rcases d with q | r
  · obtain ⟨h1, h2, hc⟩ := pro_end hpre hX hg hk hσ
    have hq0 : q.site ≠ .shfl → q.w = 0 := fun hs =>
      (h2 (by have := Prologue.index_pos (L := L) (g := g) hs; omega)).trans hw
    have hsite := (w0_site hq0 hc (by omega)).1 h1.symm
    obtain ⟨site, w⟩ := q
    simp only at hsite hq0
    subst hsite
    rw [hq0 (by simp)]
  · have := (onPath_all hpre hX hg _ hk).2 r hσ
    have h2 := wbIdx_lt_wait (L := L) (g := g)
    rw [hw] at this
    omega

/-- A warp-0 thread past its warp barrier's index has made its full-mask warp barrier there. -/
theorem warpBar_event (hg : g < L.threads) (hw : warpOf L g = 0)
    (hnu : ∀ k pc f, X.get (g, k) ≠ some ⟨pc, .ub f⟩) (hlt : wbIdx L g < (X.tr g).length) :
    ∃ inst, X.get (g, wbIdx L g) = some ⟨Prologue.Site.warpBar.pc, .warpBar fullMask inst⟩ := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[wbIdx L g]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨d, hτ⟩ := Frame.event_state (fun _ => sound hpre) hX (tracked hpre hX) he
    (fun pc f h => hnu _ pc f (h ▸ he))
  have hd := wb_state hpre hX hg hw hlt.le hτ
  subst hd
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hτ
  change kernel.code[Prologue.Site.warpBar.pc]? = some ins at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_0)
  obtain ⟨inst, rfl⟩ := fires_warpBar_full hf
  exact ⟨inst, he⟩

/-- A role state before the thread's event 5 is impossible for warps 8 to 11: event 5 follows the
register request's site. -/
theorem role_len (hg : g < L.threads) {r : Prologue.Role}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr r))) (hw0 : warpOf L g ≠ 0)
    (hq : warpOf L g / 4 = 2) : 6 ≤ (X.tr g).length := by
  have hwait := (onPath_all hpre hX hg _ le_rfl).2 r hσ
  simp only [Prologue.index, Prologue.fenceIdx, hw0, ↓reduceIte] at hwait
  by_contra hlt
  have h5 : (X.tr g).length = 5 := by omega
  have hs5 := mmaPath5 hpre hX hg hw0 hq (by omega)
  rw [← h5, hσ] at hs5
  cases hs5

/-- The event before a role election (event 5) is the register request. -/
theorem role_before (hg : g < L.threads) (hw0 : warpOf L g ≠ 0) (hq : warpOf L g / 4 = 2)
    (h5 : 5 < (X.tr g).length) :
    ∃ pc inc n inst, X.get (g, 5) = some ⟨pc, .setMaxReg inc n inst⟩ := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[5]? = some e := ⟨_, List.getElem?_eq_getElem h5⟩
  have hs5 := mmaPath5 hpre hX hg hw0 hq (by omega)
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hs5
  obtain ⟨inst, rfl⟩ := reg_fire (d := .inl ⟨.setMaxReg, warpOf L g⟩) rfl hc hf
  exact ⟨_, _, _, inst, he⟩

/-- An MMA thread at its election has made six events, on a leader CTA. -/
theorem mma_elect_len (hg : g < L.threads) {m : Mma.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m)))) (hs : m.site =
      .elect) :
    (X.tr g).length = 6 ∧ (warpOf L g = 8 ∨ warpOf L g = 9) ∧ g / L.block % 2 = 0 := by
  have hrw := role_warp hpre hX hg _ le_rfl _ hσ
  simp only [roleWarp] at hrw
  obtain ⟨-, hw89⟩ := hrw
  have hlead := mma_lead (Frame.stateAt_end ▸ hσ)
  simp only [Mma.Lead, hs, reduceCtorEq, false_or] at hlead
  refine ⟨?_, hw89, hlead⟩
  have h6 := role_len hpre hX hg hσ (by omega) (by omega)
  by_contra hne
  have hs6 := mmaPath6 hpre hX hg hw89 (by omega)
  obtain ⟨e6, he6⟩ : ∃ e, (X.tr g)[6]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hrun := mma_run (stateAt_seven hs6 he6) ((X.tr g).length - 7) (by omega)
  rw [show 7 + ((X.tr g).length - 7) = (X.tr g).length by omega, hσ] at hrun
  rcases hrun with h | ⟨m', h, hm'⟩
  · cases h
  · cases h
    exact hm' hs

/-- A scheduler at its election has made six events. -/
theorem sched_elect_len (hg : g < L.threads) {sd : Scheduler.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length =
      some (some (.inr (.sched sd)))) (hs : sd.site = .elect) :
    (X.tr g).length = 6 ∧ warpOf L g = 10 := by
  have hrw := role_warp hpre hX hg _ le_rfl _ hσ
  simp only [roleWarp] at hrw
  refine ⟨?_, hrw⟩
  have h6 := role_len hpre hX hg hσ (by omega) (by omega)
  by_contra hne
  have hs6 := schedPath6 hpre hX hg hrw (by omega)
  obtain ⟨e6, he6⟩ : ∃ e, (X.tr g)[6]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hbase : Frame.stateAt (code L) X g 7 = none ∨
      ∃ s7, Frame.stateAt (code L) X g 7 = some (some (.inr (.sched s7))) ∧ s7.site ≠ .elect := by
    have h7 := stateAt_sched he6 hs6
    cases hn : Scheduler.next L g Prologue.schedStart e6 with
    | none => exact Or.inl (by rw [h7, hn]; rfl)
    | some o =>
      cases o with
      | none => exact absurd (by rw [h7, hn]; rfl) (tracked hpre hX g 7 hg)
      | some s7 => exact Or.inr ⟨s7, by rw [h7, hn]; rfl, Scheduler.next_site_ne_elect hn⟩
  have hrun := sched_run (tracked hpre hX) hg hbase ((X.tr g).length - 7) (by omega)
  rw [show 7 + ((X.tr g).length - 7) = (X.tr g).length by omega, hσ] at hrun
  rcases hrun with h | ⟨s', h, hs'⟩
  · cases h
  · cases h
    exact hs' hs

/-- A thread past event 6 of a role warp has made its election there: the role's full-mask
election at `pc`. -/
theorem role_elect_event (hg : g < L.threads) {j pc' mask inst leader : Nat}
    (hel : X.Elect (g, j) pc' mask inst leader) (hw0 : warpOf L g ≠ 0) :
    j = 6 ∧ 6 < (X.tr g).length := by
  have hj := len_of_get hel
  rcases elect_pos hpre hX hg hel with ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd h hw0
  · exact ⟨h, by simp only at hj; omega⟩

end

end
end PTX.Kernels.Fp16Gemm8192.Proof
