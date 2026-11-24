-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RescaleTmemReadSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0RescaleSuccessor
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualQkBlock
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory
import Lemmas.Tcgen05.TcMmaRead

@[expose] public section

/-! # The actual FP32 words consumed by rescaling and the epilogue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputTmemWords

open PTX PTX.Flow PTX.AsyncCopy Wg0 Protocol
open OutputTmemReadSource
open PvAccumulatorSource (Issue)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i issuer : Nat} {d : D} {tile : Fin 4}

/-- The last issue of each output half has a numerical result once its completion is observed. -/
def PvLaneResults (P : Params) (L : Launch) (X : Execution) (g block : Nat) : Prop :=
  ∀ {issuer src c : Nat} {rank : Fin 16} (tile : Fin 4) (reg : Fin 64),
    ctaOf L issuer = ctaOf L g → tidOf L g < 128 →
    Frame.stateAt (Machine.code P L) X issuer src =
      some (some (.mma ⟨.pvMma (lastIssue tile), block⟩)) →
    Issue L X issuer src block (lastIssue tile) →
    TracksMma X (issuer, src) (issuer, c) → rank ∈ X.tcNotified (issuer, c) →
    ∃ x : ℝ, TcMma.Result L Assumptions.all X (issuer, src) (outputCell L g tile reg)
      (.float .f32 x)

/-- The actual load returns the source cell's FP32 result word. -/
theorem word_of_result {ld src : EvId} {address : Nat} {words : List Value}
    {reg : Nat} {cell : TcMma.Cell} {x : ℝ}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hload : X.TLd ld address words .s32x32b)
    (hcell : TcMma.LoadCell L X ld reg cell) (hsource : TcMma.ReadSource L X .ld src ld cell)
    (hvalue : TcMma.Result L Assumptions.all X src cell (.float .f32 x)) :
    words[reg]? = some (.float .f32 x) :=
  TcMma.LoadReadOk.f32 hX.tcRead.1 hload hcell hsource (.inl hvalue)

section
variable {tag : Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
include hpre hX hs

/-- At a rescale wait, one actual prior-block PV cell supplies the exact value of the selected
word. The current QK notification has completed that PV issue. -/
theorem rescale_word_from_prior (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleWait tile) (hwait : X.get (g, i) = some ⟨tag, .tc .waitLd⟩)
    (reg : Fin 64) :
    ∃ (src c : Nat) (rank : Fin 16),
      Frame.stateAt (Machine.code P L) X issuer src =
        some (some (.mma ⟨.pvMma (lastIssue tile), d.block - 1⟩)) ∧
      Issue L X issuer src (d.block - 1) (lastIssue tile) ∧
      TracksMma X (issuer, src) (issuer, c) ∧ rank ∈ X.tcNotified (issuer, c) ∧
      d.rescaleWords.length = 64 ∧
      ∀ x : ℝ, TcMma.Result L Assumptions.all X (issuer, src) (outputCell L g tile reg)
        (.float .f32 x) → d.rescaleWords[reg.val]? = some (.float .f32 x) := by
  obtain ⟨ld, src, c, ct, sp, rank, _, hsrcLt, hc, hn, hSrc, hIssue, hLoad, hLen, hCell, hRead⟩ :=
    RescaleTmemReadSource.actual_previous_source_at_wait hpre hX hs hmma hd hsite hwait reg
  have hTrack : TracksMma X (issuer, src) (issuer, c) :=
    ⟨rfl, hsrcLt, .inl ⟨_, _, _, _, hIssue⟩, sp, ct, hc⟩
  exact ⟨src, c, rank, hSrc, hIssue, hTrack, hn, hLen, fun _ => word_of_result hX hLoad hCell hRead⟩

/-- At an epilogue load wait, the same final PV cell gives the selected register's exact word. -/
theorem final_word_from_pv (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .oWait tile) (hwait : X.get (g, i) = some ⟨tag, .tc .waitLd⟩) (reg : Fin 64) :
    ∃ (src c : Nat) (rank : Fin 16),
      Frame.stateAt (Machine.code P L) X issuer src =
        some (some (.mma ⟨.pvMma (lastIssue tile), d.block⟩)) ∧
      Issue L X issuer src d.block (lastIssue tile) ∧
      TracksMma X (issuer, src) (issuer, c) ∧ rank ∈ X.tcNotified (issuer, c) ∧
      d.oWords.length = 64 ∧
      ∀ x : ℝ, TcMma.Result L Assumptions.all X (issuer, src) (outputCell L g tile reg)
        (.float .f32 x) → d.oWords[reg.val]? = some (.float .f32 x) := by
  obtain ⟨ld, c, ct, sp, rank, p, src, hc, hp, hpSite, hpBlock, hn, hSrcIdx, hIssue, hLoad, hLen,
    hCell, hRead⟩ := actual_final_source_at_wait hpre hX hs hmma hd hsite hwait reg
  obtain ⟨j, hj, hSrc⟩ := PvIssueHistory.pv_state_of_commit hc hp hpSite (lastIssue tile)
  have heq : j = src := by omega
  subst j
  rw [hpBlock] at hSrc
  have hSrcLt : src < c := by have := (lastIssue tile).isLt; omega
  have hTrack : TracksMma X (issuer, src) (issuer, c) :=
    ⟨rfl, hSrcLt, .inl ⟨_, _, _, _, hIssue⟩, sp, ct, hc⟩
  exact ⟨src, c, rank, hSrc, hIssue, hTrack, hn, hLen, fun _ => word_of_result hX hLoad hCell hRead⟩

omit hpre hX hs in
/-- A tile is consumable when its 64 actual words are FP32 results. -/
theorem good_words_of_f32 {words : List Value} (hLen : words.length = 64)
    (hWords : ∀ j : Fin 64, ∃ x : ℝ, words[j.val]? = some (.float .f32 x)) :
    goodOutputWords words = true := by
  unfold goodOutputWords
  rw [Bool.and_eq_true]
  refine ⟨by rw [hLen]; rfl, List.all_eq_true.mpr ?_⟩
  intro v hv
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
  have hjlt := (List.getElem?_eq_some_iff.mp hj).1
  have jlt : j < 64 := hLen ▸ hjlt
  obtain ⟨x, hx⟩ := hWords ⟨j, jlt⟩
  rw [hj] at hx
  obtain rfl := Option.some.inj hx
  simp [outputWord, Assumptions.scoreHalf, valFloat_float, Except.toOption]

omit hpre hX hs in
private theorem lane_geometry {tag : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hw : X.get (g, i) = some ⟨tag, .tc .waitLd⟩) : tidOf L g < 128 := by
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hw hd
  have hn := (show Wg0.Inv P L g d from hInv).warpLt
  unfold warpOf at hn
  omega

/-- The final PV result makes all words at the epilogue wait consumable. -/
theorem final_good_words (hv : PvLaneResults P L X g d.block)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer) (hCta : ctaOf L issuer = ctaOf L g)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .oWait tile) (hw : X.get (g, i) = some ⟨tag, .tc .waitLd⟩) :
    goodOutputWords d.oWords = true := by
  have getWord := final_word_from_pv hpre hX hs hmma hd hsite hw
  obtain ⟨_, _, _, _, _, _, _, hLen, _⟩ := getWord 0
  apply good_words_of_f32 hLen
  intro reg
  obtain ⟨src, c, rank, hState, hIssue, hTrack, hNotify, _, hWord⟩ := getWord reg
  obtain ⟨x, hx⟩ := hv tile reg hCta (lane_geometry hX hs hd hw) hState hIssue hTrack hNotify
  exact ⟨x, hWord x hx⟩

/-- The preceding PV result makes all words at a rescale wait consumable. -/
theorem rescale_good_words (hv : PvLaneResults P L X g (d.block - 1))
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer) (hCta : ctaOf L issuer = ctaOf L g)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleWait tile) (hw : X.get (g, i) = some ⟨tag, .tc .waitLd⟩) :
    goodOutputWords d.rescaleWords = true := by
  have getWord := rescale_word_from_prior hpre hX hs hmma hd hsite hw
  obtain ⟨_, _, _, _, _, _, _, hLen, _⟩ := getWord 0
  apply good_words_of_f32 hLen
  intro reg
  obtain ⟨src, c, rank, hState, hIssue, hTrack, hNotify, _, hWord⟩ := getWord reg
  obtain ⟨x, hx⟩ := hv tile reg hCta (lane_geometry hX hs hd hw) hState hIssue hTrack hNotify
  exact ⟨x, hWord x hx⟩
end

private theorem issuer_at_cta (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    ∃ issuer, ctaOf L issuer = ctaOf L g ∧ GemmRing.MmaIssuer P L X (ctaOf L g) issuer := by
  let cta := ctaOf L g
  obtain ⟨lane, h⟩ := Wg1MmaLeader.cta_issuer (cta := cta) hpre hX
    (fun g hg => (hs g hg).machine)
  refine ⟨cta * L.block + 128 + lane.val, ?_, h⟩
  have hLane := lane.isLt
  change (cta * L.block + 128 + lane.val) / L.block = cta
  rw [hpre.block]
  omega

/-- The epilogue does not stop tracking when its actual final PV cells are available. -/
theorem final_wait_never_dismiss {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hv : ∀ {issuer tag}, GemmRing.MmaIssuer P L X (ctaOf L g) issuer →
      X.get (g, i) = some ⟨tag, .tc .waitLd⟩ → PvLaneResults P L X g d.block)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .oWait tile) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  obtain ⟨tag, kind⟩ := e
  cases kind <;> simp [Machine.next, Wg0.next, nextSite, hsite]
  case tc k =>
    cases k
    case waitLd =>
      obtain ⟨issuer, hCta, hIssuer⟩ := issuer_at_cta (g := g) hpre hX hs
      have hw := final_good_words hpre hX hs (hv hIssuer he) hIssuer hCta hd hsite he
      simp [hw]
    all_goals simp

/-- Rescaling does not stop tracking when the preceding PV result cells are available. -/
theorem rescale_wait_never_dismiss {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hv : ∀ {issuer tag}, GemmRing.MmaIssuer P L X (ctaOf L g) issuer →
      X.get (g, i) = some ⟨tag, .tc .waitLd⟩ → PvLaneResults P L X g (d.block - 1))
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleWait tile) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  by_cases hk : e.kind = .tc .waitLd
  · obtain ⟨tag, kind⟩ := e
    change kind = .tc .waitLd at hk
    subst kind
    obtain ⟨issuer, hCta, hIssuer⟩ := issuer_at_cta (g := g) hpre hX hs
    have hw := rescale_good_words hpre hX hs (hv hIssuer he) hIssuer hCta hd hsite he
    exact Wg0RescaleSuccessor.wait_never_dismiss he hd hsite hw
  · cases heKind : e.kind <;> simp [Machine.next, Wg0.next, nextSite, hsite, heKind]
    case tc cmd =>
      cases cmd
      case waitLd => exact (hk heKind).elim
      all_goals simp

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.OutputTmemWords
