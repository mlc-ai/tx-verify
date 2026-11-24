-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReadOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StageUnique
public import Lemmas.TensorStore.SourceBytes
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputStageReuse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StageWriteClasses
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2RawWriteKinds

@[expose] public section

/-! # Transport the staged byte through its output tensor store -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputValues

open PTX Wg0

/-- A performed generic write whose machine state is an output staging element. -/
def StageWrite (P : Params) (L : Launch) (X : Execution)
    (w : AsyncCopy.Ref) (a : Acc) (bytes : List Byte) : Prop :=
  ∃ (g i : Nat) (d : D) (j : Fin 4) (v : Fin 8),
    w = .thread (g, i) ∧ X.Writes (g, i) a bytes ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) ∧
      d.site = .oStage j v

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem stage_eq (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    {a a' : Acc} {bs bs' : List Byte} {w w' : AsyncCopy.Ref} {l : Loc}
    (hw : StageWrite P L X w a bs) (hw' : StageWrite P L X w' a' bs') (hc : a.Covers l)
    (hc' : a'.Covers l) :
    w = w' := by
  obtain ⟨g, i, d, j, v, rfl, ⟨tag, he⟩, hd, hsite⟩ := hw
  obtain ⟨g', i', d', j', v', rfl, ⟨tag', he'⟩, hd', hsite'⟩ := hw'
  exact congrArg AsyncCopy.Ref.thread
    (Wg0StageUnique.sameByte hpre hX hs ht he he' rfl rfl hd hd' hsite hsite' hc hc')

private theorem source_window {L : Launch} {g : Nat} (j : Fin 4) (s : Result.OutputSlot)
    (hw : warpOf L g < 2) :
    let l := shLoc L g (stageOff s.2.1.val (tmaX j.val (warpOf L g) + s.1.val) + s.2.2.val)
    l.space = .shared ∧ L.sharedBase + 65536 ≤ l.addr ∧ l.addr < L.sharedBase + 131072 := by
  dsimp only
  let c := tmaX j.val (warpOf L g) + s.1.val
  have hcol : c < 512 := Result.outputColumn_lt j hw s.1.isLt
  have hlt := stageOff_lt s.2.1.isLt hcol
  have hEven : stageOff s.2.1.val c % 2 = 0 := by
    unfold stageOff stageRel stageBase stageTileBytes
    omega
  have hb := s.2.2.isLt
  have hlo : 65536 ≤ stageOff s.2.1.val c := by
    simp [stageOff, stageBase]
  change Space.shared = .shared ∧
    L.sharedBase + 65536 ≤ L.sharedBase + (stageOff s.2.1.val c + s.2.2.val) ∧
    L.sharedBase + (stageOff s.2.1.val c + s.2.2.val) < L.sharedBase + 131072
  unfold stageBase stageBytes at hlt
  exact ⟨rfl, by omega, by omega⟩

private theorem nonstage_before (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    {other : AsyncCopy.Ref} {a fp : Acc} {raw bytes : List Byte} {l : Loc} {w b : Nat} {d : D}
    {tile : Fin 4} {chunk : Fin 8} (hmem : X.MemWrites other fp raw) (hc : fp.Covers l)
    (hnot : ¬ StageWrite P L X other fp raw) (hw : X.Writes (w, b) a bytes) (hwcov : a.Covers l)
    (hd : Frame.stateAt (Machine.code P L) X w b = some (some (.wg0 d)))
    (hstage : d.site = .oStage tile chunk) (hspace : l.space = .shared)
    (hlo : L.sharedBase + 65536 ≤ l.addr) (hhi : l.addr < L.sharedBase + 131072) :
    ByteCausality L X l other (.thread (w, b)) := by
  rcases Wg2.raw_read_competing_kinds hX hmem hc hspace with
    ⟨⟨g, i⟩, rfl, hwr⟩ | ⟨i, x, y, z, rfl⟩
  · rcases StageWriteClasses.from_covered_write hpre hX hs ht hwr hc hspace hlo hhi with
      ⟨otherStage, tile', chunk', hstate, hsite⟩ | ⟨dq, r, s, u, hstate, hsite, hbuf, _, hf⟩
    · exact (hnot ⟨g, i, otherStage, tile', chunk', rfl, hwr, hstate, hsite⟩).elim
    · let cta := ctaOf L w
      have hCta : ctaOf L g = cta := by
        have hdq := RoleSharedWrites.shared_cta hpre hs hX ht hwr (hc.1.symm.trans hspace)
        have hout := RoleSharedWrites.shared_cta hpre hs hX ht hw (hwcov.1.symm.trans hspace)
        exact hdq.symm.trans (hc.2.1.symm.trans (hwcov.2.1.trans hout))
      obtain ⟨_, _, _, _, hOut, _, _⟩ := Frame.fired_site hs hX hw.choose_spec hd
      have hwg := (show Inv P L w d from hOut).wg
      have hg := Frame.lt_of_get hX hwr.choose_spec
      have hdq : wgOf L g = 2 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hstate
      obtain ⟨lane, hG⟩ := RawRing.consumer_of_wg2 hpre hCta hdq
      obtain ⟨softmaxLane, hW⟩ := GemmRing.softmax_thread hpre (cta := cta) rfl hwg
      have he : X.get (g, i) = some ⟨hwr.choose, .wr fp raw⟩ := hwr.choose_spec
      generalize htag : hwr.choose = tag at he hf
      clear htag
      rw [hG] at hstate he hf hwr ⊢
      rw [hW] at hw hd ⊢
      obtain ⟨offset, rfl⟩ :=
        OutputStageReuse.dequantStoreByte_of_cover hpre hsite hf he hwr hc
      exact OutputStageReuse.dequant_store_before_stage hpre hX hs ht he hstate hsite
        hbuf hf hd hstage hw offset hwcov
  · obtain ⟨_, _, hwindow, _⟩ := TensorSharedBounds.written_byte_windows hpre hX hs ht hmem hc
    rcases hwindow with ⟨_, hq⟩ | ⟨hraw, _⟩
    · omega
    · omega

/-- A performed tensor write contains the corresponding byte of its actual staged pair. -/
theorem of_write {g i : Nat} {address : Nat} {sp : TensorStore.Spec} {d : D} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomplete : Complete L X) (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hi : X.TensorStoreIssue (g, i) address sp)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hj : d.site = .tmaStore j)
    (s : Result.OutputSlot) {dst : Acc} {out : Byte}
    (hw : X.MemWrites (.async (g, i) (.write (.store s.1.val s.2.1.val s.2.2.val))) dst [out]) :
    ∃ (w b : Nat) (ds : D) (a : Acc) (k : Fin 8) (sub pos : Fin 4),
      Frame.stateAt (Machine.code P L) X w b = some (some (.wg0 ds)) ∧
      ds.site = .oStage j k ∧ ds.sub = sub.val ∧ head L w = s.2.1.val ∧
      X.Writes (w, b) a (stagePair P L w ds (4 * k.val + sub.val)).toBytes ∧
      a.loc.at pos.val =
        shLoc L g (stageOff s.2.1.val (tmaX j.val (warpOf L g) + s.1.val) + s.2.2.val) ∧
      some out = (stagePair P L w ds (4 * k.val + sub.val)).toBytes[pos.val]? := by
  obtain ⟨o, addr, byte, ho, hiss, _, hwb, _, hbyte, _⟩ := hw
  have hout : out = byte := (List.cons.inj hbyte).1
  subst byte
  have hsp : o.spec = sp := by
    obtain ⟨_, he⟩ := hi
    obtain ⟨_, he'⟩ := hiss
    rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorStore.injEq] at he'
    exact he'.2.2.symm
  have he := hi.choose_spec
  have hg := Frame.lt_of_get hX he
  have hSound (g : Nat) (hg : g < L.threads) := (hs g hg).machine
  have hw := Wg0OutputControl.outputWarp hX (hSound g hg) he hd hj
  obtain ⟨_, hread, _⟩ := Wg0OutputTrace.tileFootprint hpre hX (hSound g hg) hi hd hj hw s
  have hred : sp.reduce = none := by
    rw [(Wg0OutputTrace.tileSpec hpre hX (hSound g hg) hi hd hj).2]
    rfl
  obtain ⟨w, b, ds, a, k, sub, pos, hst, hsite, hsub, hh, hwr, hloc, hcov, hb⟩ :=
    OutputReadOrder.of_issue hpre hX hcomplete hSound ht hi hd hj s
  let l := shLoc L g (stageOff s.2.1.val (tmaX j.val (warpOf L g) + s.1.val) + s.2.2.val)
  let source := (stagePair P L w ds (4 * k.val + sub.val)).toBytes
  let r : AsyncCopy.Ref := .async (g, i) (.read (.store s.1.val s.2.1.val s.2.2.val))
  have hc : StageWrite P L X (.thread (w, b)) a source :=
    ⟨w, b, ds, j, k, rfl, hwr, hst, hsite⟩
  have hord : SourceOrdered L X r l (.thread (w, b)) a source := by
    refine ⟨Or.inl hwr, hcov, .direct hb, ?_⟩
    intro other fp bs hm hcov'
    by_cases hstage : StageWrite P L X other fp bs
    · exact .inl (stage_eq hpre hX hSound ht hstage hc hcov' hcov)
    · obtain ⟨hspace, hlo, hhi⟩ := source_window j s hw
      exact .inr (.inl (nonstage_before hpre hX hs ht
        hm hcov' hstage hwr hcov hst hsite hspace hlo hhi))
  rw [← hsp] at hred hread
  have hbytes := hX.store_read_byte ho hred hwb hread hord
  refine ⟨w, b, ds, a, k, sub, pos, hst, hsite, hsub, hh, hwr, hloc, ?_⟩
  rw [hbytes, ← hloc]
  simp [wbyte, Loc.at, source]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputValues
