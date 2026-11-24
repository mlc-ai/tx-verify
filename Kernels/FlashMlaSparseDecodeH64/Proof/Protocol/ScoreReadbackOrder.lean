-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmFirstWriteOrder
import Lemmas.Tcgen05.TcProgramOrder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmemLoadWaits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreBytes

@[expose] public section

/-! # Ordering other QK writes around the score load -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback

open PTX AsyncCopy PTX.Flow PTX.MbarRing GemmRing

noncomputable section

set_option maxRecDepth 4096

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem same_scope {g h : Nat} (hc : SameCta L g h) (scope : MbarScope) :
    MbarScopeIncludes L scope g h := by
  cases scope
  · exact hc
  · exact ⟨hc.1, hc.2.1, congrArg L.clusterOfCta hc.2.2⟩
  · exact ⟨hc.1, hc.2.1⟩
  · exact ⟨hc.1, hc.2.1⟩

/-- Earlier QK writes of the elected issuer target the same accumulator as the selected write,
so their order follows from the actual instruction pipeline. -/
theorem earlier_qk_write
    {issuer i j a b : Nat} {p k : Fin 16}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hi : X.MmaIssue (issuer, i) Wg1Mma.tmemP (MmaDataTrace.qkOperands L issuer a p)
      (MmaDataTrace.qkAccum p) [0, 0, 0, 0])
    (hj : X.MmaIssue (issuer, j) Wg1Mma.tmemP (MmaDataTrace.qkOperands L issuer b k)
      (MmaDataTrace.qkAccum k) [0, 0, 0, 0])
    (hij : i < j) : TcMma.WriteBefore L X (issuer, i) (issuer, j) := by
  have hissuer := Frame.lt_of_get hX hi.choose_spec
  exact .inl (TcMma.Before.of_mma_po hi hj hissuer rfl hij ⟨rfl, rfl, rfl, rfl, rfl⟩)

private theorem score_publication_for_qk_poll {cta issuer j block : Nat} {lane : Fin 128}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer) (hWarp : warpOf L issuer = 4)
    (hp : block / 2 + 1 ≤ PTX.Flow.okPolls (GemmRing.score L cta (rawSlot block))
      ((X.tr issuer).take j)) :
    let g := softmax L cta lane
    let m := GemmRing.score L cta (rawSlot block)
    ∃ a arrTag ascope k ktag parity ws,
      X.get (g, a) = some ⟨arrTag, .arrive m 0 1 true ascope⟩ ∧
      X.get (issuer, k) = some ⟨ktag, .wait m parity true true ws⟩ ∧ k < j ∧
      PTX.Flow.arrivals m ((X.tr g).take a) = block / 2 ∧
      Witness L X (.thread (g, a)) (issuer, k) := by
  let g := softmax L cta lane
  let slot := rawSlot block
  let m := GemmRing.score L cta slot
  let u := block / 2
  obtain ⟨k, kt, parity, acq, ws, hkj, hk, hkCount⟩ := Poll.exists_nth hp
  obtain ⟨rfl, _⟩ := RingSourceSites.actual_wait_acquire hX hk rfl
  let R := actualScoreRing (slot := slot) hpre hX hs hmma hWarp
  change okPolls m ((X.tr issuer).take k) = u at hkCount
  have hnth : Poll.nth X m issuer u = k := by rw [← hkCount, Poll.nth_eq hk]
  have hPres : X.RefPresent (.thread (R.wE 0 (u + 1))) := by
    change X.RefPresent (.thread (issuer, Poll.nth X m issuer (u + 1 - 1)))
    rw [Nat.add_sub_cancel, hnth]
    exact ⟨_, hk⟩
  obtain ⟨hItem, hWitness⟩ := R.observes_empty hX.depAcyclic hPres lane
  let F := actual_score_history (cta := cta) (slot := slot) hpre hX hs
  obtain ⟨_, ⟨arrTag, ascope, hArrive⟩, hOrdinal⟩ := F.S_rec hItem
  let a := (Unit.it X m (softmax L cta) lane u).2
  change PTX.Flow.arrivals m ((X.tr g).take a) = u at hOrdinal
  change Witness L X (.thread (g, a)) (issuer, Poll.nth X m issuer (u + 1 - 1)) at hWitness
  rw [Nat.add_sub_cancel, hnth] at hWitness
  exact ⟨a, arrTag, ascope, k, kt, parity, ws, hArrive, hk, hkj, hOrdinal, hWitness⟩

/-- The score generation's completion is ordered before a later MMA event once the MMA
prefix includes that generation's acquire. Ring attribution identifies the publishing arrival
of this exact WG0 lane. -/
theorem read_before_qk_of_counts
    {cta issuer ld wait j block : Nat} {lane : Fin 128}
    {tag : Nat} {consumer : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer) (hWarp : warpOf L issuer = 4)
    (hc : ctaOf L issuer = cta) (he : X.get (issuer, j) = some consumer)
    (hwait : X.get (softmax L cta lane, wait) = some ⟨tag, .tc .waitLd⟩)
    (hlt : ld < wait)
    (hn : PTX.Flow.arrivals (GemmRing.score L cta (rawSlot block))
      ((X.tr (softmax L cta lane)).take wait) = block / 2)
    (hp : block / 2 + 1 ≤ PTX.Flow.okPolls (GemmRing.score L cta (rawSlot block))
      ((X.tr issuer).take j)) :
    TcMma.ReadBefore L X .ld (softmax L cta lane, ld) (issuer, j) := by
  let g := softmax L cta lane
  let slot := rawSlot block
  let m := GemmRing.score L cta slot
  have hi := Frame.lt_of_get hX he
  have hg := Frame.lt_of_get hX hwait
  obtain ⟨a, arrTag, ascope, k, kt, parity, ws, hArrive, hk, hkj, hOrdinal, hWitness⟩ :=
    score_publication_for_qk_poll (lane := lane) hpre hX hs hmma hWarp hp
  have hLe : wait ≤ a := arrival_index_ge hArrive
    (by simp [arrivesOn, sourceArrive]) hOrdinal hn.le
  have hgcta : ctaOf L g = cta := by
    have := lane.isLt
    simp only [g, softmax, ctaOf, hpre.block]
    omega
  have hSync : MSync L X (g, wait) (issuer, j) :=
    ⟨(g, a), (issuer, k), m, ascope, ws, ⟨0, 1, arrTag, hArrive⟩,
      (hWitness.waitObserves hk).2,
      ⟨same_scope ⟨hg, hi, hgcta.trans hc.symm⟩ ascope,
        same_scope ⟨hi, hg, hc.trans hgcta.symm⟩ ws⟩,
      rfl, hkj, PTX.len_of_get he, rfl, hLe⟩
  exact .inl ⟨(g, wait), ⟨tag, hwait⟩, rfl, hlt, .inl (.single (.inr (.inr (.inl hSync))))⟩

/-- Once the score load's own wait has occurred, no later QK block can overwrite its
Tensor Memory until that wait has completed. The count covers both alternating slots. -/
theorem read_before_later_qk
    {cta issuer ld wait j tag : Nat} {lane : Fin 128}
    {d : Wg0.D} {q : Wg1Mma.D} {chunk : Fin 16} {consumer : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer)
    (hc : ctaOf L issuer = cta) (he : X.get (issuer, j) = some consumer)
    (hq : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma q)))
    (hqSite : q.site = .qkMma chunk) (hblock : d.block < q.i)
    (hwait : X.get (softmax L cta lane, wait) = some ⟨tag, .tc .waitLd⟩)
    (hstate : Frame.stateAt (Machine.code P L) X (softmax L cta lane) wait =
      some (some (.wg0 d))) (hsite : d.site = .scoreWait)
    (hlt : ld < wait) : TcMma.ReadBefore L X .ld (softmax L cta lane, ld) (issuer, j) := by
  let g := softmax L cta lane
  let slot := rawSlot d.block
  have hg := Frame.lt_of_get hX hwait
  have hi := Frame.lt_of_get hX he
  have hgcta : ctaOf L g = cta := by
    have := lane.isLt
    simp only [g, softmax, ctaOf, hpre.block]
    omega
  have hn := Wg0GemmTrace.composed_scoreWait_arrivals hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hstate hsite
  rw [hgcta] at hn
  have hp := Wg1MmaGemmTrace.score_polls_before_qk hpre hi slot
    ((hs issuer hi).machine.produces (hX.thr issuer hi)) hq hqSite
  change okPolls (GemmRing.score L (ctaOf L issuer) slot) ((X.tr issuer).take j) =
    (q.i + (1 - slot.val)) / 2 at hp
  rw [hc] at hp
  have hWarp : warpOf L issuer = 4 := RingRoleGeometry.of_trace hX hi (hs issuer hi).machine hq
  apply read_before_qk_of_counts (block := d.block) hpre hX hs hmma hWarp hc he hwait hlt hn
  rw [hp]
  change d.block / 2 + 1 ≤ (q.i + (1 - d.block % 2)) / 2
  omega

/-- A later QK overwrite forces the load wait even when the load itself is the proof boundary. -/
theorem read_before_later_qk_at_score_load
    {cta issuer ld j : Nat} {lane : Fin 128} {words : List Value}
    {d : Wg0.D} {arm part : Fin 2}
    {q : Wg1Mma.D} {chunk : Fin 16} {consumer : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hmma : MmaIssuer P L X cta issuer)
    (hc : ctaOf L issuer = cta) (he : X.get (issuer, j) = some consumer)
    (hq : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma q)))
    (hqSite : q.site = .qkMma chunk) (hblock : d.block < q.i)
    (hload : X.TLd (softmax L cta lane, ld) (Wg0.scoreLoadColumn part) words .s32x32b)
    (hd : Frame.stateAt (Machine.code P L) X (softmax L cta lane) ld = some (some (.wg0 d)))
    (hsite : d.site = .scoreLoad arm part) :
    TcMma.ReadBefore L X .ld (softmax L cta lane, ld) (issuer, j) := by
  let g := softmax L cta lane
  let slot := rawSlot d.block
  let m := GemmRing.score L cta slot
  have hgcta : ctaOf L g = cta := by
    have := lane.isLt
    simp only [g, softmax, ctaOf, hpre.block]
    omega
  have hi := Frame.lt_of_get hX he
  have hg := Frame.lt_of_get hX hload.choose_spec
  have hp := Wg1MmaGemmTrace.score_polls_before_qk hpre hi slot
    ((hs issuer hi).machine.produces (hX.thr issuer hi)) hq hqSite
  change okPolls (GemmRing.score L (ctaOf L issuer) slot) ((X.tr issuer).take j) =
    (q.i + (1 - slot.val)) / 2 at hp
  rw [hc] at hp
  have hPoll : d.block / 2 + 1 ≤ okPolls m ((X.tr issuer).take j) := by
    change d.block / 2 + 1 ≤ okPolls (GemmRing.score L cta slot) ((X.tr issuer).take j)
    rw [hp]
    change d.block / 2 + 1 ≤ (q.i + (1 - d.block % 2)) / 2
    omega
  have hWarp : warpOf L issuer = 4 := RingRoleGeometry.of_trace hX hi (hs issuer hi).machine hq
  obtain ⟨a, tag, scope, _, _, _, _, hArr, _, _, hOrd, _⟩ :=
    score_publication_for_qk_poll (lane := lane) (block := d.block) hpre hX hs hmma hWarp hPoll
  have hn := Wg0GemmTrace.composed_scoreLoad_arrivals hpre
    ((hs g hg).machine.produces (hX.thr g hg)) hd hsite
  rw [hgcta] at hn
  change arrivals m ((X.tr g).take ld) = d.block / 2 at hn
  have haGe : ld ≤ a := arrival_index_ge hArr (by simp [arrivesOn, sourceArrive])
    hOrd hn.le
  have haGt : ld < a := by
    by_contra! hn
    obtain rfl : a = ld := by omega
    cases congrArg Event.kind (Option.some.inj (hload.choose_spec.symm.trans hArr))
  obtain ⟨⟨_, pub, _, hPub, hPubState⟩, _, _, _, _⟩ := arrival (obj := .soReady) hpre hX
    (hs g (Frame.lt_of_get hX hArr)).machine ht hArr rfl
  have hOutside (s : Wg0.D) (hEq : Machine.ThreadD.wg0 pub = .wg0 s) :
      ¬ (s.site = .scoreWait ∨ ∃ a k, s.site = .scoreLoad a k) := by
    cases hEq
    simp [hPub]
  obtain ⟨w, wt, sw, hwlt, hw, hsw, hswSite, hswBlock⟩ :=
    TmemLoadWaits.score_wait_before_later_state hpre hX hs hload hd hsite haGt
      hArr hPubState hOutside
  exact read_before_later_qk hpre hX hs hmma hc he hq hqSite (hswBlock.symm ▸ hblock)
    hw hsw hswSite hwlt

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback
