-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarLedger
public import Lemmas.Async.AsyncOrigins
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Tmem.TmemPairHistory

@[expose] public section

namespace PTX
open AsyncCopy
open CtaBarrier
noncomputable section

/-- Two events are lanes of one record of a CTA's barrier history. -/
def CtaBarrier.SameRecord (X : Execution) (e f : EvId) : Prop :=
  ∃ (c i : Nat) (r : CtaBarrier.Record EvId),
    (X.barriers c)[i]? = some r ∧ e ∈ r.refs ∧ f ∈ r.refs

/-- A lane of a warp need of a `bar` event is a lane of the event's own record, unless it is an
exit record's event. -/
theorem warpNeed_record {L : Launch} {X : Execution} {e j : EvId} {pc id : Nat}
    {count : Option Nat} {fills : AsyncCopy.Ref → Prop}
    (hb : CtaBarHistoryOk L X)
    (he : X.get e = some ⟨pc, .bar id count .sync⟩)
    (hwarp : Need.node fills ∈ ctaBarWarpNeeds L X j) (hfill : fills (.thread e)) :
    CtaBarrier.SameRecord X e j := by
  obtain ⟨h, -, hfl⟩ := List.mem_map.mp hwarp
  cases hfl
  obtain ⟨i, r, y, hi, hjmem, heq, -, hopt⟩ := hfill
  cases heq
  rcases hopt with hymem | ⟨i', g, hi', hexit⟩
  · exact ⟨j.1 / L.block, i, r, hi, hymem, hjmem⟩
  · exfalso
    have hs := (hb.2 _ (hb.grid_of_get hi)).2.1 (.exit g e) (List.mem_of_getElem? hexit)
    obtain ⟨-, -, pc', hget⟩ := hs
    rw [he] at hget
    cases hget

/-- A record counted by the release that a `bar.sync` waits for makes its lane an arrival of the
waited generation. -/
theorem counted_waits {L : Launch} {X : Execution} {e j : EvId} {pc id : Nat}
    {count : Option Nat} (hb : CtaBarHistoryOk L X)
    (he : X.get e = some ⟨pc, .bar id count .sync⟩) (hcc : CtaBarCounted L X j e) :
    CtaBarWaits L X e j false true := by
  obtain ⟨key, ic, hkj, hcomp, i, r, hi, her, hle, hshape⟩ := hcc
  have hgrid := hb.grid_of_get hi
  have hsrc := (hb.2 _ hgrid).2.1 r (List.mem_of_getElem? hi)
  have hrun := (hb.2 _ hgrid).2.2
  obtain ⟨last, hrun⟩ := hrun
  rcases hshape with ⟨w, cnt, lanes, s, hr, hat, hgen⟩ | ⟨g, hexit⟩
  · subst hr
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp her
    obtain ⟨hpblock, hpcta, pc', hisarr⟩ := hsrc p hp
    have hethr : e.1 < L.threads := by
      have hval : e.1 = (j.1 / L.block) * L.block + p.1 := by rw [← hpe]; exact hpcta
      rw [Launch.threads, hval]
      calc (j.1 / L.block) * L.block + p.1 < (j.1 / L.block) * L.block + L.block := by omega
        _ = ((j.1 / L.block) + 1) * L.block := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ L.grid * L.block := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨s', t, hat', hperf⟩ := CtaBarrier.run_at_record hrun hi
    have hsame : s' = s := by
      have h1 : (Except.ok s' : Except CtaBarrier.Error CtaBarrier.State) =
          Except.ok s := hat'.symm.trans hat
      exact Except.ok.inj h1
    subst s'
    have hgenof : CtaBarrier.GenerationOf L.block (X.barriers (j.1 / L.block)) e (key % 16)
        (key / 16) :=
      ⟨i, s, w, cnt, lanes, p.1, hi, hat, by rw [← hpe]; exact hp, hgen, t, hperf⟩
    have hisarr' : X.IsBarArrival e (key % 16) cnt pc' := by rw [← hpe]; exact hisarr
    have hgetj : ∃ ev, X.get j = some ev := by
      obtain ⟨cnt', pc', hget⟩ := hkj.2.1
      exact ⟨_, hget⟩
    have hcta : SameCta L e.1 j.1 :=
      ⟨hethr, hkj.1, hb.ref_cta (List.mem_of_getElem? hi) her⟩
    have hgenof' : CtaBarrier.GenerationOf L.block (X.barriers (e.1 / L.block)) e (key % 16)
        (key / 16) := by
      rw [hcta.2.2]; exact hgenof
    have harr : CtaBarArrivalK L X e key := ⟨hethr, ⟨cnt, pc', hisarr'⟩, hgenof'⟩
    exact ⟨⟨_, he⟩, hgetj, .inr (.inl ⟨rfl, rfl, hcta, key, harr, hkj⟩)⟩
  · exfalso
    subst hexit
    obtain ⟨-, -, pc', hget⟩ := hsrc
    rw [he] at hget
    cases hget


/-- A node need is needed exactly when its condition holds. -/
theorem mem_needsIf_node {P : Prop} {ns : List Need} {fills : AsyncCopy.Ref → Prop} :
    Need.node fills ∈ needsIf P ns ↔ P ∧ Need.node fills ∈ ns := by
  unfold needsIf
  by_cases h : P <;> simp [h]

/-- A masked warp collective's wait is no `bar.sync`: its source is an event of the class. -/
theorem maskWait_not_bar {Q V : Type} {L : Launch} {X : Execution} {e j : EvId} {pc id : Nat}
    {count : Option Nat} {c : Kind → Option (WarpPart Q V)}
    (he : X.get e = some ⟨pc, .bar id count .sync⟩) (hnone : c (.bar id count .sync) = none)
    (hmw : MaskWait L c X e j) : False := by
  rcases MaskWait.src (L := L) hmw with ⟨pc', k, q, hget, hc⟩ | ⟨pc', hget⟩
  · rw [he] at hget
    cases hget
    rw [hnone] at hc
    cases hc
  · rw [he] at hget
    cases hget

/-- A warp-collective `tcgen05` event is no `bar.sync`. -/
theorem tcK_not_bar {X : Execution} {e : EvId} {pc id : Nat}
    {count : Option Nat} {n : Nat}
    (he : X.get e = some ⟨pc, .bar id count .sync⟩) (htk : X.TcK e n) : False := by
  obtain ⟨⟨ev', hget, hbit⟩, -⟩ := htk
  rw [he] at hget
  cases hget
  simp [isTcColl] at hbit

/-- A `bar.sync` event that fills a need of `j` is either an arrival of the generation whose
release `j` waits for, or a lane of a record of `j`'s own barrier history. -/
theorem ctaBar_witness_cases {L : Launch} {X : Execution} {e j : EvId} {pc id : Nat}
    {count : Option Nat} (hb : CtaBarHistoryOk L X) (hv : EffectValidity L X)
    (hp : Tmem.Pair.HistoriesOk L X) (hc : ClusterHistoryOk L X)
    (he : X.get e = some ⟨pc, .bar id count .sync⟩)
    (ho : Witness L X (.thread e) j) :
    CtaBarWaits L X e j false true ∨ CtaBarrier.SameRecord X e j := by
  obtain ⟨fills, hmem, -, hfill⟩ := ho
  cases hg : X.get j with
  | none => simp only [Needs, hg, List.not_mem_nil] at hmem
  | some ev =>
    obtain ⟨pcj, kind⟩ := ev
    simp only [Needs, hg] at hmem
    cases kind with
    | bar id' count' mode =>
      cases mode with
      | sync =>
        simp only [KindNeeds, ctaBarNeeds, List.mem_append, List.mem_cons] at hmem
        rcases hmem with hwarp | hcond | hcount
        · exact .inr (warpNeed_record hb he hwarp hfill)
        · cases hcond
        · obtain ⟨y, hy, hcy⟩ := List.mem_flatMap.mp hcount
          by_cases hcc : CtaBarCounted L X j y
          · simp only [needsIf, hcc, ite_true, List.mem_singleton, Need.node.injEq] at hcy
            rw [hcy] at hfill
            cases hfill
            exact .inl (counted_waits hb he hcc)
          · simp only [needsIf, hcc, ite_false, List.not_mem_nil] at hcy
      | arrive =>
        simp only [KindNeeds, ctaBarNeeds, List.mem_append] at hmem
        rcases hmem with hwarp | hempty
        · exact .inr (warpNeed_record hb he hwarp hfill)
        · cases hempty
    | shfl mode a b c recv ok =>
      simp only [KindNeeds, maskNeeds, hg, shflClass] at hmem
      obtain ⟨l, -, hfl⟩ := List.mem_map.mp hmem
      cases hfl
      obtain ⟨j', heq, hmw⟩ := hfill
      cases heq
      exact absurd hmw (maskWait_not_bar he rfl)
    | vote mask a ballot =>
      simp only [KindNeeds, maskNeeds, hg, voteClass] at hmem
      obtain ⟨l, -, hfl⟩ := List.mem_map.mp hmem
      cases hfl
      obtain ⟨j', heq, hmw⟩ := hfill
      cases heq
      exact absurd hmw (maskWait_not_bar he rfl)
    | voteMode mode mask a d =>
      simp only [KindNeeds, maskNeeds, hg, voteClass] at hmem
      obtain ⟨l, -, hfl⟩ := List.mem_map.mp hmem
      cases hfl
      obtain ⟨j', heq, hmw⟩ := hfill
      cases heq
      exact absurd hmw (maskWait_not_bar he rfl)
    | redux op signed mask a d =>
      simp only [KindNeeds, maskNeeds, hg, reduxClass] at hmem
      obtain ⟨l, -, hfl⟩ := List.mem_map.mp hmem
      cases hfl
      obtain ⟨j', heq, hmw⟩ := hfill
      cases heq
      exact absurd hmw (maskWait_not_bar he rfl)
    | match_ all wide mask a d p =>
      simp only [KindNeeds, maskNeeds, hg, matchClass] at hmem
      obtain ⟨l, -, hfl⟩ := List.mem_map.mp hmem
      cases hfl
      obtain ⟨j', heq, hmw⟩ := hfill
      cases heq
      exact absurd hmw (maskWait_not_bar he rfl)
    | elect mask inst leader =>
      simp only [KindNeeds, List.mem_map] at hmem
      obtain ⟨l, -, hfl⟩ := hmem
      cases hfl
      obtain ⟨j', pc', leader', heq, hget⟩ := hfill
      cases heq
      rw [he] at hget
      cases hget
    | warpBar mask inst =>
      simp only [KindNeeds, List.mem_map] at hmem
      obtain ⟨l, -, hfl⟩ := hmem
      cases hfl
      obtain ⟨j', heq, hwb⟩ := hfill
      cases heq
      obtain ⟨pc', hget⟩ := hwb
      rw [he] at hget
      cases hget
    | matrix op own recv =>
      simp only [KindNeeds, List.mem_map] at hmem
      obtain ⟨l, -, hfl⟩ := hmem
      cases hfl
      obtain ⟨j', heq, hmat | hexit⟩ := hfill
      · cases heq
        obtain ⟨⟨ev', hget, hbit⟩, -⟩ := hmat
        rw [he] at hget
        cases hget
        simp [isMatrix] at hbit
      · cases heq
        obtain ⟨⟨pc', hget⟩, -⟩ := hexit
        rw [he] at hget
        cases hget
    | setMaxReg increase count' inst =>
      simp only [KindNeeds, List.mem_map] at hmem
      obtain ⟨l, -, hfl⟩ := hmem
      cases hfl
      obtain ⟨j', heq, hsr⟩ := hfill
      cases heq
      obtain ⟨-, -, pc', inc', n', einst', finst', -, hreq⟩ := hsr
      simp only [SetMaxNReg.Request] at hreq
      rw [he] at hreq
      cases hreq
    | cluster op =>
      simp only [KindNeeds, clusterNeeds, List.mem_append] at hmem
      rcases hmem with hwarp | hcount
      · obtain ⟨h, -, hfl⟩ := List.mem_map.mp hwarp
        cases hfl
        obtain ⟨i, r, y, hi, hjmem, heq, -, hopt⟩ := hfill
        cases heq
        rcases hopt with hymem | ⟨i', g, hi', hexit⟩
        · rcases hc.ref_operation (List.mem_of_getElem? hi) hymem with ⟨pc', op', hget⟩ |
            ⟨pc', hget⟩ <;> rw [he] at hget <;> cases hget
        · have hmem : e ∈ (ClusterBarrier.Record.exit g e).refs := by
            simp only [ClusterBarrier.Record.refs, List.mem_singleton]
          rcases hc.ref_operation (List.mem_of_getElem? hexit) hmem with ⟨pc', op', hget⟩ |
            ⟨pc', hget⟩ <;> rw [he] at hget <;> cases hget
      · cases op with
        | arrive release aligned => simp only [List.not_mem_nil] at hcount
        | wait aligned =>
          obtain ⟨y, hy, hcc⟩ := List.mem_flatMap.mp hcount
          by_cases hcl : ClusterCounted L X j y
          · simp only [needsIf, hcl, ite_true, List.mem_singleton, Need.node.injEq] at hcc
            rw [hcc] at hfill
            cases hfill
            rcases hcl with ⟨phase, release, hw, ha⟩ | ⟨i, i', r, g, hi, hjmem, hr, hi', hexit⟩
            · obtain ⟨pc', aligned', hget⟩ := hc.arrival_present ha
              rw [he] at hget
              cases hget
            · have hmem : e ∈ (ClusterBarrier.Record.exit g e).refs := by
                simp only [ClusterBarrier.Record.refs, List.mem_singleton]
              rcases hc.ref_operation (List.mem_of_getElem? hexit) hmem with
                ⟨pc', op', hget⟩ | ⟨pc', hget⟩ <;> rw [he] at hget <;> cases hget
          · simp only [needsIf, hcl, ite_false, List.not_mem_nil] at hcc
    | bulkWait mode remaining =>
      simp only [KindNeeds, groupNeeds, List.mem_flatMap] at hmem
      obtain ⟨y, hy, hfl⟩ := hmem
      rw [mem_needsIf_node] at hfl
      obtain ⟨-, hfl⟩ := hfl
      simp only [List.mem_map] at hfl
      obtain ⟨p, -, hfl⟩ := hfl
      cases hfl
      cases hfill
    | asyncWait remaining =>
      simp only [KindNeeds, groupNeeds, List.mem_flatMap] at hmem
      obtain ⟨y, hy, hfl⟩ := hmem
      rw [mem_needsIf_node] at hfl
      obtain ⟨-, hfl⟩ := hfl
      simp only [List.mem_map] at hfl
      obtain ⟨p, -, hfl⟩ := hfl
      cases hfl
      cases hfill
    | wait m parity ok acquire scope =>
      cases ok with
      | false => simp only [KindNeeds, Bool.false_eq_true, ite_false, List.not_mem_nil] at hmem
      | true =>
        simp only [KindNeeds, ite_true, pollNeeds] at hmem
        obtain ⟨r, hr, hfl⟩ := List.mem_flatMap.mp hmem
        by_cases hmo : MbarObserved X r.id (.thread j)
        · simp only [needsIf, hmo, ite_true, List.mem_singleton, Need.node.injEq] at hfl
          rw [hfl] at hfill
          have hact := ((hv.tma.2.2.1 m).2.1 r hr).1
          rw [← hfill] at hact
          simp [objectAction, he] at hact
        · simp only [needsIf, hmo, ite_false, List.not_mem_nil] at hfl
    | tc k =>
      cases k with
      | resource group dst request =>
        simp only [KindNeeds, resourceNeeds, List.mem_append, List.mem_cons] at hmem
        rcases hmem with (htc | hcond | hrest) | hresult
        · obtain ⟨h, -, hfl⟩ := List.mem_map.mp htc
          cases hfl
          obtain ⟨j', heq, htk⟩ := hfill
          cases heq
          exact absurd htk (tcK_not_bar he)
        · cases hcond
        · by_cases hmw : Tmem.Pair.MustWait X j
          · simp only [needsIf, hmw, ite_true] at hrest
            rcases List.mem_cons.mp hrest with hcond | hrest
            · cases hcond
            · rcases List.mem_append.mp hrest with hpair | hreuse
              · cases group with
                | two =>
                  simp only [List.mem_map] at hpair
                  obtain ⟨l, -, hfl⟩ := hpair
                  cases hfl
                  obtain ⟨q, hq, hpe⟩ := hfill
                  rcases hpe with ⟨-, heq⟩ | ⟨-, heq⟩
                  · cases heq
                    obtain ⟨-, -, hgetall, -⟩ := (hp.2.1 q hq).1.2.2.1
                    have hget := hgetall l
                    rw [he] at hget
                    cases hget
                  · cases heq
                    obtain ⟨-, -, hgetall, -⟩ := (hp.2.1 q hq).1.2.1
                    have hget := hgetall l
                    rw [he] at hget
                    cases hget
                | one => simp only [List.not_mem_nil] at hpair
              · cases request with
                | alloc columns =>
                  simp only [List.mem_flatMap] at hreuse
                  obtain ⟨jj, hjj, hfl⟩ := hreuse
                  by_cases hrr : ReuseRelease L X j jj
                  · rw [ite_eq_left hrr] at hfl
                    simp only [List.mem_map] at hfl
                    obtain ⟨l, -, hfl⟩ := hfl
                    cases hfl
                    obtain ⟨d, hdmem, heq⟩ := hfill
                    cases heq
                    obtain ⟨-, -, hgetall, -⟩ :=
                      ((hp.1 (j.1 / L.block)).1 d (List.mem_of_getElem? hdmem)).2.2
                    have hget := hgetall l
                    rw [he] at hget
                    cases hget
                  · rw [ite_eq_right hrr] at hfl
                    simp only [List.not_mem_nil] at hfl
                | dealloc base columns => simp only [List.not_mem_nil] at hreuse
                | relinquish => simp only [List.not_mem_nil] at hreuse
          · simp only [needsIf, hmw, ite_false, List.not_mem_nil] at hrest
        · cases Tmem.Pair.allocResultNeeds_node L hresult
          obtain ⟨store, _, _, _, heq, hwrite⟩ := Tmem.Pair.AllocResultFill.written L hfill
          cases heq
          rw [he] at hwrite
          cases hwrite
      | ld a vals shape =>
        simp only [KindNeeds, tcNeeds, List.mem_map] at hmem
        obtain ⟨h, -, hfl⟩ := hmem
        cases hfl
        obtain ⟨j', heq, htk⟩ := hfill
        cases heq
        exact absurd htk (tcK_not_bar he)
      | st a vals shape =>
        simp only [KindNeeds, tcNeeds, List.mem_map] at hmem
        obtain ⟨h, -, hfl⟩ := hmem
        cases hfl
        obtain ⟨j', heq, htk⟩ := hfill
        cases heq
        exact absurd htk (tcK_not_bar he)
      | waitLd =>
        simp only [KindNeeds, tcNeeds, List.mem_map] at hmem
        obtain ⟨h, -, hfl⟩ := hmem
        cases hfl
        obtain ⟨j', heq, htk⟩ := hfill
        cases heq
        exact absurd htk (tcK_not_bar he)
      | waitSt =>
        simp only [KindNeeds, tcNeeds, List.mem_map] at hmem
        obtain ⟨h, -, hfl⟩ := hmem
        cases hfl
        obtain ⟨j', heq, htk⟩ := hfill
        cases heq
        exact absurd htk (tcK_not_bar he)
      | mma d operands accumulate disableOutput => simp only [KindNeeds, List.not_mem_nil] at hmem
      | commit spec => simp only [KindNeeds, List.not_mem_nil] at hmem
      | cp spec => simp only [KindNeeds, List.not_mem_nil] at hmem
      | shift spec => simp only [KindNeeds, List.not_mem_nil] at hmem
      | fenceBefore => simp only [KindNeeds, List.not_mem_nil] at hmem
      | fenceAfter => simp only [KindNeeds, List.not_mem_nil] at hmem
    | rd a bs => simp only [KindNeeds, List.not_mem_nil] at hmem
    | nc a bs => simp only [KindNeeds, List.not_mem_nil] at hmem
    | wr a bs => simp only [KindNeeds, List.not_mem_nil] at hmem
    | rmw a old new => simp only [KindNeeds, List.not_mem_nil] at hmem
    | clcQuery query response => simp only [KindNeeds, List.not_mem_nil] at hmem
    | clcIssue spec targets => simp only [KindNeeds, List.not_mem_nil] at hmem
    | tensorIssue mapAddress spec => simp only [KindNeeds, List.not_mem_nil] at hmem
    | tensorStore mapAddress spec => simp only [KindNeeds, List.not_mem_nil] at hmem
    | bulkCommit => simp only [KindNeeds, List.not_mem_nil] at hmem
    | activemask d => simp only [KindNeeds, List.not_mem_nil] at hmem
    | exit => simp only [KindNeeds, List.not_mem_nil] at hmem
    | ub f => simp only [KindNeeds, List.not_mem_nil] at hmem
    | mbInit m count => simp only [KindNeeds, List.not_mem_nil] at hmem
    | mbInval m => simp only [KindNeeds, List.not_mem_nil] at hmem
    | fence sem scope => simp only [KindNeeds, List.not_mem_nil] at hmem
    | fenceProxy k scope => simp only [KindNeeds, List.not_mem_nil] at hmem
    | fenceMbarInit => simp only [KindNeeds, List.not_mem_nil] at hmem
    | arrive m tx count release scope => simp only [KindNeeds, List.not_mem_nil] at hmem
    | copy s => simp only [KindNeeds, List.not_mem_nil] at hmem
    | bulkPrefetch src => simp only [KindNeeds, List.not_mem_nil] at hmem
    | asyncCommit => simp only [KindNeeds, List.not_mem_nil] at hmem
    | asyncArrive m noinc => simp only [KindNeeds, List.not_mem_nil] at hmem
    | tensorPrefetch mapAddress spec => simp only [KindNeeds, List.not_mem_nil] at hmem
    | sreg regs vals => simp only [KindNeeds, List.not_mem_nil] at hmem

/-- A source-terminal `bar.sync` can return or depend on the same actual CTA resource, or on a lane
of a record of its own barrier history. It cannot issue async work, publish an mbarrier record, or
become an unrelated collective or resource request. -/
theorem terminal_barrier_waits_cases {L : Launch} {X : Execution} {e : EvId}
    {id pc : Nat} {count : Option Nat} (hv : EffectValidity L X) (hbH : CtaBarHistoryOk L X)
    (hc : ClusterHistoryOk L X) (hp : Tmem.Pair.HistoriesOk L X)
    (he : X.IsBarrier e id count pc) (ht : e.2+1 = (X.tr e.1).length)
    {b : Bool} {v : Ref × Bool} (hw : Waits L X (.thread e,b) v) :
    b = false ∧ (v = (.thread e,true) ∨
      ∃ f b', v = (.thread f,b') ∧
        (CtaBarWaits L X e f false b' ∨ (b' = true ∧ CtaBarrier.SameRecord X e f))) := by
  obtain ⟨f, b'⟩ := v
  rcases hw with ⟨heq, hb, hb', _⟩ | ⟨hb, hb', i, j, hi, hj, hthr, hnext, hlen⟩ |
    ⟨i, j, hi, hj, hbar⟩ |
    ⟨hb, hb', i, j, hi, hj, _, n, hshfl, _⟩ |
    ⟨hb, hb', i, j, hi, hj, _, n, htc, _⟩ |
    ⟨hb, hb', hs⟩ |
    ⟨hb, hb', m, i, j, ri, rj, hri, hid, hrj, hjd, hlt⟩ |
    ⟨i, j, hi, hj, hcl⟩ |
    ⟨hb, hb', j, hf, hwit⟩ |
    ⟨hb, hb', i, j, hi, hj, _, mask, inst, hwb, _⟩ |
    ⟨hb, hb', i, j, hi, hj, a, bb, bs, cs, hw, hr, _⟩ |
    ⟨i, j, hi, hj, _, _, hsr⟩ |
    ⟨hb, hb', i, j, hi, hj, cta, hpre⟩ |
    ⟨hb, hb', i, j, hi, hj, hfs⟩ |
    ⟨hb, hb', his⟩
  · exact ⟨hb, .inl (Prod.ext heq.symm hb')⟩
  · cases hi
    rw [← hthr, ← ht] at hlen
    omega
  · cases hi
    have hb : b = false := by
      rcases hbar.2.2 with ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨hb, _⟩ <;> exact hb
    exact ⟨hb, .inr ⟨j, b', Prod.ext hj rfl, .inl (by simpa only [hb] using hbar)⟩⟩
  · cases hi
    obtain ⟨⟨p, md, a, bv, cv, recv, ok, hget⟩, -⟩ := hshfl
    rw [he] at hget
    cases hget
  · cases hi
    obtain ⟨⟨ev', hget, hbit⟩, -⟩ := htc
    rw [he] at hget
    cases hget
    simp [isTcColl] at hbit
  · rcases hs with ⟨-, hfalse, -⟩ | ⟨-, -, hse⟩
    · rw [hb] at hfalse
      cases hfalse
    · simp only [StageEdge] at hse
  · exact absurd ⟨i, j, ri, rj, hri, hid, hrj, hjd, hlt⟩
      (plain_no_object_before hv.tma he rfl m f)
  · cases hi
    rcases hc.waits_source hcl with ⟨p, op, hh⟩ | ⟨p, hh⟩ <;> rw [he] at hh <;> cases hh
  · refine ⟨hb, .inr ⟨j, b', Prod.ext hf rfl, ?_⟩⟩
    rcases ctaBar_witness_cases hbH hv hp hc he hwit with h | h
    · exact .inl (by rw [hb']; exact h)
    · exact .inr ⟨hb', h⟩
  · cases hi
    obtain ⟨p, hh⟩ := hwb
    rw [he] at hh
    cases hh
  · cases hi
    rcases hw with hw | ⟨old, hw⟩
    · obtain ⟨p, hh⟩ := hw
      rw [he] at hh
      cases hh
    · obtain ⟨p, hh⟩ := hw
      rw [he] at hh
      cases hh
  · cases hi
    obtain ⟨-, -, p, inc, n, einst, finst, hreq, -⟩ := hsr
    simp only [SetMaxNReg.Request] at hreq
    rw [he] at hreq
    cases hreq
  · cases hi
    obtain ⟨p, g, d, a, hh⟩ := hpre.actual hp
    rw [he] at hh
    cases hh
  · cases hi
    rcases hfs with ⟨w, r, a, bacc, bs, cs, se, sf, hw, -, -, hrel, -, hfence, -⟩ |
      ⟨⟨s, t, hfence, -⟩, -⟩
    · have hnot : X.MemWrites (.thread e) a bs := by
        rcases hrel with ⟨heq, -, -⟩ | ⟨sem, htf, -⟩
        · simpa only [heq] using hw
        · obtain ⟨p, hh⟩ := htf
          rw [he] at hh
          cases hh
      rcases hnot with hnot | ⟨old, hnot⟩ <;> obtain ⟨p, hh⟩ := hnot <;> rw [he] at hh <;>
        cases hh
    · obtain ⟨p, hh⟩ := hfence
      rw [he] at hh
      cases hh
  · obtain ⟨-, -, i, p, hi, -, -, hp, -⟩ := his
    cases hi
    exact absurd hp (plain_no_async hv he rfl p)

end
end PTX
