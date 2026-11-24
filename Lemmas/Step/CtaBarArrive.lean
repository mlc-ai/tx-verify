-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.CtaBarNamed
public import Lemmas.Protocol.NamedBarArrive
public import Lemmas.Step.WfInOrder

@[expose] public section

/-! # Named barrier generations with `bar.arrive` participants: appended arrivals

A proof tool for the progress layer of a kernel with `bar.arrive` (Core `BarMode.arrive`). The
library's step lemmas (`Step.CtaBar.release_append`, `NamedBar.named_finish`,
`NamedBar.wait_cases`) assume a kernel without it (`Kernel.NoBarArrive`). Here:

* Appending arrival records of either form to one CTA's history keeps a maximal execution maximal
  (`release_append_arrive`) when each appended arrival is the last event of its thread
  (`TerminalArrival`); every earlier arrival of its thread has returned and is already recorded
  (`Step.CtaBar.recorded_of_returned`), so the needs of every returned event are unchanged
  (`Step.CtaBar.ready_append`). The appended issue nodes and the returns of terminal arrivals
  are sinks (`arrive_sinkFrame`).
* **Finishing a generation** (`named_finish_arrive`): if every participant lane of a named barrier
  has made its arrival of ordinal `G`, each either recorded or the last event of its thread, and
  generation `G - 1` is released, the missing warp records complete generation `G`. A thread
  blocked at its `bar.sync` of that generation is then released (`wait_finish_arrive`).

**Why not insert.** An arrive-only participant that has moved on past an unrecorded `bar.arrive`
`a` cannot be finished this way, and not by inserting its record earlier in the history either.
Its later events can reach, in base causality, the issue of a record `r` of the same generation
already in the history (it arrives on an mbarrier that a `bar.sync` participant waits on before
its `bar.sync`). Appending `a` after `r` puts the object order `r → a` against the causal path
`a → r` (`ObjectCoherent`). An execution with `a` inserted before `r` does not extend the old one
(`Execution.le` keeps each history as a prefix), so maximality does not transfer to it; and no
extension of the old execution records `a`, so `r`'s thread is never released. Such an execution
can be maximal and not complete. Core's dependency axiom excludes it: a `bar.arrive` followed by
another event of its thread has returned, so its warp needs name its record (`DependencyOk.ready`,
`ctaBarWarpNeeds`), and every arrival is recorded or terminal (`recorded_or_last`), which is what
the lemmas here need. -/

namespace PTX
open AsyncCopy
noncomputable section

/-- A CTA barrier arrival of either form that is the last event of its thread. -/
def TerminalArrival (X : Execution) (e : EvId) : Prop :=
  (∃ id count pc m, X.get e = some ⟨pc, .bar id count m⟩) ∧ e.2 + 1 = (X.tr e.1).length

/-- A terminal `bar.sync` is a terminal arrival. -/
theorem TerminalBar.arrival {X : Execution} {e : EvId} (h : TerminalBar X e) :
    TerminalArrival X e := by
  obtain ⟨⟨id, count, pc, hI⟩, ht⟩ := h
  exact ⟨⟨id, count, pc, .sync, hI⟩, ht⟩

/-- A CTA barrier arrival of either form issues no asynchronous operation: each stage names its
issue event, of an issuing kind. -/
theorem arrival_no_async {L : Launch} {X : Execution} (hv : EffectValidity L X) {i : EvId}
    {pc id : Nat} {cnt : Option Nat} {m : BarMode} (hi : X.get i = some ⟨pc, .bar id cnt m⟩)
    (p : Part) : ¬ X.AsyncPresent i p := by
  have ht := hv.tma
  have copyNo (hn : nonempty (X.async.copies i)) : False := by
    obtain ⟨s, hs, _⟩ := ht.1 i hn
    simp [issuedBy, hi] at hs
  have mmaNo (hs : X.async.mmaStarted i = true) : False := by
    rcases ht.2.1.1 i hs with
      ⟨d, spec, accum, mask, operands, ⟨pc', hm⟩, _⟩ | ⟨c, operands, ⟨pc', hm⟩, _⟩ |
      ⟨s, operands, ⟨pc', hm⟩, _⟩ <;> rw [hi] at hm <;> cases hm
  have tensorNo {o : TensorCopy.Observation} (ho : X.tensor i = some o) : False := by
    obtain ⟨addr, pc', hp⟩ := (hv.tensor i o ho).1
    rw [hi] at hp; cases hp
  have storeNo {o : TensorStore.Observation} (ho : X.tensorStores i = some o) : False := by
    obtain ⟨addr, pc', hp⟩ := (hv.store i o ho).1
    rw [hi] at hp; cases hp
  have clcNo (hn : (X.clc i).resolved.isSome ∨ (X.clc i).written.Nonempty ∨
      (X.clc i).notified.Nonempty) : False := by
    obtain ⟨s, targets, pc', hp⟩ := hv.clc.2.2.1 i hn
    rw [hi] at hp; cases hp
  intro hp
  cases p with
  | readCopy => exact copyNo ⟨.read .copy, hp⟩
  | writeCopy => exact copyNo ⟨.write .copy, hp⟩
  | notifyCopy => exact copyNo ⟨.notify .copy, hp⟩
  | writeElem j => exact copyNo ⟨.write (.elem j), hp⟩
  | oldElem j => exact copyNo ⟨.old (.elem j), hp⟩
  | mmaDone => exact mmaNo (ht.2.1.2 i hp)
  | readLoad x y k | notifyLoad => obtain ⟨o, ho, _⟩ := hp; exact tensorNo ho
  | writeLoad x y k => obtain ⟨o, slot, value, ho, _⟩ := hp; exact tensorNo ho
  | readStore x y k | writeStore x y k | oldStore x y k | readsDone | fullDone =>
    obtain ⟨o, ho, _⟩ := hp; exact storeNo ho
  | readCta | readElem j | oldCopy | oldLoad | oldCta | readPrefetch | writePrefetch |
      oldPrefetch => exact hp.elim
  | resolve => exact clcNo (.inl hp)
  | writeCta c => exact clcNo (.inr (.inl ⟨c, hp⟩))
  | notifyCta c => exact clcNo (.inr (.inr ⟨c, hp⟩))
  | tcNotify r =>
    obtain ⟨⟨s, m', ⟨pc', hp'⟩, _⟩, _⟩ := hv.tcCommit i r hp
    rw [hi] at hp'; cases hp'
  | mmaRead b k =>
    obtain ⟨l, byte, hf, -⟩ := hp
    rcases hf with ⟨_, _, _, _, ⟨pc', hm⟩, _⟩ | ⟨_, _, _, ⟨pc', hm⟩, _, _, _, _⟩ <;>
      rw [hi] at hm <;> cases hm
  | arriveOn =>
    obtain ⟨⟨m', noinc, pc', hp'⟩, _⟩ := ht.2.2.2 i hp
    rw [hi] at hp'; cases hp'

/-- A CTA barrier arrival of either form is in no mbarrier history. -/
theorem arrival_no_object_before {X : Execution} (ht : TmaOk X) {i : EvId} {pc id : Nat}
    {cnt : Option Nat} {m : BarMode} (hi : X.get i = some ⟨pc, .bar id cnt m⟩) (o : Loc)
    (f : Ref) : ¬ MBarrier.Before (X.objects o) (.thread i) f := by
  rintro ⟨a, b, ra, rb, ha, hid, _⟩
  have ho := ((ht.2.2.1 o).2.1 ra (List.mem_of_getElem? ha)).1
  rw [hid] at ho
  simp [objectAction, hi] at ho

/-! The witness and waiting cases of a CTA barrier arrival of either form. They are the
statements of `ctaBar_witness_cases` and `terminal_barrier_waits_cases`
(`Lemmas/MBarrier/BarrierWaitingSources.lean`) for an arrival of any mode; the proofs use the
event's kind only to tell it apart from the other kinds. -/

section
open CtaBarrier

/-- A lane of a warp need of a `bar` event is a lane of the event's own record, unless it is an
exit record's event. -/
theorem warpNeed_record_arrival {L : Launch} {X : Execution} {e j : EvId} {pc id : Nat}
    {count : Option Nat} {md : BarMode} {fills : AsyncCopy.Ref → Prop}
    (hb : CtaBarHistoryOk L X)
    (he : X.get e = some ⟨pc, .bar id count md⟩)
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

/-- A record counted by the release that a `bar.sync` waits for makes its lane, an arrival of
either form, an arrival of the
waited generation. -/
theorem counted_waits_arrival {L : Launch} {X : Execution} {e j : EvId} {pc id : Nat}
    {count : Option Nat} {md : BarMode} (hb : CtaBarHistoryOk L X)
    (he : X.get e = some ⟨pc, .bar id count md⟩) (hcc : CtaBarCounted L X j e) :
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


/-- A masked warp collective's wait is no CTA barrier arrival: its source is an event of the
class. -/
theorem maskWait_not_arrival {Q V : Type} {L : Launch} {X : Execution} {e j : EvId} {pc id : Nat}
    {count : Option Nat} {md : BarMode} {c : Kind → Option (WarpPart Q V)}
    (he : X.get e = some ⟨pc, .bar id count md⟩) (hnone : c (.bar id count md) = none)
    (hmw : MaskWait L c X e j) : False := by
  rcases MaskWait.src (L := L) hmw with ⟨pc', k, q, hget, hc⟩ | ⟨pc', hget⟩
  · rw [he] at hget
    cases hget
    rw [hnone] at hc
    cases hc
  · rw [he] at hget
    cases hget

/-- A warp-collective `tcgen05` event is no CTA barrier arrival. -/
theorem tcK_not_arrival {X : Execution} {e : EvId} {pc id : Nat}
    {count : Option Nat} {md : BarMode} {n : Nat}
    (he : X.get e = some ⟨pc, .bar id count md⟩) (htk : X.TcK e n) : False := by
  obtain ⟨⟨ev', hget, hbit⟩, -⟩ := htk
  rw [he] at hget
  cases hget
  simp [isTcColl] at hbit

/-- A CTA barrier arrival of either form that fills a need of `j` is either an arrival of the
generation whose release `j` waits for, or a lane of a record of `j`'s own barrier history. -/
theorem ctaBarArrival_witness_cases {L : Launch} {X : Execution} {e j : EvId} {pc id : Nat}
    {count : Option Nat} {md : BarMode} (hb : CtaBarHistoryOk L X) (hv : EffectValidity L X)
    (hp : Tmem.Pair.HistoriesOk L X) (hc : ClusterHistoryOk L X)
    (he : X.get e = some ⟨pc, .bar id count md⟩)
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
        · exact .inr (warpNeed_record_arrival hb he hwarp hfill)
        · cases hcond
        · obtain ⟨y, hy, hcy⟩ := List.mem_flatMap.mp hcount
          by_cases hcc : CtaBarCounted L X j y
          · simp only [needsIf, hcc, ite_true, List.mem_singleton, Need.node.injEq] at hcy
            rw [hcy] at hfill
            cases hfill
            exact .inl (counted_waits_arrival hb he hcc)
          · simp only [needsIf, hcc, ite_false, List.not_mem_nil] at hcy
      | arrive =>
        simp only [KindNeeds, ctaBarNeeds, List.mem_append] at hmem
        rcases hmem with hwarp | hempty
        · exact .inr (warpNeed_record_arrival hb he hwarp hfill)
        · cases hempty
    | shfl mode a b c recv ok =>
      simp only [KindNeeds, maskNeeds, hg, shflClass] at hmem
      obtain ⟨l, -, hfl⟩ := List.mem_map.mp hmem
      cases hfl
      obtain ⟨j', heq, hmw⟩ := hfill
      cases heq
      exact absurd hmw (maskWait_not_arrival he rfl)
    | vote mask a ballot =>
      simp only [KindNeeds, maskNeeds, hg, voteClass] at hmem
      obtain ⟨l, -, hfl⟩ := List.mem_map.mp hmem
      cases hfl
      obtain ⟨j', heq, hmw⟩ := hfill
      cases heq
      exact absurd hmw (maskWait_not_arrival he rfl)
    | voteMode mode mask a d =>
      simp only [KindNeeds, maskNeeds, hg, voteClass] at hmem
      obtain ⟨l, -, hfl⟩ := List.mem_map.mp hmem
      cases hfl
      obtain ⟨j', heq, hmw⟩ := hfill
      cases heq
      exact absurd hmw (maskWait_not_arrival he rfl)
    | redux op signed mask a d =>
      simp only [KindNeeds, maskNeeds, hg, reduxClass] at hmem
      obtain ⟨l, -, hfl⟩ := List.mem_map.mp hmem
      cases hfl
      obtain ⟨j', heq, hmw⟩ := hfill
      cases heq
      exact absurd hmw (maskWait_not_arrival he rfl)
    | match_ all wide mask a d p =>
      simp only [KindNeeds, maskNeeds, hg, matchClass] at hmem
      obtain ⟨l, -, hfl⟩ := List.mem_map.mp hmem
      cases hfl
      obtain ⟨j', heq, hmw⟩ := hfill
      cases heq
      exact absurd hmw (maskWait_not_arrival he rfl)
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
          exact absurd htk (tcK_not_arrival he)
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
        exact absurd htk (tcK_not_arrival he)
      | st a vals shape =>
        simp only [KindNeeds, tcNeeds, List.mem_map] at hmem
        obtain ⟨h, -, hfl⟩ := hmem
        cases hfl
        obtain ⟨j', heq, htk⟩ := hfill
        cases heq
        exact absurd htk (tcK_not_arrival he)
      | waitLd =>
        simp only [KindNeeds, tcNeeds, List.mem_map] at hmem
        obtain ⟨h, -, hfl⟩ := hmem
        cases hfl
        obtain ⟨j', heq, htk⟩ := hfill
        cases heq
        exact absurd htk (tcK_not_arrival he)
      | waitSt =>
        simp only [KindNeeds, tcNeeds, List.mem_map] at hmem
        obtain ⟨h, -, hfl⟩ := hmem
        cases hfl
        obtain ⟨j', heq, htk⟩ := hfill
        cases heq
        exact absurd htk (tcK_not_arrival he)
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

/-- A source-terminal CTA barrier arrival of either form can return or depend on the same actual
CTA resource, or on a lane of a record of its own barrier history. It cannot issue async work,
publish an mbarrier record, or become an unrelated collective or resource request. -/
theorem terminal_arrival_waits_cases {L : Launch} {X : Execution} {e : EvId}
    {id pc : Nat} {count : Option Nat} {md : BarMode} (hv : EffectValidity L X)
    (hbH : CtaBarHistoryOk L X)
    (hc : ClusterHistoryOk L X) (hp : Tmem.Pair.HistoriesOk L X)
    (he : X.get e = some ⟨pc, .bar id count md⟩) (ht : e.2+1 = (X.tr e.1).length)
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
      (arrival_no_object_before hv.tma he m f)
  · cases hi
    rcases hc.waits_source hcl with ⟨p, op, hh⟩ | ⟨p, hh⟩ <;> rw [he] at hh <;> cases hh
  · refine ⟨hb, .inr ⟨j, b', Prod.ext hf rfl, ?_⟩⟩
    rcases ctaBarArrival_witness_cases hbH hv hp hc he hwit with h | h
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
    exact absurd hp (arrival_no_async hv he p)

end

/-- **An arrival is recorded or the last event of its thread.** -/
theorem recorded_or_last {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) {e : EvId}
    {pc id : Nat} {cnt : Option Nat} {m : BarMode} (he : X.get e = some ⟨pc, .bar id cnt m⟩) :
    e ∈ (X.barriers (e.1 / L.block)).flatMap CtaBarrier.Record.refs ∨
      e.2 + 1 = (X.tr e.1).length := by
  have hl := len_of_get he
  by_cases hlt : e.2 + 1 < (X.tr e.1).length
  · obtain ⟨i, r, hi, her⟩ := Step.CtaBar.recorded_of_returned hX he hlt
    exact .inl (List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hi, her⟩)
  · exact .inr (by omega)

namespace Step.CtaBar

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The nodes added by appending arrivals that are last events: the issue nodes of the suffix and
the return nodes of terminal arrivals. -/
def ArriveNode (X : Execution) (suffix : List (CtaBarrier.Record EvId))
    (p : Ref × Bool) : Prop :=
  (∃ e, p = (.thread e, true) ∧ TerminalArrival X e) ∨
    (∃ e, p = (.thread e, false) ∧ e ∈ suffix.flatMap CtaBarrier.Record.refs)

/-- Appending a checked suffix of terminal arrivals of either form extends the execution by the
suffix nodes: no waiting dependency leaves them, the rank orders issue nodes by record position
and puts every return node above them, and outside them every relation is one of `X`. -/
theorem arrive_sinkFrame (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {suffix : List (CtaBarrier.Record EvId)}
    (hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    (hterm : ∀ e ∈ suffix.flatMap CtaBarrier.Record.refs, e.2 + 1 = (X.tr e.1).length) :
    SinkFrame L K A X (X.withCtaHistory c (X.barriers c ++ suffix)) (ArriveNode X suffix) := by
  have hYE : EffectValidity L (X.withCtaHistory c (X.barriers c ++ suffix)) :=
    effectValidity_withCtaHistory_legacy hX
  refine ctaHistory_append_prim hX hh _ (fun j hj => .inr ⟨j, rfl, hj⟩)
    ⟨rankOf ((X.barriers c ++ suffix).flatMap CtaBarrier.Record.refs), ?_⟩ ?_
    (dep_append hX hh _ fun j pc id cnt m hev hlast =>
      .inl ⟨j, rfl, ⟨id, cnt, pc, m, hev⟩, hlast⟩)
  · intro u v hw hu
    obtain ⟨ue, ub⟩ := u
    obtain ⟨ve, vb⟩ := v
    rcases hu with ⟨e, hue, hT⟩ | ⟨e, hue, he⟩
    · -- a return node: it has no successor
      simp only [Prod.mk.injEq] at hue
      obtain ⟨rfl, rfl⟩ := hue
      obtain ⟨⟨id, count, pc, m, hI⟩, ht⟩ := hT
      have h0 := (terminal_arrival_waits_cases (X := X.withCtaHistory c (X.barriers c ++ suffix))
        hYE hh hX.cluster hX.tmemPair hI ht hw).1
      exact absurd h0 (by decide)
    · -- an issue node of the suffix
      simp only [Prod.mk.injEq] at hue
      obtain ⟨rfl, rfl⟩ := hue
      obtain ⟨r, hr, her⟩ := List.mem_flatMap.mp he
      obtain ⟨hec, ⟨id, count, pc, m, hI⟩, hfresh⟩ := suffix_ref_facts hc hsuf hh hr her
      have ht := hterm e he
      have hT : TerminalArrival X e := ⟨⟨id, count, pc, m, hI⟩, ht⟩
      have hmem : e ∈ (X.barriers c ++ suffix).flatMap CtaBarrier.Record.refs :=
        List.mem_flatMap.mpr ⟨r, List.mem_append_right _ hr, her⟩
      have hlen := List.idxOf_lt_length_iff.mpr hmem
      rcases (terminal_arrival_waits_cases (X := X.withCtaHistory c (X.barriers c ++ suffix))
          hYE hh hX.cluster hX.tmemPair hI ht hw).2 with
        h | ⟨f, b', h, hcw | ⟨hb', d, i, q, hq, heq, hfq⟩⟩
      · -- the return node of the same arrival
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨Or.inl ⟨e, rfl, hT⟩, ?_⟩
        simp only [rankOf]
        omega
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases ctaWaits_forward hX hc hsuf hh he hcw with ⟨hb', hfS, hidx⟩ | ⟨hb', hfT⟩
        · subst hb'
          refine ⟨Or.inr ⟨f, rfl, hfS⟩, ?_⟩
          simp only [rankOf]
          exact hidx
        · subst hb'
          refine ⟨Or.inl ⟨f, rfl, hfT.arrival⟩, ?_⟩
          simp only [rankOf]
          omega
      · -- a lane of the same record: the record is appended, so the lane is terminal
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hb'
        have hdc : d = c := (hh.ref_cta (List.mem_of_getElem? hq) heq).symm.trans hec
        subst hdc
        rw [withCtaHistory_barriers_self] at hq
        have hge : (X.barriers d).length ≤ i := by
          by_contra hlt
          rw [List.getElem?_append_left (by omega)] at hq
          exact hfresh (List.mem_flatMap.mpr ⟨q, List.mem_of_getElem? hq, heq⟩)
        rw [List.getElem?_append_right hge] at hq
        have hqs := List.mem_of_getElem? hq
        have hfS : f ∈ suffix.flatMap CtaBarrier.Record.refs := List.mem_flatMap.mpr ⟨q, hqs, hfq⟩
        obtain ⟨-, ⟨idf, countf, pcf, mf, hIf⟩, -⟩ := suffix_ref_facts hc hsuf hh hqs hfq
        refine ⟨Or.inl ⟨f, rfl, ⟨idf, countf, pcf, mf, hIf⟩, hterm f hfS⟩, ?_⟩
        simp only [rankOf]
        omega
  · rintro m i p y hb (⟨e, he, -⟩ | ⟨e, he, hm⟩)
    · cases he
    · cases he
      obtain ⟨r, hr, her⟩ := List.mem_flatMap.mp hm
      obtain ⟨-, ⟨id, count, pc, mode, hI⟩, -⟩ := suffix_ref_facts hc hsuf hh hr her
      exact (sync_no_async_before hX.tma hI (.inl ⟨_, _, _, rfl⟩) m p y hb).elim

/-- Appending a checked suffix of terminal arrivals of either form keeps the execution
consistent. -/
theorem arrive_consistent (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {suffix : List (CtaBarrier.Record EvId)}
    (hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.withCtaHistory c (X.barriers c ++ suffix)))
    (hterm : ∀ e ∈ suffix.flatMap CtaBarrier.Record.refs, e.2 + 1 = (X.tr e.1).length) :
    Consistent L K A mem0 (X.withCtaHistory c (X.barriers c ++ suffix)) := by
  have hp : X.barriers c <+: X.barriers c ++ suffix := ⟨suffix, rfl⟩
  have hle : X.le (X.withCtaHistory c (X.barriers c ++ suffix)) :=
    X.le_withCtaHistory c hp
  have hbo := baseCausality_withCtaHistory_iff hX hp hh
  have horder := (arrive_sinkFrame hX hc hsuf hh hterm).orderOk hX.orderOk
  apply consistent_preserving_extension hX hle
  · exact hX.thr
  · exact hX.outside
  · intro e a bs he; exact he
  · intro e a bs he; exact he
  · intro e a bs he; exact he
  · intros; rfl
  · intro l e f _; exact modelCausality_withCtaHistory hbo
  · exact ready_append hX hh
  · exact hX.shfl
  · exact horder
  · exact hasm
  · exact hX.tma
  · rfl
  · exact withCtaHistory_obligations hX hp hh hbo

/-- **Appending terminal arrivals of either form.** The extended execution is consistent, extends
the old one at the same size, and a maximal execution stays maximal. -/
theorem release_append_arrive (hmax : Maximal L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {suffix : List (CtaBarrier.Record EvId)}
    (hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes)
    (hh : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.withCtaHistory c (X.barriers c ++ suffix)))
    (hterm : ∀ e ∈ suffix.flatMap CtaBarrier.Record.refs, e.2 + 1 = (X.tr e.1).length) :
    Consistent L K A mem0 (X.withCtaHistory c (X.barriers c ++ suffix)) ∧
      X.le (X.withCtaHistory c (X.barriers c ++ suffix)) ∧
      (X.withCtaHistory c (X.barriers c ++ suffix)).size L = X.size L ∧
      Maximal L K A mem0 (X.withCtaHistory c (X.barriers c ++ suffix)) := by
  have hY := arrive_consistent hmax.1 hc hsuf hh hasm hterm
  have hle : X.le (X.withCtaHistory c (X.barriers c ++ suffix)) :=
    X.le_withCtaHistory c ⟨suffix, rfl⟩
  have hsz : (X.withCtaHistory c (X.barriers c ++ suffix)).size L = X.size L := rfl
  refine ⟨hY, hle, hsz, hY, fun Z hZ hYZ => ?_⟩
  have h1 := hmax.2 Z hZ (Execution.le_trans hle hYZ)
  omega

end Step.CtaBar

namespace NamedBar
open CtaBarrier

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **Finishing a generation whose participants have all arrived, either form.** In a maximal
execution, let every participant lane of CTA `c` (named barrier `id`, group `p`, sources `hS`, no
participant exit) have made its arrival of ordinal `G`, recorded or the last event of its thread,
and let generation `G - 1` be released. Then the records of the participant warps that have none
complete generation `G`: the extended execution is maximal, with the same traces and size. -/
theorem named_finish_arrive (hmax : Maximal L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {count : Option Nat} {p : Finset Nat} {id : Nat} (hG : Shape L count p id)
    (hS : Sources L X count p id)
    (hno : ∀ y, y / L.block = c → (y % L.block) / 32 ∈ p → ∀ j pc,
      X.get (y, j) ≠ some ⟨pc, .exit⟩)
    {G : Nat} (hpred : 0 < G → Released L.block (X.barriers c) id (G - 1))
    (hlane : ∀ g, g < L.block → g / 32 ∈ p → ∃ j pc m,
      X.get (c * L.block + g, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (c * L.block + g)).take j).countP (Execution.isBarId id) = G ∧
      ((c * L.block + g, j) ∈ (X.barriers c).flatMap Record.refs ∨
        j + 1 = (X.tr (c * L.block + g)).length))
    {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A) :
    ∃ Y, Maximal L K A mem0 Y ∧ X.le Y ∧ Y.size L = X.size L ∧ Y.tr = X.tr ∧
      CtaBarDone L Y c (id + 16 * G) := by
  have hX := hmax.1
  obtain ⟨w0, hw0⟩ : ∃ w, w ∈ p := Finset.card_pos.mp hG.pos
  have hb : 0 < L.block := by
    have := hG.bound w0 hw0
    omega
  have hid := hG.id_lt
  have hmodid : (id + 16 * G) % 16 = id := by omega
  have hdivid : (id + 16 * G) / 16 = G := by omega
  have hdone_iff : ∀ Y : Execution, CtaBarDone L Y c (id + 16 * G) ↔
      Released L.block (Y.barriers c) id G := by
    intro Y
    unfold CtaBarDone
    rw [hmodid, hdivid]
  by_cases hrel : Released L.block (X.barriers c) id G
  · exact ⟨X, hmax, Execution.le_refl X, rfl, rfl, (hdone_iff X).mpr hrel⟩
  have hPx := (Sources.part hX hS hno).exits hX hc hb
  obtain ⟨s, hs⟩ := (hX.ctaBar.2 c hc).2.2
  have hl := (hS.protocol hX hc).run_ledger hG.pos hG.target rfl hG.bound hs
  have hprot := run_protected hPx hs
  have hgs_le : (s.slots id).generation ≤ G := by
    by_contra hlt
    push Not at hlt
    exact hrel (Step.CtaBar.released_of_generation_lt hs hlt)
  have hgs_ge : G ≤ (s.slots id).generation := by
    rcases Nat.eq_zero_or_pos G with h0 | hpos
    · omega
    · have := released_generation_lt hs (hpred hpos)
      omega
  have hgs : (s.slots id).generation = G := le_antisymm hgs_le hgs_ge
  -- an arrival of ordinal `G` of a lane of a warp that has not arrived is in no record
  have hnew : ∀ w ∈ p, w ∉ (s.slots id).arrived → ∀ g, g < L.block → g / 32 = w →
      ∀ j pcg mg, X.get (c * L.block + g, j) = some ⟨pcg, .bar id count mg⟩ →
      ((X.tr (c * L.block + g)).take j).countP (Execution.isBarId id) = G →
      (c * L.block + g, j) ∉ (X.barriers c).flatMap Record.refs := by
    intro w hwp hwA g hg hgw j pcg mg hbarg hordg hmem
    obtain ⟨r, hr, hgr⟩ := List.mem_flatMap.mp hmem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨last, hlast⟩ := (hX.ctaBar.2 c hc).2.2
    obtain ⟨si, ti, hat, hpf⟩ := run_at_record hlast hi
    have hsrc := (hX.ctaBar.2 c hc).2.1 r hr
    cases r with
    | exit g' e' =>
      obtain ⟨-, -, pc, hget⟩ := hsrc
      have he : (c * L.block + g, j) = e' := by simpa [Record.refs] using hgr
      rw [← he, hbarg] at hget
      cases hget
    | arrival id' w' cnt' lanes =>
      obtain ⟨⟨g1, f1⟩, hm, hf1⟩ := List.mem_map.mp hgr
      obtain ⟨hg1, hfg1, pc1, m1, hbar1⟩ := hsrc (g1, f1) hm
      have hf1e : f1 = (c * L.block + g, j) := hf1
      subst hf1e
      have hgg : g1 = g := by
        have : c * L.block + g = c * L.block + g1 := hfg1
        omega
      subst hgg
      rw [hbarg] at hbar1
      simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at hbar1
      obtain ⟨-, rfl, -⟩ := hbar1
      have hwarp := ((perform_arrival_lanes hpf).2.1 (g1, _) hm).2.1
      simp only at hwarp
      have hwexit : g1 ∉ si.exited :=
        run_protected (fun g a ha => hPx g a (List.mem_of_mem_take ha)) hat g1 hg
          (hgw ▸ hwp)
      have hcount := cta_prefix_id_arrival_count hX (c := c) (i := i) (localg := g1) (id := id)
        hc hi hgr hat hg rfl hwexit rfl
      simp only at hcount
      rw [hordg] at hcount
      have hge : G + 1 ≤ idArrivals (X.barriers c) id w := by
        have hr' : (X.barriers c)[i]? = some (Record.arrival id w' cnt' lanes) := hi
        have hsub : (X.barriers c).take (i + 1) =
            (X.barriers c).take i ++ [Record.arrival id w' cnt' lanes] := by
          rw [List.take_add_one, hr']
          rfl
        have hww : w' = w := by omega
        subst hww
        have h1 : idArrivals ((X.barriers c).take (i + 1)) id w' = G + 1 := by
          unfold idArrivals at hcount ⊢
          rw [hsub, List.countP_append, ← hgw, hcount]
          simp [isWarpIdArrival]
        have h2 := (List.take_sublist (i + 1) (X.barriers c)).countP_le
          (p := isWarpIdArrival id w')
        unfold idArrivals
        unfold idArrivals at h1
        omega
      have hbal := hl.balance w hwp (lane_live hG.bound hprot hwp)
      simp only [hwA, ↓reduceIte, Nat.add_zero] at hbal
      omega
  -- so the arrival of such a lane is the last event of its thread
  have hterm_lane : ∀ w ∈ p, w ∉ (s.slots id).arrived → ∀ g, g < L.block → g / 32 = w →
      ∃ pc m, X.get (c * L.block + g, (X.tr (c * L.block + g)).length - 1) =
        some ⟨pc, .bar id count m⟩ ∧
        ((X.tr (c * L.block + g)).take ((X.tr (c * L.block + g)).length - 1)).countP
          (Execution.isBarId id) = G ∧ 0 < (X.tr (c * L.block + g)).length := by
    intro w hwp hwA g hg hgw
    obtain ⟨j, pc, m, hget, hord, hrec | hlast⟩ := hlane g hg (hgw ▸ hwp)
    · exact absurd hrec (hnew w hwp hwA g hg hgw j pc m hget hord)
    · have hj : (X.tr (c * L.block + g)).length - 1 = j := by omega
      rw [hj]
      exact ⟨pc, m, hget, hord, by omega⟩
  -- the missing participant warps arrive, completing the generation
  let event : Nat → EvId := fun g => (c * L.block + g, (X.tr (c * L.block + g)).length - 1)
  obtain ⟨ws, t, hnd, hws, hcov, hrun, hgen⟩ :=
    finish_named hid hG.pos hG.target rfl hG.bound event _ hl hprot rfl
  let suffix : List (Record EvId) :=
    ws.map (fun w => Record.arrival id w count (fullLanes L.block w event))
  have hsuf : ∀ r ∈ suffix, ∃ id warp count lanes, r = .arrival id warp count lanes := by
    intro r hr
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
    exact ⟨_, _, _, _, rfl⟩
  have hsufref : ∀ f ∈ suffix.flatMap Record.refs, ∃ w ∈ ws, ∃ g, g < L.block ∧ g / 32 = w ∧
      f = event g := by
    intro f hf
    obtain ⟨r, hr, hfr⟩ := List.mem_flatMap.mp hf
    obtain ⟨w, hwws, rfl⟩ := List.mem_map.mp hr
    simp only [Record.refs, List.mem_map] at hfr
    obtain ⟨q, hq, rfl⟩ := hfr
    obtain ⟨hg, hw, heq⟩ := mem_fullLanes.mp hq
    exact ⟨w, hwws, q.1, hg, hw, heq⟩
  have hinj : Function.Injective event := by
    intro g h hh
    have := congrArg Prod.fst hh
    simp only [event] at this
    omega
  have hhist : CtaBarHistoryOk L (X.withCtaHistory c (X.barriers c ++ suffix)) := by
    constructor
    · intro d hd
      have hne : d ≠ c := by omega
      rw [withCtaHistory_barriers_ne X _ hne]
      exact hX.ctaBar.1 d hd
    · intro d hd
      by_cases hdc : d = c
      · subst hdc
        rw [withCtaHistory_barriers_self]
        refine ⟨?_, ?_, t, ?_⟩
        · rw [List.flatMap_append]
          refine List.nodup_append.mpr ⟨(hX.ctaBar.2 d hc).1, ?_, ?_⟩
          · have h := fullLanes_suffix_nodup (id := id) (block := L.block) (event := event) hnd hinj
            simpa [suffix, List.flatMap_map, Record.refs] using h
          · intro e he f hf hef
            subst hef
            obtain ⟨w, hwws, g, hg, hgw, rfl⟩ := hsufref e hf
            have hw := hws w hwws
            obtain ⟨pc, m, hget, hord, -⟩ := hterm_lane w hw.1 hw.2 g hg hgw
            exact hnew w hw.1 hw.2 g hg hgw _ pc m hget hord he
        · intro r hr'
          rcases List.mem_append.mp hr' with hr | hr
          · exact (hX.ctaBar.2 d hc).2.1 r hr
          · obtain ⟨w, hwws, rfl⟩ := List.mem_map.mp hr
            intro q hq
            obtain ⟨hg, hw, heq⟩ := mem_fullLanes.mp hq
            obtain ⟨pc, m, hbar, -⟩ :=
              hterm_lane w (hws w hwws).1 (hws w hwws).2 q.1 hg hw
            refine ⟨hg, by rw [heq], pc, m, ?_⟩
            rw [heq]
            exact hbar
        · rw [run_append, hs]
          exact hrun
      · rw [withCtaHistory_barriers_ne X _ hdc]
        exact hX.ctaBar.2 d hd
  have hterm : ∀ e ∈ suffix.flatMap Record.refs, e.2 + 1 = (X.tr e.1).length := by
    intro e he
    obtain ⟨w, hwws, g, hg, hgw, rfl⟩ := hsufref e he
    obtain ⟨-, -, -, -, hpos⟩ := hterm_lane w (hws w hwws).1 (hws w hwws).2 g hg hgw
    simp only [event]
    omega
  obtain ⟨-, hle, hsz, hmaxY⟩ := Step.CtaBar.release_append_arrive hmax hc hsuf hhist
    (hA X _ hX (X.le_withCtaHistory c ⟨suffix, rfl⟩) (Execution.notifiedInOrder_of_eq rfl)
      (Execution.noNewRead_of_tr rfl))
    hterm
  have hrec : Released L.block (X.barriers c ++ suffix) id G := by
    have := released_of_arrival_run_cnt (xs := X.barriers c) (ys := suffix) (s := s) (t := t)
      (id := id) (cnt := count) (fun r hr => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
        exact ⟨w, _, rfl⟩) hs hrun (by omega)
    rwa [hgs] at this
  have hYb : (X.withCtaHistory c (X.barriers c ++ suffix)).barriers c = X.barriers c ++ suffix :=
    withCtaHistory_barriers_self X c _
  exact ⟨_, hmaxY, hle, hsz, rfl, (hdone_iff _).mpr (by rw [hYb]; exact hrec)⟩

/-- **A thread blocked at a `bar.sync` whose generation lacks only arrivals that already happened
can be released.** In a maximal execution, let thread `g`'s last event be its `bar.sync` on named
barrier `id`, of ordinal `G`. If every participant lane of its CTA has made its arrival of ordinal
`G`, recorded or the last event of its thread, and generation `G - 1` is released, then a maximal
execution with the same traces releases `g`. -/
theorem wait_finish_arrive (hmax : Maximal L K A mem0 X) {sel : Nat → Bool}
    (hA : Assumption.WfStep sel L K mem0 A)
    {count : Option Nat} {p : Finset Nat} {id : Nat} (hG : Shape L count p id)
    (hS : Sources L X count p id) {g pc : Nat} (hg : g < L.threads)
    (hno : ∀ y, y / L.block = g / L.block → (y % L.block) / 32 ∈ p → ∀ j pc,
      X.get (y, j) ≠ some ⟨pc, .exit⟩)
    (hlast : X.IsBarrier (g, (X.tr g).length - 1) id count pc) {G : Nat}
    (hord : ((X.tr g).take ((X.tr g).length - 1)).countP (Execution.isBarId id) = G)
    (hpred : 0 < G → Released L.block (X.barriers (g / L.block)) id (G - 1))
    (hlane : ∀ y, y < L.block → y / 32 ∈ p → ∃ j pc m,
      X.get (g / L.block * L.block + y, j) = some ⟨pc, .bar id count m⟩ ∧
      ((X.tr (g / L.block * L.block + y)).take j).countP (Execution.isBarId id) = G ∧
      ((g / L.block * L.block + y, j) ∈ (X.barriers (g / L.block)).flatMap Record.refs ∨
        j + 1 = (X.tr (g / L.block * L.block + y)).length)) :
    ∃ Y, Maximal L K A mem0 Y ∧ Y.tr = X.tr ∧ Step.Released L Y g := by
  obtain ⟨Y, hmaxY, -, -, hYtr, hdone⟩ :=
    named_finish_arrive hmax (cta_lt hg) hG hS hno hpred hlane hA
  have hget : ∀ e, Y.get e = X.get e := fun e => by simp only [Execution.get, hYtr]
  have hSY : Sources L Y count p id := fun e pc cnt ⟨m, he⟩ hgt =>
    hS e pc cnt ⟨m, (hget e) ▸ he⟩ hgt
  have hlastY : Y.get (g, (X.tr g).length - 1) = some ⟨pc, .bar id count .sync⟩ := by
    rw [hget]
    exact hlast
  have hid := hG.id_lt
  have hd : Released L.block (Y.barriers (g / L.block)) id G := by
    unfold CtaBarDone at hdone
    rwa [show (id + 16 * G) % 16 = id by omega, show (id + 16 * G) / 16 = G by omega] at hdone
  have hk := hSY.key_of_released hmaxY.1 hG hlastY hg (by
    simp only [hYtr]
    rw [hord]
    exact hd)
  simp only [hYtr, hord] at hk
  have hk' : CtaBarArrivalK L Y (g, (X.tr g).length - 1) (id + 16 * G) := hk
  have hmod : (id + 16 * G) % 16 = id := by omega
  have hkey : CtaBarK L Y (g, (X.tr g).length - 1) (id + 16 * G) :=
    ⟨hk'.1, ⟨count, pc, by rw [hmod]; exact hlastY⟩, hk'.2.2⟩
  exact ⟨Y, hmaxY, hYtr, released_of_key hmaxY.1.ctaBar hYtr hlast hkey hdone⟩

end NamedBar

end
end PTX
