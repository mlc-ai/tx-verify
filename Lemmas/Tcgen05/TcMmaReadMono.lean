-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.Tcgen05.TcMmaRead
public import Lemmas.Tcgen05.TcMmaValue
public import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! Load-read sources of an extended execution restrict to the original one when the
extension preserves causality into old events, old completion observations, recorded
operand values and allocation coverage. Then the values of old loads stay constrained
exactly as before, and only new loads carry new obligations. -/
namespace PTX.TcMma
noncomputable section

/-- An extension that adds no new evidence about old events. -/
structure ReadPreserved (L : Launch) (X Y : Execution) : Prop where
  le : X.le Y
  hb : ∀ {x f : EvId}, f.2 < (X.tr f.1).length → (baseCausality L Y x f ↔ baseCausality L X x f)
  observes : ∀ {x w : EvId} {acq : Bool} {ws : MbarScope}, w.2 < (X.tr w.1).length →
    (AsyncCopy.AsyncObserved Y x .mmaDone w acq ws ↔ AsyncCopy.AsyncObserved X x .mmaDone w acq ws)
  operands : ∀ i ops, Y.async.mmaOperands i = some ops → X.async.mmaOperands i = some ops
  /-- A new record covers nothing and is in no pairing. -/
  pairs : ∀ cta r, r ∈ Y.tmemHistory cta →
    r ∈ X.tmemHistory cta ∨ ((∀ owner e col, ¬ Tmem.Pair.Covers L Y r owner e col) ∧
      ∀ q ∈ Y.tmemPairing, q.1 ≠ r.own ∧ q.2 ≠ r.own)
  mbarExec : ∀ {x f : EvId}, f.2 < (X.tr f.1).length → (MbarExec L Y x f ↔ MbarExec L X x f)
  /-- A new pairing of an allocation record publishes nothing: no lane event of either of its
  requests happens before an event (`Tmem.Pair.PairAllocBefore`). -/
  pairings : ∀ q ∈ Y.tmemPairing, q ∈ X.tmemPairing ∨
    ∀ cta r, r ∈ Y.tmemHistory cta → (q.1 = r.own ∨ q.2 = r.own) →
      (∃ n base, r.action = .alloc n base) →
      ∀ lane e, ¬ _root_.PTX.baseCausality L X (q.1.event L lane) e ∧
        ¬ _root_.PTX.baseCausality L X (q.2.event L lane) e

section
variable {L : Launch} {A : List Assumption} {X Y : Execution} (h : ReadPreserved L X Y)
include h

private theorem old_get {e : EvId} {ev : Event} (he : Y.get e = some ev)
    (hold : e.2 < (X.tr e.1).length) : X.get e = some ev := by
  obtain ⟨suffix, hs⟩ := h.le.1 e.1
  unfold Execution.get at he ⊢
  rw [← hs, List.getElem?_append_left hold] at he
  exact he

theorem ReadPreserved.tcFrame : TcFrame L X Y :=
  ⟨h.le, h.hb, h.mbarExec, h.observes⟩

private theorem baseCausality_old {x f : EvId} (hf : f.2 < (X.tr f.1).length)
    (hy : _root_.PTX.baseCausality L Y x f) :
    _root_.PTX.baseCausality L X x f ∧ x.2 < (X.tr x.1).length := by
  have hx := (h.hb hf).mp hy
  exact ⟨hx, (baseCausality_events hx).1⟩

theorem ReadPreserved.mmaIssue {i : EvId} {d : Nat} {s : OperandSpec} {accum : Bool}
    {mask : List Nat} (hold : i.2 < (X.tr i.1).length) :
    Y.MmaIssue i d s accum mask ↔ X.MmaIssue i d s accum mask :=
  ⟨fun ⟨pc, hp⟩ => ⟨pc, old_get h hp hold⟩, fun ⟨pc, hp⟩ => ⟨pc, Execution.le_get h.le hp⟩⟩

theorem ReadPreserved.mmaCell {i : EvId} {cell : Cell} (hx : X.MmaCell i cell) :
    Y.MmaCell i cell := by
  obtain ⟨d, s, accum, mask, row, col, ⟨pc, hp⟩, hw⟩ := hx
  exact ⟨d, s, accum, mask, row, col, ⟨pc, Execution.le_get h.le hp⟩, hw⟩

theorem ReadPreserved.doneBefore {x f : EvId} (hf : f.2 < (X.tr f.1).length)
    (hd : DoneBefore L Y x f) : DoneBefore L X x f :=
  (h.tcFrame.doneBefore hf).mp hd

theorem ReadPreserved.waitBefore {k : TcKind} {x f : EvId} (hf : f.2 < (X.tr f.1).length)
    (hd : WaitBefore L Y k x f) : WaitBefore L X k x f :=
  (h.tcFrame.waitBefore hf).mp hd

theorem ReadPreserved.cpIssue {i : EvId} {c : TcCopy.Spec} (hold : i.2 < (X.tr i.1).length) :
    Y.CpIssue i c ↔ X.CpIssue i c :=
  ⟨fun ⟨pc, hp⟩ => ⟨pc, old_get h hp hold⟩, fun ⟨pc, hp⟩ => ⟨pc, Execution.le_get h.le hp⟩⟩

theorem ReadPreserved.shiftIssue {i : EvId} {s : TcShift.Spec} (hold : i.2 < (X.tr i.1).length) :
    Y.ShiftIssue i s ↔ X.ShiftIssue i s :=
  ⟨fun ⟨pc, hp⟩ => ⟨pc, old_get h hp hold⟩, fun ⟨pc, hp⟩ => ⟨pc, Execution.le_get h.le hp⟩⟩

theorem ReadPreserved.tst {i : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    (hold : i.2 < (X.tr i.1).length) : Y.TSt i a vals sh ↔ X.TSt i a vals sh :=
  ⟨fun ⟨pc, hp⟩ => ⟨pc, old_get h hp hold⟩, fun ⟨pc, hp⟩ => ⟨pc, Execution.le_get h.le hp⟩⟩

theorem ReadPreserved.tld {i : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    (hold : i.2 < (X.tr i.1).length) : Y.TLd i a vals sh ↔ X.TLd i a vals sh :=
  ⟨fun ⟨pc, hp⟩ => ⟨pc, old_get h hp hold⟩, fun ⟨pc, hp⟩ => ⟨pc, Execution.le_get h.le hp⟩⟩

theorem ReadPreserved.tcAsync {i : EvId} (hold : i.2 < (X.tr i.1).length) :
    Y.TcAsync i ↔ X.TcAsync i := by
  unfold Execution.TcAsync
  simp only [h.mmaIssue hold, h.cpIssue hold, h.shiftIssue hold]

theorem ReadPreserved.completedBefore {x f : EvId} (hf : f.2 < (X.tr f.1).length)
    (hxo : x.2 < (X.tr x.1).length) (hd : CompletedBefore L Y x f) : CompletedBefore L X x f :=
  ⟨fun ⟨a, v, sh, hp⟩ => h.waitBefore hf (hd.1 ⟨a, v, sh, (h.tld hxo).mpr hp⟩),
    fun ⟨a, v, sh, hp⟩ => h.waitBefore hf (hd.2.1 ⟨a, v, sh, (h.tst hxo).mpr hp⟩),
    fun hk => h.doneBefore hf (hd.2.2 ((h.tcAsync hxo).mpr hk))⟩

private theorem tc_old {x f : EvId} (hf : f.2 < (X.tr f.1).length) (hy : TcBefore L Y x f) :
    TcBefore L X x f ∧ x.2 < (X.tr x.1).length := by
  have hx := (h.tcFrame.tcBefore hf).mp hy
  exact ⟨hx, (tcStep_path_events hx.tcStep).1⟩

/-- Every pipelined pair ending at an old operation restricts to the original execution, with
its first operation old. -/
theorem ReadPreserved.pipelined {a c : PipeAccess} {x f : EvId} (hf : f.2 < (X.tr f.1).length)
    (hd : Pipelined L Y a x c f) : Pipelined L X a x c f ∧ x.2 < (X.tr x.1).length := by
  cases a <;> cases c <;> try exact hd.elim
  all_goals
    obtain ⟨hw, hxf, hr⟩ := hd
    obtain ⟨hxf', hxo⟩ := tc_old h hf hxf
  · obtain ⟨⟨d, s, acc, mask, hi, ha⟩, d', s', acc', mask', hi'⟩ := hr
    exact ⟨⟨hw, hxf', ⟨d, s, acc, mask, (h.mmaIssue hxo).mp hi, ha⟩, d', s', acc', mask',
      (h.mmaIssue hf).mp hi'⟩, hxo⟩
  · obtain ⟨⟨d, s, acc, mask, hi, ha⟩, c, hc⟩ := hr
    exact ⟨⟨hw, hxf', ⟨d, s, acc, mask, (h.mmaIssue hxo).mp hi, ha⟩, c,
      (h.cpIssue hf).mp hc⟩, hxo⟩
  all_goals first
    | (obtain ⟨d, s, acc, mask, d', s', acc', mask', hi, hi', hs⟩ := hr
       exact ⟨⟨hw, hxf', d, s, acc, mask, d', s', acc', mask', (h.mmaIssue hxo).mp hi,
        (h.mmaIssue hf).mp hi', hs⟩, hxo⟩)
    | (obtain ⟨c, d, s, acc, mask, hc, hne, hm, ha⟩ := hr
       exact ⟨⟨hw, hxf', c, d, s, acc, mask, (h.cpIssue hxo).mp hc, hne,
        (h.mmaIssue hf).mp hm, ha⟩, hxo⟩)
    | (obtain ⟨⟨a, v, sh, h1⟩, ⟨a', v', sh', h2⟩⟩ := hr
       first
         | exact ⟨⟨hw, hxf', ⟨a, v, sh, (h.tst hxo).mp h1⟩, ⟨a', v', sh', (h.tld hf).mp h2⟩⟩, hxo⟩
         | exact ⟨⟨hw, hxf', ⟨a, v, sh, (h.tst hxo).mp h1⟩, ⟨a', v', sh', (h.tst hf).mp h2⟩⟩, hxo⟩
         | exact ⟨⟨hw, hxf', ⟨a, v, sh, (h.tld hxo).mp h1⟩, ⟨a', v', sh', (h.tst hf).mp h2⟩⟩, hxo⟩)

theorem ReadPreserved.before {x f : EvId} (hf : f.2 < (X.tr f.1).length)
    (hd : Before L Y x f) : Before L X x f ∧ x.2 < (X.tr x.1).length := by
  rcases hd with hd | hd
  · have hd' := h.doneBefore hf hd
    exact ⟨.inl hd', (tcStep_path_events hd'.tcStep).1⟩
  · obtain ⟨h1, h2⟩ := h.pipelined hf hd
    exact ⟨.inr h1, h2⟩

theorem ReadPreserved.tmemWrite {i : EvId} {cell : Cell} (hx : TmemWrite L X i cell) :
    TmemWrite L Y i cell := by
  rcases hx with ⟨d, s, accum, mask, row, col, ⟨pc, hp⟩, hw⟩ |
    ⟨a, vals, sh, j, ⟨pc, hp⟩, hj, hc⟩ | ⟨c, cta, index, lane, ⟨pc, hp⟩, hk⟩ |
    ⟨s, ⟨pc, hp⟩, hw⟩
  · exact .inl ⟨d, s, accum, mask, row, col, ⟨pc, Execution.le_get h.le hp⟩, hw⟩
  · exact .inr (.inl ⟨a, vals, sh, j, ⟨pc, Execution.le_get h.le hp⟩, hj, hc⟩)
  · exact .inr (.inr (.inl ⟨c, cta, index, lane, ⟨pc, Execution.le_get h.le hp⟩, hk⟩))
  · exact .inr (.inr (.inr ⟨s, ⟨pc, Execution.le_get h.le hp⟩, hw⟩))

omit h in
theorem tmemWrite_lt {X : Execution} {i : EvId} {cell : Cell} (hx : TmemWrite L X i cell) :
    i.2 < (X.tr i.1).length := by
  rcases hx with ⟨_, _, _, _, _, _, ⟨pc, hp⟩, _⟩ | ⟨_, _, _, _, ⟨pc, hp⟩, _⟩ |
    ⟨_, _, _, _, ⟨pc, hp⟩, _⟩ | ⟨_, ⟨pc, hp⟩, _⟩ <;> exact len_of_get hp

theorem ReadPreserved.tmemWrite_old {i : EvId} {cell : Cell} (hold : i.2 < (X.tr i.1).length)
    (hy : TmemWrite L Y i cell) : TmemWrite L X i cell := by
  rcases hy with ⟨d, s, accum, mask, row, col, hi, hw⟩ | ⟨a, vals, sh, j, ht, hj, hc⟩ |
    ⟨c, cta, index, lane, hi, hk⟩ | ⟨s, hs, hw⟩
  · exact .inl ⟨d, s, accum, mask, row, col, (h.mmaIssue hold).mp hi, hw⟩
  · exact .inr (.inl ⟨a, vals, sh, j, (h.tst hold).mp ht, hj, hc⟩)
  · exact .inr (.inr (.inl ⟨c, cta, index, lane, (h.cpIssue hold).mp hi, hk⟩))
  · exact .inr (.inr (.inr ⟨s, (h.shiftIssue hold).mp hs, hw⟩))

theorem ReadPreserved.storeDoneBefore {x f : EvId} (hf : f.2 < (X.tr f.1).length)
    (hd : StoreDoneBefore L Y x f) :
    StoreDoneBefore L X x f ∧ x.2 < (X.tr x.1).length := by
  obtain ⟨⟨a, vals, sh, ht⟩, hw | hp⟩ := hd
  · have hw' := (h.tcFrame.waitBefore hf).mp hw
    have hxo := (tcStep_path_events hw'.tcStep).1
    exact ⟨⟨⟨a, vals, sh, (h.tst hxo).mp ht⟩, .inl hw'⟩, hxo⟩
  · rcases hp with hp | hp
    · obtain ⟨h1, hxo⟩ := h.pipelined hf hp
      exact ⟨⟨⟨a, vals, sh, (h.tst hxo).mp ht⟩, .inr (.inl h1)⟩, hxo⟩
    · obtain ⟨h1, hxo⟩ := h.pipelined hf hp
      exact ⟨⟨⟨a, vals, sh, (h.tst hxo).mp ht⟩, .inr (.inr h1)⟩, hxo⟩

/-- Coverage of an old event by an old record is unchanged by the extension, as far as it
exists in the original execution. -/
theorem ReadPreserved.covers_mono {r : Tmem.Pair.Requests} {owner : Nat} {e : EvId} {col : Nat}
    (he : e.2 < (X.tr e.1).length) (hc : Tmem.Pair.Covers L X r owner e col) :
    Tmem.Pair.Covers L Y r owner e col := by
  obtain ⟨n, base, ha, ho, hl, hu, hc⟩ := hc
  refine ⟨n, base, ha, ho, hl, hu, hc.imp (h.hb he).mpr ?_⟩
  rintro ⟨q, hq, p, hp, lane, hb⟩
  exact ⟨q, (Execution.le_tmemPairing h.le).subset hq, p, hp, lane, (h.hb he).mpr hb⟩

theorem ReadPreserved.covers_old {cta : Nat} {r : Tmem.Pair.Requests} {owner : Nat} {e : EvId}
    {col : Nat} (he : e.2 < (X.tr e.1).length) (hr : r ∈ Y.tmemHistory cta)
    (hc : Tmem.Pair.Covers L Y r owner e col) : r ∈ X.tmemHistory cta ∧
      Tmem.Pair.Covers L X r owner e col := by
  rcases h.pairs cta r hr with hr' | hn
  · refine ⟨hr', ?_⟩
    obtain ⟨n, base, ha, ho, hl, hu, hc⟩ := hc
    refine ⟨n, base, ha, ho, hl, hu, hc.imp (h.hb he).mp ?_⟩
    rintro ⟨q, hq, p, hqp, lane, hhb⟩
    have hhb' := (h.hb he).mp hhb
    have hown : q.1 = r.own ∨ q.2 = r.own := hqp.imp And.left And.left
    refine ⟨q, ?_, p, hqp, lane, hhb'⟩
    rcases h.pairings q hq with hq' | hn
    · exact hq'
    · have hno := hn cta r hr hown ⟨n, base, ha⟩ lane e
      rcases hqp with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact (hno.2 hhb').elim
      · exact (hno.1 hhb').elim
  · exact (hn.1 _ _ _ hc).elim

omit h in
private theorem releaseOf_lt {r : Tmem.Pair.Requests} {d : EvId}
    (hrel : Tmem.Pair.ReleaseOf L X r d) : d.2 < (X.tr d.1).length := by
  rcases hrel with ⟨_, _, _, _, ⟨_, hp⟩, _⟩ | ⟨_, _, _, _, _, ⟨_, _, _, _, ⟨_, hp⟩, _⟩⟩ <;>
    exact len_of_get hp

theorem ReadPreserved.releaseOf {r : Tmem.Pair.Requests} {d : EvId}
    (hd : Tmem.Pair.ReleaseOf L X r d) : Tmem.Pair.ReleaseOf L Y r d := by
  have one {w : Tmem.Pair.Requests} (hw : Tmem.Pair.OwnRelease L X w d) :
      Tmem.Pair.OwnRelease L Y w d := by
    obtain ⟨n, base, pc, ha, ⟨group, hp⟩, hlane⟩ := hw
    have hdo := len_of_get hp
    refine ⟨n, base, pc, ha, ⟨group, Execution.le_get h.le hp⟩, ?_⟩
    rcases hlane with ⟨lane, hthread, hidx, hfirst⟩ | hother
    · refine .inl ⟨lane, hthread, hidx, ?_⟩
      intro f pc' group' hf hft hfi
      by_cases hfo : f.2 < (X.tr f.1).length
      · exact hfirst f pc' group' (old_get h hf hfo) hft hfi
      · rw [hft] at hfo; omega
    · exact .inr hother
  rcases hd with hw | ⟨q, hq, s, hs, hpair, hw⟩
  · exact .inl (one hw)
  · exact .inr ⟨q, (Execution.le_tmemPairing h.le).subset hq, s,
      (Execution.le_tmemHistory h.le _).subset hs, hpair, one hw⟩

theorem ReadPreserved.writeBefore {x f : EvId} (hf : f.2 < (X.tr f.1).length)
    (hd : WriteBefore L Y x f) : WriteBefore L X x f ∧ x.2 < (X.tr x.1).length := by
  rcases hd with hd | hd | hd
  · obtain ⟨h1, h2⟩ := h.before hf hd
    exact ⟨.inl h1, h2⟩
  · obtain ⟨h1, h2⟩ := h.storeDoneBefore hf hd
    exact ⟨.inr (.inl h1), h2⟩
  · obtain ⟨h1, h2⟩ := h.pipelined hf hd
    exact ⟨.inr (.inr h1), h2⟩

theorem ReadPreserved.readBefore {k : TmemRead} {e w : EvId} (hw : w.2 < (X.tr w.1).length)
    (hd : ReadBefore L Y k e w) : ReadBefore L X k e w := by
  cases k <;> simp only [ReadBefore] at hd ⊢
  · rcases hd with hd | hd
    · exact .inl (h.waitBefore hw hd)
    · exact .inr (h.pipelined hw hd).1
  · rcases hd with hd | hd | hd
    · exact .inl hd
    · exact .inr (.inl (h.doneBefore hw hd))
    · exact .inr (.inr (h.pipelined hw hd).1)
  · rcases hd with hd | hd | hd | hd
    · exact .inl hd
    · exact .inr (.inl (h.doneBefore hw hd))
    · exact .inr (.inr (.inl (h.pipelined hw hd).1))
    · exact .inr (.inr (.inr (h.pipelined hw hd).1))
  · rcases hd with hd | hd
    · exact .inl hd
    · exact .inr (h.doneBefore hw hd)

private theorem pairs_mono {cta : Nat} {r : Tmem.Pair.Requests} (hr : r ∈ X.tmemHistory cta) :
    r ∈ Y.tmemHistory cta := by
  obtain ⟨suffix, hs⟩ := Execution.le_tmemHistory h.le cta
  rw [← hs]
  exact List.mem_append_left _ hr

theorem ReadPreserved.sourceLive {source consumer : EvId} {cell : Cell}
    (hc : consumer.2 < (X.tr consumer.1).length) (hso : source.2 < (X.tr source.1).length)
    (hl : SourceLive L Y source consumer cell) : SourceLive L X source consumer cell := by
  intro cta r hr hcov release hrel
  rcases hl cta r (pairs_mono h hr) (h.covers_mono hc hcov) release (h.releaseOf hrel) with
    h1 | h1
  · exact .inl (h.completedBefore (releaseOf_lt hrel) hc h1)
  · exact .inr (baseCausality_old h hso h1).1

/-- An old read's source restricts to the original execution, and is old. -/
theorem ReadPreserved.readSource {k : TmemRead} {source e : EvId} {cell : Cell}
    (he : e.2 < (X.tr e.1).length) (hs : ReadSource L Y k source e cell) :
    ReadSource L X k source e cell ∧ source.2 < (X.tr source.1).length := by
  obtain ⟨hne, hwrite, hbefore, hstable, hlive⟩ := hs
  obtain ⟨hbefore', hso⟩ := h.writeBefore he hbefore
  refine ⟨⟨hne, h.tmemWrite_old hso hwrite, hbefore', ?_, h.sourceLive he hso hlive⟩, hso⟩
  intro other ho
  have hoo := tmemWrite_lt ho
  rcases hstable other (h.tmemWrite ho) with h1 | h1 | h1
  · exact .inl h1
  · exact .inr (.inl (h.writeBefore hso h1).1)
  · exact .inr (.inr (h.readBefore hoo h1))

theorem ReadPreserved.result {source : EvId} {cell : Cell} {v : Value}
    (hr : Result L A Y source cell v) (hs : source.2 < (X.tr source.1).length) :
    Result L A X source cell v := by
  induction hr with
  | overwrite issue position reads arithmetic =>
    exact .overwrite ((h.mmaIssue hs).mp issue) position (h.operands _ _ reads) arithmetic
  | accumulate issue position reads _ provenance arithmetic ih =>
    obtain ⟨prov, hpo⟩ := h.readSource hs provenance
    exact .accumulate ((h.mmaIssue hs).mp issue) position (h.operands _ _ reads) (ih hpo) prov
      arithmetic
  | accumulateStored issue position reads previous provenance arithmetic =>
    obtain ⟨prov, hpo⟩ := h.readSource hs provenance
    obtain ⟨a, vals, sh, j, ht, hj, hc⟩ := previous
    exact .accumulateStored ((h.mmaIssue hs).mp issue) position (h.operands _ _ reads)
      ⟨a, vals, sh, j, (h.tst hpo).mp ht, hj, hc⟩ prov arithmetic

theorem ReadPreserved.storeValue {source : EvId} {cell : Cell} {v : Value}
    (hs : source.2 < (X.tr source.1).length) (hv : StoreValue L Y source cell v) :
    StoreValue L X source cell v := by
  obtain ⟨a, vals, sh, j, ht, hj, hc⟩ := hv
  exact ⟨a, vals, sh, j, (h.tst hs).mp ht, hj, hc⟩

theorem ReadPreserved.cpValue {source : EvId} {cell : Cell} {v : Value}
    (hs : source.2 < (X.tr source.1).length) (hv : CpValue Y source cell v) :
    CpValue X source cell v := by
  obtain ⟨c, k, cta, ops, row, col, lane, hc, hk, ho, hrow, hcol, hl, hcell, hw⟩ := hv
  exact ⟨c, k, cta, ops, row, col, lane, (h.cpIssue hs).mp hc, hk, h.operands _ _ ho, hrow, hcol,
    hl, hcell, hw⟩

theorem ReadPreserved.shiftValue {sh : EvId} {cell : Cell} {v : Value}
    (hs : sh.2 < (X.tr sh.1).length) (hv : ShiftValue L A Y sh cell v) :
    ShiftValue L A X sh cell v := by
  obtain ⟨source, from', ⟨⟨s, hi, hw⟩, hsrc, ⟨s', hi', hr⟩, hrs⟩, hval⟩ := hv
  obtain ⟨hrs', hso⟩ := h.readSource hs hrs
  refine ⟨source, from', ⟨⟨s, (h.shiftIssue hs).mp hi, hw⟩, hsrc,
    ⟨s', (h.shiftIssue hs).mp hi', hr⟩, hrs'⟩, ?_⟩
  rcases hval with hv | hv | hv
  · exact .inl (h.result hv hso)
  · exact .inr (.inl (h.storeValue hso hv))
  · exact .inr (.inr (h.cpValue hso hv))

theorem ReadPreserved.wrote {source : EvId} {cell : Cell} {v : Value}
    (hs : source.2 < (X.tr source.1).length) (hv : Wrote L A Y source cell v) :
    Wrote L A X source cell v := by
  rcases hv with hv | hv | hv | hv
  · exact .inl (h.result hv hs)
  · exact .inr (.inl (h.storeValue hs hv))
  · exact .inr (.inr (.inl (h.cpValue hs hv)))
  · exact .inr (.inr (.inr (h.shiftValue hs hv)))

/-- Old loads and old MMA operand reads keep their read constraints; only new loads are new
obligations (a new MMA has no recorded operands that the original execution lacks). -/
theorem ReadPreserved.readOk (hx : ReadOk L A X) (ht : AsyncCopy.TcEffectsOk X)
    (hnew : ∀ (load : EvId) (address : Nat) (vals : List Value) (sh : TcShape) (j : Nat)
      (source : EvId) (cell : Cell) (value : Value), Y.TLd load address vals sh →
      LoadCell L Y load j cell → (X.tr load.1).length ≤ load.2 →
      ReadSource L Y .ld source load cell → Wrote L A Y source cell value →
      ∃ word, vals[j]? = some word ∧ WordContains value word) :
    ReadOk L A Y := by
  refine ⟨fun load address vals sh j source cell value hl hc hs hw => ?_,
    fun mma index cell pos source value ops hi hs hw ho hp => ?_⟩
  · by_cases hlo : load.2 < (X.tr load.1).length
    · obtain ⟨hs', hso⟩ := h.readSource hlo hs
      obtain ⟨a, vs, sh', hl', hj, hcell⟩ := hc
      exact hx.1 load address vals sh j source cell value ((h.tld hlo).mp hl)
        ⟨a, vs, sh', (h.tld hlo).mp hl', hj, hcell⟩ hs' (h.wrote hso hw)
    · exact hnew load address vals sh j source cell value hl hc (Nat.le_of_not_lt hlo) hs hw
  · have hox := h.operands _ _ ho
    have hmo : mma.2 < (X.tr mma.1).length := by
      have hs' : X.async.mmaStarted mma = true := by simp [AsyncCopy.Snapshot.mmaStarted, hox]
      rcases ht.1 mma hs' with ⟨_, _, _, _, _, ⟨pc, hi⟩, _⟩ | ⟨_, _, ⟨pc, hi⟩, _⟩ |
        ⟨_, _, ⟨pc, hi⟩, _⟩ <;> exact len_of_get hi
    obtain ⟨d, s, accum, mask, hi', hc⟩ := hi
    obtain ⟨hs', hso⟩ := h.readSource hmo hs
    exact hx.2 mma index cell pos source value ops
      ⟨d, s, accum, mask, (h.mmaIssue hmo).mp hi', hc⟩ hs' (h.wrote hso hw) hox hp

end

/-- When every MMA reads A from shared memory, the Tensor Memory A rule is vacuous. -/
theorem aReadOk_of_shared {L : Launch} {A : List Assumption} {X : Execution}
    (h : ∀ i d s acc mask, X.MmaIssue i d s acc mask → s.aTmem = none) :
    AReadOk L A X := by
  intro mma index cell pos source value ops hs
  obtain ⟨d, s, acc, mask, hi, hc⟩ := hs
  simp [aCell, h _ _ _ _ _ hi] at hc

/-- Without loads the read constraint is vacuous. -/
theorem readOk_of_no_load {L : Launch} {A : List Assumption} {X : Execution}
    (h : ∀ load address vals sh, ¬ X.TLd load address vals sh)
    (hA : ∀ i d s acc mask, X.MmaIssue i d s acc mask → s.aTmem = none) :
    ReadOk L A X :=
  ⟨fun load address vals sh _ _ _ _ hl _ _ _ => (h load address vals sh hl).elim,
    aReadOk_of_shared hA⟩

end
end PTX.TcMma
