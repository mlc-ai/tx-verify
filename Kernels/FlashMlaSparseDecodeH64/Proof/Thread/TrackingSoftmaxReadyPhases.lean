-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReady
import Lemmas.Order.CausalObjectWaitCount

@[expose] public section

/-! # Distinct ready phases before a WG0 slot release -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier
open Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private structure ReadyState (X : Execution) (m : Loc) (g q p : Nat) where
  index : Nat
  record : Record Ref
  before : State
  get : (X.objects m)[index]? = some record
  source : record.id = .thread (g, q)
  clean : record.fault = none
  waited : record.reply.waited = some true
  state : stateBefore (X.objects m) index = some before
  expected : before.expected = 32
  parity : before.phase % 2 ≠ p % 2
  completion : record.reply.completed = if 0 < before.phase then some (before.phase - 1) else none

private theorem softmax_ready_state {g q p tag : Nat} {z : Wg0.D} {slot : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hState : Frame.stateAt (Machine.code P L) X g q = some (some (.wg0 z)))
    (hWait : X.get (g, q) = some ⟨tag, .wait (ready L (ctaOf L g) slot) p true true .cta⟩) :
    Nonempty (ReadyState X (ready L (ctaOf L g) slot) g q p) := by
  let entry := readyEntry slot
  have hloc := ready_entry_loc L (ctaOf L g) slot
  have hw : X.get (g, q) = some ⟨tag, .wait (initTable.loc L (ctaOf L g) entry) p true true .cta⟩ :=
    hloc ▸ hWait
  obtain ⟨i, r, t, hi, hid, hstate, hExp, hAct, hClean, hWaited⟩ :=
    wait_after_table_init hpre hX hs hState (by intro s he; cases he) entry hw
  rw [hloc] at hi hstate
  change t.expected = initCount (readyEntry slot) at hExp
  rw [ready_entry_count] at hExp
  obtain ⟨v, p', hv, hAct', hParity, hComp⟩ :=
    (X.objects_checked hX (ready L (ctaOf L g) slot)).okPoll hi hWaited
  rw [hstate] at hv
  obtain rfl := Option.some.inj hv
  rw [hAct] at hAct'
  obtain ⟨rfl, _⟩ := Action.pollParity.inj hAct'
  exact ⟨⟨i, r, t, hi, hid, hClean, hWaited, hstate, hExp, hParity, hComp⟩⟩

private theorem ready_state_producers {g i q p tag : Nat} {e : Event} {slot : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hq : q < i)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t)
    (hWait : X.get (g, q) = some ⟨tag, .wait (ready L (ctaOf L g) slot) p true true .cta⟩)
    (S : ReadyState X (ready L (ctaOf L g) slot) g q p)
    (hPos : 0 < S.before.phase) :
    let m := ready L (ctaOf L g) slot
    let log := X.objects m
    ∃ positions : Finset Nat, positions.card = 32 ∧ ∀ t ∈ positions,
      ∃ (r : Record Ref) (h j : Nat) (f : Event) (d : Wg1Index.D) (extra : Bool),
        log[t]? = some r ∧ r.id = .thread (h, j) ∧ phaseAt log t = some (S.before.phase - 1) ∧
        ctaOf L h = ctaOf L g ∧ d.block % 4 = slot.val ∧ d.site = .ready extra ∧
        X.get (h, j) = some f ∧ Frame.stateAt (Machine.code P L) X h j = some (some (.index d)) ∧
        baseCausality L X (h, j) (g, i) := by
  let m := ready L (ctaOf L g) slot
  have hObs : observedAt (X.objects m) S.index = some (S.before.phase - 1) := by
    change observedAt (X.objects (ready L (ctaOf L g) slot)) S.index = _
    simp only [observedAt, S.get, Option.bind_some, S.completion, ite_eq_left hPos]
  have hPhase : S.before.phase = (S.before.phase - 1) + 1 := by omega
  obtain ⟨positions, hCard, hRecords⟩ := observed_ready_producers hpre hX hs he hq hPrior
    hWait S.source S.clean S.waited S.get hObs S.state hPhase S.expected
  refine ⟨positions, hCard, fun t ht => ?_⟩
  obtain ⟨r, h, j, hEarlier, hr, hid, _, hClean, hAt, hc, d, hSlot, ⟨extra, hSite⟩, hSt⟩ :=
    hRecords t ht
  obtain ⟨f, hf⟩ := hX.object_thread_record_present (List.mem_of_getElem? hr) hid
  have hh := Frame.lt_of_get hX hf
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, hFire⟩ := RingEvents.fired_of_trace hX (hs h hh).machine hf hSt
  have hKind := RingEvents.validReady_arrive hpre hSite hFire
  change h / L.block = ctaOf L g at hc
  rw [hc, hSlot] at hKind
  change f.kind = .arrive m 0 1 true .cta at hKind
  have hRelease : MbarRelease X (h, j) m .cta :=
    ⟨0, 1, f.pc, by rw [hf, ← hKind]⟩
  have hObserve : WaitObserves X (.thread (h, j)) (g, q) m true .cta :=
    ⟨⟨tag, p, hWait⟩, t, S.index, r, S.record, S.before.phase - 1, hr, hid,
      hClean, S.get, S.source, S.clean, S.waited, hEarlier, hAt, hObs,
      (objects_single_lifetime hX m).sameLifetime t S.index⟩
  have hBefore := Staging.baseCausality_of_handoff hRelease hObserve
    (ScopesMeet.of_sameCta ⟨hh, hg, hc⟩) (e := (h, j)) (f := (g, i)) ⟨rfl, le_rfl⟩
    ⟨rfl, hq, PTX.len_of_get he⟩
  exact ⟨r, h, j, f, d, extra, hr, hid, hAt, hc, hSlot, hSite, hf, hSt, hBefore⟩

private structure CountedReadyState (X : Execution) (m : Loc) (g i n : Nat) where
  pos : Nat
  tag : Nat
  earlier : pos < i
  wait : X.get (g, pos) = some ⟨tag, .wait m (n % 2) true true .cta⟩
  count : Flow.okPolls m ((X.tr g).take pos) = n
  ready : ReadyState X m g pos (n % 2)

private theorem CountedReadyState.phase_lt_succ {g i n : Nat} {m : Loc}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (a : CountedReadyState X m g i n) (b : CountedReadyState X m g i (n + 1)) :
    a.ready.before.phase < b.ready.before.phase := by
  have hq : a.pos < b.pos := by
    by_contra! hn
    have hp := MbarRing.Poll.okPolls_mono m (X.tr g) hn
    rw [a.count, b.count] at hp
    omega
  have hi := (hX.object_thread_index_iff a.ready.get b.ready.get
    a.ready.source b.ready.source).mpr hq
  obtain ⟨v, hv, hMon⟩ := (X.objects_checked hX m).phase_mono (objects_single_lifetime hX m) hi.le
    (List.getElem?_eq_some_iff.mp b.ready.get).1.le a.ready.state
  rw [b.ready.state] at hv
  obtain rfl := Option.some.inj hv
  have hp0 := a.ready.parity
  have hp1 := b.ready.parity
  omega

/-- A followed WG0 mask read or slot release depends on a distinct ready phase for each slot use
through its own. Each phase contributes 32 actual index publication records. -/
theorem softmax_ready_pool {g i n : Nat} {d : Wg0.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hSite : d.site = .validFree ∨ d.site = .maskRead) (hUse : n ≤ d.block / 4)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) :
    let m := ready L (ctaOf L g) (indexSlot d.block)
    let log := X.objects m
    ∃ positions : Finset Nat, positions.card = (n + 1) * 32 ∧ ∀ t ∈ positions,
      ∃ (r : Record Ref) (h j : Nat) (f : Event) (z : Wg1Index.D) (extra : Bool),
        log[t]? = some r ∧ r.id = .thread (h, j) ∧ ctaOf L h = ctaOf L g ∧
        z.block % 4 = d.block % 4 ∧ z.site = .ready extra ∧
        X.get (h, j) = some f ∧ Frame.stateAt (Machine.code P L) X h j = some (some (.index z)) ∧
        baseCausality L X (h, j) (g, i) := by
  classical
  let m := ready L (ctaOf L g) (indexSlot d.block)
  have hg := Frame.lt_of_get hX he
  have existsPoll (a : Fin (n + 1)) : Nonempty (CountedReadyState X m g i a.val) := by
    obtain ⟨q, tag, z, hq, hWait, hCount, hZ⟩ :=
      softmax_ready_acquire hpre hX (hs g hg).machine he hd hSite
        (n := a.val) (by have := a.isLt; omega)
    obtain ⟨r⟩ := softmax_ready_state hpre hX hs hZ hWait
    exact ⟨⟨q, tag, hq, hWait, hCount, r⟩⟩
  let poll (a : Fin (n + 1)) := (existsPoll a).some
  have hSeq : StrictMono (fun a : Fin (n + 1) => (poll a).ready.before.phase) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro a
    exact (poll a.castSucc).phase_lt_succ hX (poll a.succ)
  have hPos (a : Fin (n + 1)) : 0 < (poll a).ready.before.phase := by
    have hInit : 0 < (poll 0).ready.before.phase := by
      have hp := (poll 0).ready.parity
      change (poll 0).ready.before.phase % 2 ≠ 0 at hp
      omega
    exact hInit.trans_le (hSeq.monotone (Fin.zero_le a))
  have positionsOf (a : Fin (n + 1)) :
      ∃ positions : Finset Nat, positions.card = 32 ∧ ∀ t ∈ positions,
        ∃ (r : Record Ref) (h j : Nat) (f : Event) (z : Wg1Index.D) (extra : Bool),
          (X.objects m)[t]? = some r ∧ r.id = .thread (h, j) ∧
          phaseAt (X.objects m) t = some ((poll a).ready.before.phase - 1) ∧
          ctaOf L h = ctaOf L g ∧ z.block % 4 = d.block % 4 ∧ z.site = .ready extra ∧
          X.get (h, j) = some f ∧ Frame.stateAt (Machine.code P L) X h j = some (some (.index z)) ∧
          baseCausality L X (h, j) (g, i) :=
    ready_state_producers hpre hX hs he (poll a).earlier hPrior (poll a).wait
      (poll a).ready (hPos a)
  let batch (a : Fin (n + 1)) := (positionsOf a).choose
  have hDisjoint : (↑(Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))).PairwiseDisjoint
      batch := by
    intro a _ b _ hNe
    apply Finset.disjoint_left.mpr
    intro t ha hb
    obtain ⟨_, _, _, _, _, _, _, _, hAPhase, _⟩ := (positionsOf a).choose_spec.2 t ha
    obtain ⟨_, _, _, _, _, _, _, _, hBPhase, _⟩ := (positionsOf b).choose_spec.2 t hb
    have hEq := Option.some.inj (hAPhase.symm.trans hBPhase)
    have hA := hPos a
    have hB := hPos b
    exact hNe (hSeq.injective (by omega))
  refine ⟨Finset.univ.biUnion batch, ?_, ?_⟩
  · rw [Finset.card_biUnion hDisjoint]
    simp only [show ∀ a, (batch a).card = 32 from fun a => (positionsOf a).choose_spec.1,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  · intro t ht
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨r, h, j, f, z, extra, hr, hid, _, hc, hSlot, hz, hf, hSt, hBefore⟩ :=
      (positionsOf a).choose_spec.2 t ha
    exact ⟨r, h, j, f, z, extra, hr, hid, hc, hSlot, hz, hf, hSt, hBefore⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
