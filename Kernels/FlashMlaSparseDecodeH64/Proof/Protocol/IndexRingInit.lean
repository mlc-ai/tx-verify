-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingInitSources
public import Lemmas.Protocol.BarTable

@[expose] public section

/-! # Checked initializations of the index-ring slots -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing

open PTX AsyncCopy MBarrier

/-- The prologue's 23 initialization entries, each at a distinct shared offset. -/
def initTable : BarTable (Fin 23) where
  Valid _ := True
  off := initOff
  count := initCount
  off_inj := by
    intro j k _ _
    exact (show ∀ j k : Fin 23, initOff j = initOff k → j = k by decide) j k
  count_valid := by
    intro j _
    fin_cases j <;> decide

/-- The prologue entry that initializes a slot's publication object. -/
def readyEntry (slot : Fin 4) : Fin 23 := ⟨15 + 2 * slot.val, by have := slot.isLt; omega⟩

/-- The prologue entry that initializes a slot's reuse object. -/
def freeEntry (slot : Fin 4) : Fin 23 := ⟨16 + 2 * slot.val, by have := slot.isLt; omega⟩

theorem ready_entry_count (slot : Fin 4) : initCount (readyEntry slot) = 32 := by
  fin_cases slot <;> decide

theorem free_entry_count (slot : Fin 4) : initCount (freeEntry slot) = 129 := by
  fin_cases slot <;> decide

theorem ready_entry_loc (L : Launch) (cta : Nat) (slot : Fin 4) :
    initTable.loc L cta (readyEntry slot) = ready L cta slot := by
  fin_cases slot <;> rfl

theorem free_entry_loc (L : Launch) (cta : Nat) (slot : Fin 4) :
    initTable.loc L cta (freeEntry slot) = free L cta slot := by
  fin_cases slot <;> rfl

/-- A published initializer is the first successful record. The initializer map names the
actual event of each table entry, and publication supplies it for every non-initialization
record of the object. -/
theorem published_init_first {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) {init : Fin 23 → Nat → EvId}
    (hs : initTable.InitSites L X init) (cta : Nat) (j : Fin 23)
    (hpub : ∀ r ∈ X.objects (initTable.loc L cta j), (∀ count, r.action ≠ .init count) →
      X.MbInit (init j cta) (initTable.loc L cta j) (initCount j) ∧
        InitPublished L X (init j cta) r.id.issuer (initTable.loc L cta j)) :
    PairTmaRing.InitFirst X (initTable.loc L cta j) (initCount j) := by
  intro r hr
  have hi : X.MbInit (init j cta) (initTable.loc L cta j) (initCount j) := by
    by_cases hn : ∃ count, r.action = .init count
    · obtain ⟨count, ha⟩ := hn
      obtain ⟨_, rfl, hin⟩ := BarTable.init_source hX hs (b := j) (cta := cta) trivial hr ha
      exact hin
    · exact (hpub r hr (fun count h => hn ⟨count, h⟩)).1
  have hval : validCount (initCount j) := initTable.count_valid (b := j) trivial
  obtain ⟨r0, h0, hid, ha, hf, _⟩ := init_record_success_of_unique_init hX hi hval
    (fun _ s _ hget hact => (BarTable.init_source hX hs (b := j) (cta := cta)
      trivial (List.mem_of_getElem? hget) hact).1)
    (fun _ s hget hnon => object_not_before_of_published hX ⟨_, hi⟩
      (hpub s (List.mem_of_getElem? hget) hnon).2)
  refine ⟨r0, h0, ha, hf, fun q hq ⟨count, hqa⟩ => ?_⟩
  exact hX.record_eq hq (List.mem_of_getElem? h0)
    ((BarTable.init_source hX hs (b := j) (cta := cta) trivial hq hqa).1.trans hid.symm)

/-- The ready slot is initialized with 32 arrivals when its prologue initialization is
published to the records using it. -/
theorem ready_init_first {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) {init : Fin 23 → Nat → EvId}
    (hs : initTable.InitSites L X init) (cta : Nat) (slot : Fin 4)
    (hpub : ∀ r ∈ X.objects (ready L cta slot), (∀ count, r.action ≠ .init count) →
      X.MbInit (init (readyEntry slot) cta) (ready L cta slot) 32 ∧
        InitPublished L X (init (readyEntry slot) cta) r.id.issuer (ready L cta slot)) :
    PairTmaRing.InitFirst X (ready L cta slot) 32 := by
  simpa only [ready_entry_loc, ready_entry_count] using
    published_init_first hX hs cta (readyEntry slot)
      (by simpa only [ready_entry_loc, ready_entry_count] using hpub)


variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem init_event_state {cta n : Nat} {j : Fin 23} {e : EvId} {evt : Event}
    (he : X.get e = some evt) (hk : evt.kind = .mbInit (initTable.loc L cta j) n) :
    ctaOf L e.1 = cta ∧ n = initCount j ∧
      Frame.stateAt (Machine.code P L) X e.1 e.2 = some (some (.prologue (.init j))) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨k, hd, hl, hc⟩ := RingInitSources.init_from_trace hpre hX (hs e.1 hg) ht he hk
  have hloc : initTable.loc L cta j = initTable.loc L (ctaOf L e.1) k := hl
  obtain ⟨rfl, hcta⟩ := initTable.loc_inj trivial trivial hloc
  exact ⟨hcta.symm, hc, hd⟩

/-- The two traced initializations of a table object are the same event of the elected thread. -/
theorem init_event_unique {cta n n' : Nat} {j : Fin 23} {e f : EvId} {evt evt' : Event}
    (he : X.get e = some evt) (hf : X.get f = some evt')
    (hk : evt.kind = .mbInit (initTable.loc L cta j) n)
    (hk' : evt'.kind = .mbInit (initTable.loc L cta j) n') :
    e = f := by
  obtain ⟨hce, _, hse⟩ := init_event_state hpre hX hs ht he hk
  obtain ⟨hcf, _, hsf⟩ := init_event_state hpre hX hs ht hf hk'
  rcases e with ⟨g, i⟩
  rcases f with ⟨h, k⟩
  have hg := hs g (Frame.lt_of_get hX he)
  have hh := hs h (Frame.lt_of_get hX hf)
  have hhg := RingInitSources.init_threads_eq hpre hX hg hh he hf (hce.trans hcf.symm) hse hsf
  subst h
  have hik := RingInitSources.init_entry_unique he hf hse hsf
  rw [hik]

/-- The prologue identifies every executed initialization with a unique event of its CTA.
Entries whose initialization has not executed may be assigned any event identifier. -/
theorem exists_init_sites :
    ∃ init : Fin 23 → Nat → EvId, initTable.InitSites L X init := by
  classical
  let present (j : Fin 23) (cta : Nat) :=
    ∃ (e : EvId) (evt : Event) (n : Nat),
      X.get e = some evt ∧ evt.kind = .mbInit (initTable.loc L cta j) n
  let init (j : Fin 23) (cta : Nat) : EvId :=
    if h : present j cta then h.choose else (0, 0)
  refine ⟨init, fun j cta e _ n _ he => ?_⟩
  have hex : present j cta := ⟨e, _, n, he, rfl⟩
  change e = init j cta ∧ n = initCount j
  rw [show init j cta = hex.choose by simp only [init, dite_eq_left hex]]
  obtain ⟨evt, n', hf, hk⟩ := hex.choose_spec
  exact ⟨init_event_unique hpre hX hs ht he hf rfl hk,
    (init_event_state hpre hX hs ht he rfl).2.1⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRing
