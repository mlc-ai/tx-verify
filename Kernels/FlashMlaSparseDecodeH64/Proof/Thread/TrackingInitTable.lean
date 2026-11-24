-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingInitOrigins
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingInit

@[expose] public section

/-! # The actual initialization table without a tracking premise -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- A real initialization of a table entry has exactly its CTA, state and expected count. -/
theorem init_table_event (hs : ∀ g < L.threads, (Machine.code P L g).Sound) {cta n : Nat}
    {j : Fin 23} {e : EvId} {evt : Event} (he : X.get e = some evt)
    (hk : evt.kind = .mbInit (initTable.loc L cta j) n) :
    ctaOf L e.1 = cta ∧ n = initCount j ∧
      Frame.stateAt (Machine.code P L) X e.1 e.2 = some (some (.prologue (.init j))) := by
  obtain ⟨g, i⟩ := e
  obtain ⟨k, hd, hl, hc⟩ := init_state hpre hX hs he hk
  have hloc : initTable.loc L cta j = initTable.loc L (ctaOf L g) k := hl
  obtain ⟨rfl, hcta⟩ := initTable.loc_inj trivial trivial hloc
  exact ⟨hcta.symm, hc, hd⟩

/-- All initializations of one table object are a single real event of the elected lane. -/
theorem init_table_event_unique (hs : ∀ g < L.threads, (Machine.code P L g).Sound) {cta n n' : Nat}
    {j : Fin 23} {e f : EvId} {evt evt' : Event} (he : X.get e = some evt)
    (hf : X.get f = some evt') (hk : evt.kind = .mbInit (initTable.loc L cta j) n)
    (hk' : evt'.kind = .mbInit (initTable.loc L cta j) n') :
    e = f := by
  obtain ⟨hce, _, hse⟩ := init_table_event hpre hX hs he hk
  obtain ⟨hcf, _, hsf⟩ := init_table_event hpre hX hs hf hk'
  obtain ⟨g, i⟩ := e
  obtain ⟨h, k⟩ := f
  have hg := (hs g (Frame.lt_of_get hX he)).machine
  have hh := (hs h (Frame.lt_of_get hX hf)).machine
  have hhg := RingInitSources.init_threads_eq hpre hX hg hh he hf (hce.trans hcf.symm) hse hsf
  subst h
  rw [RingInitSources.init_entry_unique he hf hse hsf]

/-- The actual trace determines the unique initializer of each table entry that executes. -/
theorem actual_init_sites (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
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
  exact ⟨init_table_event_unique hpre hX hs he hf rfl hk,
    (init_table_event hpre hX hs he rfl).2.1⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
