-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRingLogs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawReadyHandoff
public import Lemmas.Protocol.UnitItems
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualMbarInit
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRawActualArrival
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # Initialization and the raw ring's checked object histories -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing

open PTX MBarrier AsyncCopy PTX.Flow PTX.MbarRing MachineTracking

/-- The prologue table entry for the raw producer's publication barrier. -/
def readyEntry (slot : Fin 2) : Fin 23 :=
  ⟨4 + 6 * slot.val, by have := slot.isLt; omega⟩

/-- The prologue table entry for the consumers' reuse barrier. -/
def freeEntry (slot : Fin 2) : Fin 23 :=
  ⟨5 + 6 * slot.val, by have := slot.isLt; omega⟩

theorem ready_entry (L : Launch) (cta : Nat) (slot : Fin 2) :
    IndexRing.initTable.loc L cta (readyEntry slot) = ready L cta slot ∧
      initCount (readyEntry slot) = 1 := by
  fin_cases slot <;> exact ⟨rfl, rfl⟩

theorem free_entry (L : Launch) (cta : Nat) (slot : Fin 2) :
    IndexRing.initTable.loc L cta (freeEntry slot) = free L cta slot ∧
      initCount (freeEntry slot) = 128 := by
  fin_cases slot <;> exact ⟨rfl, rfl⟩

private theorem first_record {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta : Nat} {j : Fin 23} {m : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hl : IndexRing.initTable.loc L cta j = m)
    (huser : ∀ r ∈ X.objects m, (∀ n, r.action ≠ .init n) →
      ∃ init, X.MbInit init m (initCount j) ∧ baseCausality L X init r.id.issuer) :
    PairTmaRing.InitFirst X m (initCount j) := by
  obtain ⟨init, hInit⟩ := actual_init_sites hpre hX hs
  subst m
  apply IndexRing.published_init_first hX hInit cta j
  intro r hr hn
  obtain ⟨a, hMb, hBefore⟩ := huser r hr hn
  have ha := (hInit j cta a _ _ trivial hMb.choose_spec).1
  rw [← ha]
  exact ⟨hMb, .inl hBefore⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {cta : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- The actual first ready record initializes one arrival. -/
theorem actual_ready_init_first (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    PairTmaRing.InitFirst X (ready L cta slot) 1 := by
  let j := readyEntry slot
  obtain ⟨hl, hc⟩ := ready_entry L cta slot
  rw [← hc]
  apply first_record hpre hX hs hl
  intro r hr hn
  have arrival {n tx : Nat} (ha : r.action = .arrive n tx) :
      ∃ init, X.MbInit init (ready L cta slot) (initCount j) ∧
        baseCausality L X init r.id.issuer := by
    obtain ⟨_, _, g, i, e, d, hid, he, hk, hCta, _, _, _⟩ :=
      actual_ready_arrival_record hpre hX hs hr ha
    obtain ⟨init, hInit, hBefore⟩ := table_init_before_actual_arrive hpre hX hs he hk j
    rw [hCta, hl] at hInit
    rw [hid]
    exact ⟨init, hInit, hBefore⟩
  have completion {n : Nat} (ha : r.action = .completeTx n) :
      ∃ init, X.MbInit init (ready L cta slot) (initCount j) ∧
        baseCausality L X init r.id.issuer := by
    obtain ⟨_, g, i, e, a, sp, d, k, hid, he, _, _, hCta, _, _, _, _, hState⟩ :=
      actual_gather_record hpre hX hs hr ha
    obtain ⟨init, hInit, hBefore⟩ := completed_init_before_followed_role
      hpre hX hs he hState (by intro s h; cases h) j
    change X.MbInit init (IndexRing.initTable.loc L (ctaOf L g) j) (initCount j) at hInit
    rw [hCta, hl] at hInit
    rw [hid]
    exact ⟨init, hInit, hBefore⟩
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact (hn _ ha).elim
  | wait hid he _ =>
    obtain ⟨hCta, init, hInit, hBefore⟩ :=
      table_init_before_actual_poll hpre hX hs he rfl j
    change cta = _ at hCta
    rw [← hCta, hl] at hInit
    rw [hid]
    exact ⟨init, hInit, hBefore⟩
  | arrive _ _ ha | commit _ _ _ ha | arriveOn _ _ _ _ ha => exact arrival ha
  | tensor _ _ _ ha | bulk _ _ _ _ ha | clc _ _ _ _ ha => exact completion ha
  | inval _ _ ha => exact ((objects_single_lifetime hX _) r hr ha).elim
  | increment _ he _ => exact (no_async_arrive hX he rfl).elim

/-- The actual first free record initializes 128 arrivals. -/
theorem actual_free_init_first (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    PairTmaRing.InitFirst X (free L cta slot) 128 := by
  let j := freeEntry slot
  obtain ⟨hl, hc⟩ := free_entry L cta slot
  rw [← hc]
  apply first_record hpre hX hs hl
  intro r hr hn
  cases actual_free_sources hpre hX hs r hr with
  | init ha => exact (hn _ ha).elim
  | poll hid he _ =>
    obtain ⟨hCta, init, hInit, hBefore⟩ :=
      table_init_before_actual_poll hpre hX hs he rfl j
    change cta = _ at hCta
    rw [← hCta, hl] at hInit
    rw [hid]
    exact ⟨init, hInit, hBefore⟩
  | arrive hid _ he _ =>
    obtain ⟨_, _, _, _, hCta, _, _⟩ := actual_raw_free_arrive hpre hX hs he rfl
    obtain ⟨init, hInit, hBefore⟩ := table_init_before_actual_arrive hpre hX hs he rfl j
    rw [hCta, hl] at hInit
    rw [hid]
    exact ⟨init, hInit, hBefore⟩

/-- The first ready record in a fully followed execution. -/
theorem ready_init_first (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) :
    PairTmaRing.InitFirst X (ready L cta slot) 1 :=
  actual_ready_init_first hpre hX (fun _ hg => Machine.code_sound hpre hg)

/-- The raw-free object is the dequantizer's 128-arrival unit object. -/
theorem free_obj (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    Unit.Obj X (free L cta slot) 128 (consumer L cta) 1 where
  pos := by decide
  inj := consumer_inj L cta
  src := free_sources hpre hX hs ht
  init := actual_free_init_first hpre hX (fun _ hg => Machine.code_sound hpre hg)
  noInval := objects_single_lifetime hX _
  parity := by
    intro g i _ p _ _ he
    have hg := Frame.lt_of_get hX he
    obtain ⟨_, _, hc, d, hb, hd, hp, hst⟩ := reuse_source hpre hX (hs g hg) ht he rfl
    have hcount := TmaRawTrace.composed_reuse_count hpre
      ((hs g hg).produces (hX.thr g hg)) hst hd
    rw [hc, hb] at hcount
    change PTX.Flow.okPolls (free L cta slot) ((X.tr g).take i) = _ at hcount
    rw [hcount, hp]
    omega
  δ_le := by decide

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawRing
