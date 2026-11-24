-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingActualMbarInit
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # Checked object histories of the GEMM pipeline -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy MBarrier PTX.Flow

/-- All ways to add a record to one GEMM barrier after dispatch. -/
inductive RecordSource (P : Params) (L : Launch) (X : Execution) (cta : Nat) (slot : Fin 2)
    (obj : Object) (r : Record Ref) : Prop
  | init {n : Nat} (ha : r.action = .init n)
  | poll {g i parity : Nat} {ok : Bool} {e : Event} {sc : MbarScope}
      (hid : r.id = .thread (g, i)) (he : X.get (g, i) = some e)
      (hk : e.kind = .wait (obj.loc L cta slot) parity ok true sc)
      (ha : r.action = .pollParity parity ok) (hrole : Poller P L X g i cta parity slot obj)
  | publish {g i : Nat} {e : Event}
      (hid : r.id = .thread (g, i)) (he : X.get (g, i) = some e)
      (hk : e.kind = .arrive (obj.loc L cta slot) 0 1 true .cta)
      (ha : r.action = .arrive 1 0) (hrole : Publisher P L X g i cta slot obj)
  | notify {g i : Nat} {e : Event} {sp : TcCommit.Spec} {rank : Fin 16} {d : Wg1Mma.D}
      (hid : r.id = .async (g, i) (.tcNotify rank)) (he : X.get (g, i) = some e)
      (hk : e.kind = .tc (.commit sp)) (hm : sp.mbar = obj.loc L cta slot)
      (ht : TcCommit.target sp rank = some (obj.loc L cta slot)) (ha : r.action = .arrive 1 0)
      (hc : ctaOf L g = cta) (hb : d.i % 2 = slot.val)
      (hd : (obj = .qkDone ∧ d.site = .qkCommit) ∨ (obj = .svDone ∧ d.site = .pvCommit))
      (hst : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))

theorem actual_gemm_no_completion {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta n : Nat} {slot : Fin 2} {obj : Object} {r : Record Ref}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hr : r ∈ X.objects (obj.loc L cta slot)) (ha : r.action = .completeTx n) : False := by
  obtain ⟨⟨g, i⟩, e, a, sp, _, he, hk, hm, _⟩ := object_completion_source hX hr ha
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, hf⟩ := RingSourceSites.fired_at_followed hX (hs g hg).machine
    (MachineTracking.actual_tensor_issue_followed hpre hX hs he hk) he (by
      intro f hf
      rw [hk] at hf
      cases hf)
  have hb := slot.isLt
  rcases RingTensorEvents.issue_source hpre hf hk with hq | ⟨d, _, _, _, _, _, hraw, _⟩
  · have ho := congrArg Loc.addr (hm.symm.trans hq)
    change L.sharedBase + (obj.base + 8 * slot.val) = L.sharedBase + 222776 at ho
    cases obj <;> simp only [Object.base] at ho <;> omega
  · have ho := congrArg Loc.addr (hm.symm.trans hraw)
    change L.sharedBase + (obj.base + 8 * slot.val) =
      L.sharedBase + (222808 + 8 * (d.block % 2)) at ho
    cases obj <;> simp only [Object.base] at ho <;> omega

/-- Every operation comes from the prologue, an exact role event, or a commit notification. -/
theorem sources {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta : Nat} {slot : Fin 2} {obj : Object}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    ∀ r ∈ X.objects (obj.loc L cta slot), RecordSource P L X cta slot obj r := by
  intro r hr
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact .init ha
  | wait hid he ha =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨hp, rfl⟩ := poll hpre hX (hs _ hg) ht he rfl
    exact .poll hid he rfl ha hp
  | arrive hid he ha =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨hp, rfl, rfl, rfl, rfl⟩ := arrival hpre hX (hs _ hg) ht he rfl
    exact .publish hid he rfl ha hp
  | inval _ _ ha => exact ((objects_single_lifetime hX _) r hr ha).elim
  | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
  | tensor _ _ _ ha | bulk _ _ _ _ ha | clc _ _ _ _ ha =>
    exact (actual_gemm_no_completion hpre hX (fun _ hg => Machine.code_sound hpre hg) hr ha).elim
  | @commit id _ _ _ hid he htarget ha =>
    obtain ⟨g, i⟩ := id
    have hg := Frame.lt_of_get hX he
    obtain ⟨hm, hc, d, hb, hd, hst⟩ := notification hpre hX (hs g hg) ht he rfl htarget
    exact .notify hid he rfl hm htarget ha hc hb hd hst

/-- The hardware initialization allocates 128 native releases or a single commit notification. -/
def Object.count : Object → Nat
  | .dequantReady | .soReady => 128
  | .qkDone | .svDone => 1

private def Object.initEntry (obj : Object) (slot : Fin 2) : Fin 23 :=
  ⟨(match obj with
      | .dequantReady => 3
      | .qkDone => 6
      | .soReady => 7
      | .svDone => 8) + 6 * slot.val,
    by have := slot.isLt; cases obj <;> simp <;> omega⟩

private theorem Object.init_entry (obj : Object) (L : Launch) (cta : Nat) (slot : Fin 2) :
    IndexRing.initTable.loc L cta (obj.initEntry slot) = obj.loc L cta slot ∧
      initCount (obj.initEntry slot) = obj.count := by
  cases obj <;> fin_cases slot <;> exact ⟨rfl, rfl⟩

/-- Every actual GEMM barrier operation follows the initialization of its object's table word. -/
theorem actual_gemm_init_first {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta : Nat} {slot : Fin 2} {obj : Object}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    PairTmaRing.InitFirst X (obj.loc L cta slot) obj.count := by
  let j := obj.initEntry slot
  let m := obj.loc L cta slot
  obtain ⟨hl, hn⟩ := obj.init_entry L cta slot
  obtain ⟨init, hInit⟩ := MachineTracking.actual_init_sites hpre hX hs
  rw [← hl, ← hn]
  apply IndexRing.published_init_first hX hInit cta j
  intro r hr hNotInit
  have hm : r ∈ X.objects m := by
    change r ∈ X.objects (obj.loc L cta slot)
    rw [← hl]
    exact hr
  have use_before :
      ∃ a, X.MbInit a (IndexRing.initTable.loc L cta j) (initCount j) ∧
        baseCausality L X a r.id.issuer := by
    cases record_source hX.tma.2.2.1 hm with
    | init _ _ hAct => exact (hNotInit _ hAct).elim
    | wait hid he _ =>
      obtain ⟨hc, a, hMb, hOrder⟩ :=
        MachineTracking.table_init_before_actual_poll hpre hX hs he rfl j
      change cta = _ at hc
      rw [← hc] at hMb
      rw [hid]
      exact ⟨a, hMb, hOrder⟩
    | arrive hid he _ =>
      have hc := (MachineTracking.actual_arrive_fields hX he rfl).2.1
      change cta = _ at hc
      obtain ⟨a, hMb, hBefore⟩ :=
        MachineTracking.table_init_before_actual_arrive hpre hX hs he rfl j
      rw [← hc] at hMb
      rw [hid]
      exact ⟨a, hMb, hBefore⟩
    | @commit id _ _ _ hid he htarget _ =>
      obtain ⟨g, i⟩ := id
      obtain ⟨_, hc, d, _, _, hState⟩ := actual_notification hpre hX hs he rfl htarget
      obtain ⟨a, hMb, hBefore⟩ := MachineTracking.completed_init_before_followed_role
        hpre hX hs he hState (by intro s h; cases h) j
      rw [hc] at hMb
      rw [hid]
      exact ⟨a, hMb, hBefore⟩
    | inval _ _ hAct => exact ((objects_single_lifetime hX _) r hm hAct).elim
    | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
    | tensor _ _ _ hAct | bulk _ _ _ _ hAct | clc _ _ _ _ hAct =>
      exact (actual_gemm_no_completion hpre hX hs hm hAct).elim
  obtain ⟨a, hMb, hBefore⟩ := use_before
  have ha := (hInit j cta a _ _ trivial hMb.choose_spec).1
  rw [← ha]
  exact ⟨hMb, .inl hBefore⟩

/-- The first record is the prologue's published initialization of the chosen slot and count. -/
theorem init_first {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta : Nat} {slot : Fin 2} {obj : Object}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) :
    PairTmaRing.InitFirst X (obj.loc L cta slot) obj.count :=
  actual_gemm_init_first hpre hX (fun _ hg => Machine.code_sound hpre hg)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
