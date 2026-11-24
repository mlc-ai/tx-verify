-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SyncSites

@[expose] public section

/-!
# Barrier events by role

The initializations, arrivals and polls of an execution fire from the states of the thread
machines at the sites `SyncSites` lists, with the shapes of those sites, in terms of the barriers
by function (`EvD.Bar`: `kvReady`, `kvEmpty`, `sReady`, `pReady`, `oDone`, `oFinal`; the commits
are `MmaFacts`):

* `init_event_state`: the prologue's 12 initializations, count 1;
* `arrive_event_state`: the prologue's `expect_tx` arrivals on `kv_ready j` (65536 bytes), the
  loader's arrival on `kv_ready (i % 3)`, the softmax region's `p_ready` arrival (thread 0);
* `wait_event_state`: the softmax region's `s_ready` poll, the loader's `kv_empty` poll, the MMA
  warp's `kv_ready` and `p_ready` polls, the epilogue's `o_final` poll, and the softmax region's
  `o_done` poll at the site `Sm.Site.waitO`, whose event shape the thread layer does not have
  (`Sm.Shape` is `True` there; a row of "thread-layer gaps").
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The state an event fires from**: a non-ending event of a launched thread of a consistent
execution fires from the state before it, at the instruction of the state's position, and
continues. -/
theorem event_pre (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hne : ¬ Ends e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    ∃ (s : TSt) (t : TState) (ins : Instr) (o : Option TState) (u : TState),
      St Q L X g k = some (some s) ∧ kernel.code[TSt.pc s]? = some ins ∧
      Fires (TSt.pc s) (eventTmpl asms L g t ins.op) e o ∧
      (threadCode L g Q).toMachine.Fired (some s) e (some u) := by
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he hub
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have he' : (X.tr g)[k]? = some e := he
  obtain ⟨o', hF⟩ := (Frame.trace hS hX hg).fired_at he' hσ
  cases o' with
  | none =>
    obtain ⟨t', -, hf'⟩ := hF
    exact absurd (fires_none_ends hf') hne
  | some u => exact ⟨s, t, ins, o, u, hσ, hc, hf, hF⟩

/-- Events whose kind is none of undefined behaviour and exit do not end the thread. -/
theorem not_ends {e : Event} (h1 : ∀ f, e.kind ≠ .ub f) (h2 : e.kind ≠ .exit) : ¬ Ends e := by
  rintro (⟨f, h⟩ | h)
  · exact h1 f h
  · exact h2 h

theorem no_ub_of_kind {e : Event} (h1 : ∀ f, e.kind ≠ .ub f) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  rintro pc f rfl
  exact h1 f rfl

theorem in_index : ∀ s ∈ ProA.inSites, ∃ i < 12, s = ProA.inSite i := by decide

theorem arr_index : ∀ s ∈ ([.arr0, .arr1, .arr2] : List ProA.Site), ∃ j < 3,
    s = ProA.arrSite j := by
  decide

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
include hpre hX hS ht

/-- **A prologue initialization**: the prologue's 12, count 1 on the barrier `initBar i` of the
thread's CTA. -/
theorem init_event_state {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hk : ∃ l c, e.kind = .mbInit l c) :
    ∃ d : ProA.D, St Q L X g k = some (some (.d (.pro d))) ∧ ∃ i < 12,
      d.site = ProA.inSite i ∧
        e = ⟨ProA.evPc d.site, .mbInit ((ProA.initBar i).loc L (g / L.block)) 1⟩ := by
  obtain ⟨l, c, hk⟩ := hk
  obtain ⟨s, t, ins, o, u, hσ, hc, hf, hF⟩ := event_pre hX hS ht hg he
    (not_ends (by intro f h; rw [hk] at h; cases h) (by intro h; rw [hk] at h; cases h))
    (no_ub_of_kind (by intro f h; rw [hk] at h; cases h))
  have hop : initOp ins.op = true := by
    cases hq : initOp ins.op
    · exact absurd hk (notInit_of_op hq hf l c)
    · rfl
  have hpw : TSt.pc s ∈ initPcs := OpPcsFast.mem kernel_init_pcs hc hop
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (fun h => by simpa using worker_init w.site h)
    | idle d => exact absurd hpw (fun h => by simpa using idle_init d.site h)
    | loader d _ => exact absurd hpw (fun h => by simpa using loader_init d.site h)
    | mma d _ => exact absurd hpw (fun h => by simpa using mma_init d.site h)
    | exit x => exact absurd hpw (fun h => by simpa using exit_init x.site h)
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (fun h => by simpa using dstart_init d.site h)
    | sm d => exact absurd hpw (fun h => by simpa using sm_init d.site h)
    | epi d => exact absurd hpw (fun h => by simpa using epi_init d.site h)
    | pro d =>
      obtain ⟨i, hi, hs⟩ := in_index _ (pro_init d.site hpw)
      exact ⟨d, hσ, i, hi, hs, ProA.shape_in (ProA.sharedOk_of_pre hpre) hi (fired_pro hF) hs⟩

/-- **An arrival is the prologue's, the loader's or the softmax region's**, the loader's for every
counter (`EvW.LdShapeW`). -/
theorem arrive_event_stateW {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hk : ∃ l tx c rel sc, e.kind = .arrive l tx c rel sc) :
    (∃ d : ProA.D, St Q L X g k = some (some (.d (.pro d))) ∧ ∃ j < 3,
      d.site = ProA.arrSite j ∧ e = ⟨ProA.evPc d.site,
        .arrive ((EvD.kvReadyOf j).loc L (g / L.block)) 65536 1 true .cta⟩) ∨
    (∃ d : Sm.D, St Q L X g k = some (some (.d (.sm d))) ∧ d.site = .arrive ∧
      g % L.block = 0 ∧ e = ⟨Sm.evPc d.site,
        .arrive ((EvD.pReadyOf d.i).loc L (g / L.block)) 0 1 true .cta⟩) ∨
    (∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
      d.site = .arrive ∧ EvW.LdShapeW Q L g d e) := by
  obtain ⟨l, tx, c, rel, sc, hk⟩ := hk
  obtain ⟨s, t, ins, o, u, hσ, hc, hf, hF⟩ := event_pre hX hS ht hg he
    (not_ends (by intro f h; rw [hk] at h; cases h) (by intro h; rw [hk] at h; cases h))
    (no_ub_of_kind (by intro f h; rw [hk] at h; cases h))
  have hop : arriveOp ins.op = true := by
    cases hq : arriveOp ins.op
    · exact absurd hk (fires_notArrive (eventTmpl_notArrive (arriveOp_ne hq)) hf l tx c rel sc)
    · rfl
  have hpw : TSt.pc s ∈ arrivePcs := OpPcsFast.mem kernel_arrive_pcs hc hop
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (fun h => by simpa using worker_arrive w.site h)
    | idle d => exact absurd hpw (fun h => by simpa using idle_arrive d.site h)
    | mma d _ => exact absurd hpw (fun h => by simpa using mma_arrive d.site h)
    | exit x => exact absurd hpw (fun h => by simpa using exit_arrive x.site h)
    | loader d P =>
      have hs : d.site = .arrive := by simpa using loader_arrive d.site hpw
      have hr := treach_stateAt hpre hg hσ
      obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
      exact .inr (.inr ⟨d, P, hσ, hs, EvW.loader_shapeW hpre hr.2 ⟨t', ⟨ha, hi.2⟩, hf'⟩⟩)
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (fun h => by simpa using dstart_arrive d.site h)
    | epi d => exact absurd hpw (fun h => by simpa using epi_arrive d.site h)
    | pro d =>
      obtain ⟨j, hj, hs⟩ := arr_index _ (pro_arrive d.site hpw)
      exact .inl ⟨d, hσ, j, hj, hs, ProA.shape_arr (ProA.sharedOk_of_pre hpre) hj (fired_pro hF) hs⟩
    | sm d =>
      have hs : d.site = .arrive := by simpa using sm_arrive d.site hpw
      obtain ⟨h1, h2⟩ := Sm.shape_arrive (Sm.sharedOk_of_pre hpre) (fired_sm hF) hs
      exact .inr (.inl ⟨d, hσ, hs, h1, h2⟩)

/-- **An arrival is the prologue's, the loader's or the softmax region's.** -/
theorem arrive_event_state (hrg : LdRng Q L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hk : ∃ l tx c rel sc, e.kind = .arrive l tx c rel sc) :
    (∃ d : ProA.D, St Q L X g k = some (some (.d (.pro d))) ∧ ∃ j < 3,
      d.site = ProA.arrSite j ∧ e = ⟨ProA.evPc d.site,
        .arrive ((EvD.kvReadyOf j).loc L (g / L.block)) 65536 1 true .cta⟩) ∨
    (∃ d : Sm.D, St Q L X g k = some (some (.d (.sm d))) ∧ d.site = .arrive ∧
      g % L.block = 0 ∧ e = ⟨Sm.evPc d.site,
        .arrive ((EvD.pReadyOf d.i).loc L (g / L.block)) 0 1 true .cta⟩) ∨
    (∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
      d.site = .arrive ∧ EvW.LdShape Q L g d e) := by
  rcases arrive_event_stateW hpre hX hS ht hg he hk with h | h | ⟨d, P, hσ, hs, hsh⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨d, P, hσ, hs, hsh.shape (EvW.sbOk_of_pre hpre) (hrg hg hσ).bndI⟩)

/-- **A poll is the softmax region's, the loader's, the MMA warp's or the epilogue's**, the
loader's for every counter (`EvW.LdShapeW`). -/
theorem wait_event_stateW {g k : Nat} {e : Event} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hk : ∃ l p ok acq sc, e.kind = .wait l p ok acq sc) :
    (∃ d : Sm.D, St Q L X g k = some (some (.d (.sm d))) ∧
      ((d.site = .waitS ∧ ∃ ok, e = ⟨Sm.evPc d.site, .wait ((EvD.sReadyOf d.i).loc L (g / L.block))
        (d.i / 2 % 2) ok true .cta⟩) ∨ d.site = .waitO)) ∨
    (∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
      d.site = .wait ∧ EvW.LdShapeW Q L g d e) ∨
    (∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      (d.site = .kvWait ∨ d.site = .pWait) ∧ EvW.MmShape L g d e) ∨
    (∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ d.site = .wait ∧
      ∃ ok, e = ⟨Epi.evPc d.site, .wait (EvD.Bar.loc L (g / L.block) .oFinal) 0 ok true .cta⟩) := by
  obtain ⟨l, p, ok, acq, sc, hk⟩ := hk
  obtain ⟨s, t, ins, o, u, hσ, hc, hf, hF⟩ := event_pre hX hS ht hg he
    (not_ends (by intro f h; rw [hk] at h; cases h) (by intro h; rw [hk] at h; cases h))
    (no_ub_of_kind (by intro f h; rw [hk] at h; cases h))
  have hop : isWaitOp ins.op = true := by
    cases hq : isWaitOp ins.op
    · exfalso
      refine fires_notWait (eventTmpl_notWait ?_) hf l p ok acq sc hk
      intro p' b o' par a' s' h
      simp [isWaitOp, h] at hq
    · rfl
  have hpw : TSt.pc s ∈ waitPcs := OpPcsFast.mem kernel_wait_pcs hc hop
  have hr := treach_stateAt hpre hg hσ
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (fun h => by simpa using worker_wait w.site h)
    | idle d => exact absurd hpw (fun h => by simpa using idle_wait d.site h)
    | exit x => exact absurd hpw (fun h => by simpa using exit_wait x.site h)
    | loader d P =>
      have hs : d.site = .wait := by simpa using loader_wait d.site hpw
      obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
      exact .inr (.inl ⟨d, P, hσ, hs, EvW.loader_shapeW hpre hr.2 ⟨t', ⟨ha, hi.2⟩, hf'⟩⟩)
    | mma d P =>
      have hs : d.site = .kvWait ∨ d.site = .pWait := by simpa using mma_wait d.site hpw
      obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
      exact .inr (.inr (.inl ⟨d, P, hσ, hs, EvW.mma_shape hpre hg ⟨t', ⟨ha, hi.2⟩, hf'⟩⟩))
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (fun h => by simpa using dstart_wait d.site h)
    | pro d => exact absurd hpw (fun h => by simpa using pro_wait d.site h)
    | sm d =>
      have hs : d.site = .waitS ∨ d.site = .waitO := by simpa using sm_wait d.site hpw
      rcases hs with hs | hs
      · exact .inl ⟨d, hσ, .inl ⟨hs, Sm.shape_waitS_loc (Sm.sharedOk_of_pre hpre) (fired_sm hF) hs⟩⟩
      · exact .inl ⟨d, hσ, .inr hs⟩
    | epi d =>
      have hs : d.site = .wait := by simpa using epi_wait d.site hpw
      have hsb : L.sharedBase + 213340 ≤ 2 ^ 18 := hpre.sharedRange
      exact .inr (.inr (.inr ⟨d, hσ, hs,
        Epi.shape_wait_oFinal hsb hr.2 (fired_epi hF) hs⟩))

/-- **A poll is the softmax region's, the loader's, the MMA warp's or the epilogue's.** -/
theorem wait_event_state (hrg : LdRng Q L X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hk : ∃ l p ok acq sc, e.kind = .wait l p ok acq sc) :
    (∃ d : Sm.D, St Q L X g k = some (some (.d (.sm d))) ∧
      ((d.site = .waitS ∧ ∃ ok, e = ⟨Sm.evPc d.site, .wait ((EvD.sReadyOf d.i).loc L (g / L.block))
        (d.i / 2 % 2) ok true .cta⟩) ∨ d.site = .waitO)) ∨
    (∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
      d.site = .wait ∧ EvW.LdShape Q L g d e) ∨
    (∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      (d.site = .kvWait ∨ d.site = .pWait) ∧ EvW.MmShape L g d e) ∨
    (∃ d : Epi.D, St Q L X g k = some (some (.d (.epi d))) ∧ d.site = .wait ∧
      ∃ ok, e = ⟨Epi.evPc d.site, .wait (EvD.Bar.loc L (g / L.block) .oFinal) 0 ok true .cta⟩) := by
  rcases wait_event_stateW hpre hX hS ht hg he hk with h | ⟨d, P, hσ, hs, hsh⟩ | h | h
  · exact .inl h
  · exact .inr (.inl ⟨d, P, hσ, hs, hsh.shape (EvW.sbOk_of_pre hpre) (hrg hg hσ).bndI⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
