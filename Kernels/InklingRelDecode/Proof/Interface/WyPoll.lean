-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SyncFacts
public import Kernels.InklingRelDecode.Proof.Thread.ShapeSmWait
public import Kernels.InklingRelDecode.Proof2.Safety.InitAll
public import Kernels.InklingRelDecode.Proof.Safety.Barriers
public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmEvents
public import Lemmas.Protocol.UnitReachBlocker

@[expose] public section

/-!
# The polls from the state: the object, the parity, the object's final state

What the progress layer's polls take from the thread and protocol layers, in terms of abstract
states (no position, no register):

* `PollAt L g s m par`: the object and the parity a state at one of the six poll sites polls:
  the softmax region's `waitS` (`s_ready (i % 2)`, parity `(i / 2) % 2`) and `waitO` (`o_done`,
  `(i + 1) % 2`), the loader's `wait` (`kv_empty (i % 3)`, `1 - (i / 3) % 2`), the MMA warp's
  `kvWait` (`kv_ready (i % 3)`, `(i / 3) % 2`) and `pWait` (`p_ready ((i - 1) % 2)`,
  `((i - 1) / 2) % 2`), the epilogue's `wait` (`o_final`, 0).
* `poll_site`: a state whose instruction is an `mbarrier.try_wait` is at one of the six sites,
  and every continuing event fired from it polls the object `PollAt` names with its parity, with
  acquire semantics at CTA scope, at one position (the template-level counterpart of
  `wait_event_state`, from the same shape lemmas).
* `pollAt_bar`: the object is a barrier of the thread's CTA.
* `pollAt_final_of`: it has a final state once some thread of the CTA has a barrier-1 event
  followed by another event: its initialization exists (`Bar.reached_B`, `Bar.find_init`) and is
  its first record (`Bar.ctaInit`), and a history initialized first with a record has a final
  state (`MbarRing.Unit.final_of_init`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The object and parity a state at a poll site polls.** -/
def PollAt (L : Launch) (g : Nat) : TSt → Loc → Nat → Prop
  | .d (.sm d), m, p => (d.site = .waitS ∧ m = EvW.sReady L (g / L.block) (d.i % 2) ∧
      p = d.i / 2 % 2) ∨
    (d.site = .waitO ∧ m = EvW.oDone L (g / L.block) ∧ p = (d.i + 1) % 2)
  | .w (.loader d _), m, p => d.site = .wait ∧ m = EvW.kvEmpty L (g / L.block) (d.i % 3) ∧
      p = 1 - d.i / 3 % 2
  | .w (.mma d _), m, p => (d.site = .kvWait ∧ m = EvW.kvReady L (g / L.block) (d.i % 3) ∧
      p = d.i / 3 % 2) ∨
    (d.site = .pWait ∧ m = EvW.pReady L (g / L.block) ((d.i - 1) % 2) ∧ p = (d.i - 1) / 2 % 2)
  | .d (.epi d), m, p => d.site = .wait ∧ m = EvW.oFinal L (g / L.block) ∧ p = 0
  | _, _, _ => False

/-- **The shape of a poll from the state**: a state whose instruction is an `mbarrier.try_wait`
is at one of the six poll sites, and every continuing event fired from it polls the object
`PollAt` names, with its parity, with acquire semantics at CTA scope, at one position. -/
theorem poll_site (hpre : Pre Q L mem0) (hrg : LdRng Q L X) (hg : g < L.threads) {k : Nat}
    {s : TSt}
    (hσ : St Q L X g k = some (some s)) {ins : Instr} (hc : kernel.code[TSt.pc s]? = some ins)
    (hop : isWaitOp ins.op = true) :
    ∃ m pcw par, PollAt L g s m par ∧ ∀ e u,
      (threadCode L g Q).toMachine.Fired (some s) e (some u) →
        ∃ ok, e = ⟨pcw, .wait m par ok true .cta⟩ := by
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
      refine ⟨_, d.site.pc, _, ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
      obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
      have h := EvW.loader_shape hpre hr.2 (hrg hg hσ) ⟨t', ⟨ha, hi.2⟩, hf'⟩
      unfold EvW.LdShape at h
      rw [hs] at h ⊢
      exact h
    | mma d P =>
      have hs : d.site = .kvWait ∨ d.site = .pWait := by simpa using mma_wait d.site hpw
      rcases hs with hs | hs
      · refine ⟨_, d.site.pc, _, .inl ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
        obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
        have h := EvW.mma_shape hpre hg ⟨t', ⟨ha, hi.2⟩, hf'⟩
        unfold EvW.MmShape at h
        rw [hs] at h ⊢
        exact h
      · refine ⟨_, d.site.pc, _, .inr ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
        obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
        have h := EvW.mma_shape hpre hg ⟨t', ⟨ha, hi.2⟩, hf'⟩
        unfold EvW.MmShape at h
        rw [hs] at h ⊢
        exact h
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (fun h => by simpa using dstart_wait d.site h)
    | pro d => exact absurd hpw (fun h => by simpa using pro_wait d.site h)
    | sm d =>
      have hs : d.site = .waitS ∨ d.site = .waitO := by simpa using sm_wait d.site hpw
      rcases hs with hs | hs
      · refine ⟨_, Sm.evPc d.site, _, .inl ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
        obtain ⟨ok, he⟩ := Sm.shape_waitS_loc (Sm.sharedOk_of_pre hpre) (fired_sm hF) hs
        exact ⟨ok, by rw [he, SO.loc_sReadyOf]⟩
      · refine ⟨_, Sm.evPc d.site, _, .inr ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
        obtain ⟨ok, he⟩ := Sm.shape_waitO (Sm.sharedOk_of_pre hpre) (fired_sm hF) hs
        exact ⟨ok, by rw [he]; rfl⟩
    | epi d =>
      have hs : d.site = .wait := by simpa using epi_wait d.site hpw
      have hsb : L.sharedBase + 213340 ≤ 2 ^ 18 := hpre.sharedRange
      refine ⟨_, Epi.evPc d.site, _, ⟨hs, rfl, rfl⟩, fun e u hF => ?_⟩
      obtain ⟨ok, he⟩ := Epi.shape_wait_oFinal hsb hr.2 (fired_epi hF) hs
      exact ⟨ok, by rw [he, SO.loc_oFinal]⟩

/-- **The polled object is a barrier of the thread's CTA.** -/
theorem pollAt_bar {s : TSt} {m : Loc} {par : Nat} (h : PollAt L g s m par) :
    ∃ b : EvD.Bar, m = b.loc L (g / L.block) := by
  cases s with
  | w s =>
    cases s with
    | loader d P =>
      obtain ⟨-, rfl, -⟩ := h
      exact ⟨.kvEmpty ⟨d.i % 3, Nat.mod_lt _ (by decide)⟩, rfl⟩
    | mma d P =>
      rcases h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
      · exact ⟨.kvReady ⟨d.i % 3, Nat.mod_lt _ (by decide)⟩, rfl⟩
      · exact ⟨EvD.pReadyOf (d.i - 1), (SO.loc_pReadyOf L _ _).symm⟩
    | _ => exact h.elim
  | d s =>
    cases s with
    | sm d =>
      rcases h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
      · exact ⟨EvD.sReadyOf d.i, (SO.loc_sReadyOf L _ _).symm⟩
      · exact ⟨.oDone, (SO.loc_oDone L _).symm⟩
    | epi d =>
      obtain ⟨-, rfl, -⟩ := h
      exact ⟨.oFinal, (SO.loc_oFinal L _).symm⟩
    | _ => exact h.elim

/-- **The polled object has a final state**, given a barrier-1 event of the thread followed by
another of its events. -/
theorem pollAt_final_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hg : g < L.threads) {j : Nat}
    (hb1 : 1 ≤ b1N X g j) (hj : j < (X.tr g).length) {s : TSt} {m : Loc} {par : Nat}
    (h : PollAt L g s m par) :
    ∃ before, MBarrier.stateBefore (X.objects m) (X.objects m).length = some before := by
  have hgrid : g / L.block < L.grid := by
    unfold Launch.threads at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  obtain ⟨b, rfl⟩ := pollAt_bar h
  have hfirst := Proof2.all_initFirst hpre hX (g / L.block) b
  have hni : MBarrier.NoInval (X.objects (b.loc L (g / L.block))) :=
    AsyncCopy.objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => Safety.no_inval hX he) _
  obtain ⟨jb, rfl⟩ := Proof2.bar_idx b
  obtain ⟨t, k1, htc, hinit⟩ := Proof2.init_exists_c1 hpre hX hj hb1 jb
  simp only [Proof2.initEv, htc] at hinit
  obtain ⟨i, r, hr, -⟩ := init_record_of_actual_get hX hinit
  exact MbarRing.Unit.final_of_init hX hfirst hni
    (List.ne_nil_of_mem (List.mem_of_getElem? hr))

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
