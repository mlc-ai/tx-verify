-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteRegs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantTileBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate
import Lemmas.TensorStore.TensorStoreThread
import Lemmas.Flow.TcTmpl

@[expose] public section

/-! # Actual output stores use the launch's O descriptor -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def outputRegion (pc : Nat) : Bool := decide (1198 ≤ pc ∧ pc ≤ 1831)

set_option maxRecDepth 100000 in
private theorem output_address_audit : registerRegionChecked 3832 outputRegion [1197] = true := by
  decide +kernel

private def OutputAddress (P : Params) (L : Launch) (g : Nat) (d : Wg0.D) (t : TState) : Prop :=
  SoftmaxWriteState (fun r => some (Wg0.valueOf P L g d r)) t ∧
    (outputRegion t.pc = true → t.regs 3832 = some (b64 (P.param1Base + 512)))

set_option maxRecDepth 100000 in
private theorem output_address_tau {d : Wg0.D} {t u : TState}
    (hpre : Pre P L mem0) (hState : OutputAddress P L g d t)
    (hTau : Tau kernel Assumptions.all L g t u) : OutputAddress P L g d u := by
  refine ⟨softmax_write_tau hState.1 hTau, register_region_tau
    (property := fun v => v = some (b64 (P.param1Base + 512)))
    output_address_audit hState.2 ?_ hTau⟩
  intro hUpdate _
  have hPc : t.pc = 1197 := List.mem_singleton.mp hUpdate
  have hReg := hState.1.2 3001 (by decide) (by rw [hPc]; decide)
  have hPtr : t.regs 3001 = some (.ptr 64 true (.param (param "1")) 0) := by
    simpa [Wg0.valueOf, Wg0.table, lookupLit] using hReg
  have hExec := paramAdd_exec (g := g) (d := 3832) (k := 512)
    hPc (by decide) hPtr hpre.param1Object (by decide)
  let v := PTX.next (setReg t 3832 (b64 (P.param1Base + 512)))
  have hRun : run kernel Assumptions.all L g 1 t = some v := by
    simp only [run, tauStep, out, tau_fault_free hTau, hPc, Flow.code_1197,
      guardHolds, Op.isLocal, hExec, v, b64]
    rfl
  exact (one_step_matches hTau hRun) ▸ (by simp [v, PTX.next, setReg])

private theorem output_address_event {d : Wg0.D} {t u : TState} {e : Event}
    (hState : OutputAddress P L g d t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    OutputAddress P L g d u := by
  refine ⟨softmax_write_event hState.1 he, register_region_event
    (property := fun v => v = some (b64 (P.param1Base + 512)))
    output_address_audit (register_updates_local (by decide +kernel)) hState.2 he⟩

private def outputSites : List Nat := (List.finRange 4).map (fun j => (Wg0.Site.tmaStore j).pc)

set_option maxRecDepth 100000 in
private theorem output_sites : OpPcsFast kernel.code tensorStoreOp outputSites = true := by
  decide +kernel

private theorem fired_output_descriptor {pc addr : Nat} {j : Fin 4} {t : TState}
    {e : Event} {o : Option TState} {s : TensorStore.Spec}
    (hpre : Pre P L mem0) (hr : t.regs 3832 = some (b64 (P.param1Base + 512)))
    (hf : Fires pc (eventTmpl Assumptions.all L g t (Wg0.outputTmaOp j)) e o)
    (hk : e.kind = .tensorStore addr s) :
    (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨3, mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass⟩ := by
  have hRange := hpre.param1Range
  have hMapAddr : tensorMapAddress L g t (.reg 3832) = .ok (P.param1Base + 512) := by
    simp [tensorMapAddress, readValue, readReg, hr, b64, readBits, truncBits, bind,
      Except.bind, pure, Except.pure]
    omega
  unfold Wg0.outputTmaOp at hf
  simp only [eventTmpl, tensorStoreTmpl] at hf
  generalize hSpec : tensorStoreSpec L g t (.reg 3832)
    [.reg ([1914, 2083, 2252, 2422].getD j.val 0),
      .reg ([1915, 2084, 2253, 2423].getD j.val 0), .reg 459, .reg 460]
    ([1913, 2082, 2251, 2421].getD j.val 0) 0 none .tile none = result at hf
  cases result with
  | error why =>
    simp only [ofExec, bind, Except.bind, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok pair =>
    obtain ⟨a, spec⟩ := pair
    change Fires pc (.tensorStore a spec (PTX.next t)) e o at hf
    have hKind : e.kind = .tensorStore a spec := congrArg Event.kind hf.1
    have hEq := (Kind.tensorStore.inj (hk.symm.trans hKind)).2
    subst spec
    obtain ⟨hAddr, desc, hMap, _, hDesc, _, _⟩ := tensorStoreSpec_ok hSpec
    rw [hMapAddr] at hAddr
    cases hAddr
    rw [hpre.mapOBind] at hMap
    change s.descriptor = desc at hDesc
    exact (congrArg (⟨s.outer, ·⟩ : TensorDescriptor.Descriptor s.outer →
      Σ n, TensorDescriptor.Descriptor n) hDesc).trans (Option.some.inj hMap).symm

private theorem output_descriptor_after_mask {start i addr : Nat} {d : Wg0.D} {e : Event}
    {s : TensorStore.Spec} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hMask : d.site = .maskReady)
    (hState : Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 d)))
    (hLe : start ≤ i) (he : X.get (g, i) = some e) (hk : e.kind = .tensorStore addr s) :
    (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨3, mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass⟩ := by
  have hGet : ((X.tr g).drop start)[i - start]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hLe]
    exact he
  have hm := List.mem_of_getElem? hGet
  obtain ⟨t, o, hSoft, hp, hRun⟩ := softmax_write_suffix hX hs (Frame.lt_of_get hX he)
    hMask hState (List.ne_nil_of_mem hm)
  have hInitial : OutputAddress P L g d t := ⟨hSoft, by rw [hp]; nofun⟩
  obtain ⟨u, q, hAt, hStep⟩ :=
    actual_event_invariant (output_address_tau hpre) output_address_event hInitial hRun hm
  cases q with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    have hBad := fires_none_ends hf
    simp [Ends, hk] at hBad
  | some v =>
    obtain ⟨ins, hc, _, hf⟩ := estep_event_source hStep
    have hkSite := OpPcsFast.mem output_sites hc (fires_tensorStore_op hf hk)
    obtain ⟨j, _, hSite⟩ := List.mem_map.mp hkSite
    have hr := hAt.2 (by rw [← hSite]; fin_cases j <;> decide)
    rw [← hSite, Wg0.outputTma_code j] at hc
    obtain rfl := Option.some.inj hc
    exact fired_output_descriptor hpre hr hf hk

/-- Every issued output tile uses the O descriptor published in the launch, even if its
softmax data guards dismissed the followed role earlier. -/
theorem actual_output_descriptor {i addr : Nat} {e : Event} {s : TensorStore.Spec}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hk : e.kind = .tensorStore addr s) :
    (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨3, mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass⟩ := by
  by_cases hFollow : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨j, hj, role, f, hf, hState, hNext⟩ := prior_dismissal (PTX.len_of_get he).le hFollow
    cases dismissal_is_consumer hpre hX hs hf hState hNext with
    | wg0 d =>
      obtain ⟨start, hLe, first, hMask, _, hFirst⟩ :=
        dismissed_wg0_first_mask_ready hpre hX hs hf hState hNext
      exact output_descriptor_after_mask hpre hX hs hMask hFirst (hLe.trans hj.le) he hk
    | wg2 d =>
      have hPc := Frame.event_pc hs hX hf hState
      have hDq : dequantTileRegion f.pc := by
        have hLate := (dequant_dismissal_is_read hpre hX (hs g (Frame.lt_of_get hX hf)).machine
          hf hState hNext).2.1
        change f.pc = d.site.pc at hPc
        rw [hPc]
        rcases hLate with ⟨r, k, h⟩ | ⟨r, k, h⟩
        · have hScale : ∀ (r k : Fin 4), dequantTileRegion (Wg2.Site.scale r k).pc :=
            by decide +kernel
          rw [h]
          exact hScale r k
        · have hRaw : ∀ (r : Fin 4) (k : Fin 8), dequantTileRegion (Wg2.Site.raw r k).pc :=
            by decide +kernel
          rw [h]
          exact hRaw r k
      have hLater := later_event_in_control_region dequant_tile_region_closed hX
        (Frame.lt_of_get hX he) hf he hj hDq
      rcases get_source hX he with ⟨fault, hBad⟩ | ⟨_, ins, _, _, hc, hFire⟩
      · rw [hBad] at hk
        cases hk
      · have ht := OpPcsFast.mem output_sites hc (fires_tensorStore_op hFire hk)
        obtain ⟨tile, _, ht⟩ := List.mem_map.mp ht
        rw [← ht] at hLater
        have hSmall : ∀ j : Fin 4, ¬ dequantTileRegion (Wg0.Site.tmaStore j).pc :=
          by decide +kernel
        exact (hSmall tile hLater).elim
  · have hi : X.TensorStoreIssue (g, i) addr s := by
      obtain ⟨tag, kind⟩ := e
      cases hk
      exact ⟨tag, he⟩
    obtain ⟨d, j, hState, hSite⟩ :=
      GlobalWrites.outputTile_site_at_followed (i := (g, i)) hs hX hFollow hi
    obtain ⟨t, ins, o, ha, _, hc, hf⟩ := Frame.fired_site hs hX he hState
    change (Wg0.code P L g).AtD d t at ha
    change kernel.code[d.site.pc]? = some ins at hc
    rw [hSite, Wg0.outputTma_code j] at hc
    obtain rfl := Option.some.inj hc
    have hLive : 3832 ∈ (Flow.live d.site.pc).filter Wg0.tracked.contains := by
      have hLive : ∀ j : Fin 4,
          3832 ∈ (Flow.live (Wg0.Site.tmaStore j).pc).filter Wg0.tracked.contains :=
        by decide +kernel
      rw [hSite]
      exact hLive j
    have hr : t.regs 3832 = some (b64 (P.param1Base + 512)) := by
      simpa [Wg0.valueOf, Wg0.table, lookupLit, b64] using Wg0.reg_value ha hLive
    exact fired_output_descriptor hpre hr hf hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
