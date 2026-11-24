-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbTma

public section

/-! # Length and coordinate read extensions of the gather producer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof

/-- The gather producer reads either an optional length or an element of a coordinate vector. -/
inductive GatherRead : Wg1Tma.Site → Prop where
  | lenOrig : GatherRead .lenOrig
  | lenExtra : GatherRead .lenExtra
  | coord (k : Fin 16) (j : Fin 4) : GatherRead (.coord k j)

/-- At every gather input site a released lane can append the actual read. -/
theorem tma_read_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg1Tma.D} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hSafe : ¬ Unsafe L kernel Assumptions.all mem0 X)
    (hp : Frame.Pending L X g) (hRel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.tma d)))
    (hd : GatherRead d.site) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX (fun hub => hSafe (.inl hub)) hp
  obtain ⟨u, ins, hTau, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  have hOk := UbTma.control_tmpl_ok hpre ha hi hc (fun k hk => by rw [hk] at hd; cases hd)
  change kernel.code[d.site.pc]? = some ins at hc
  generalize hSite : d.site = s at hd
  cases hd with
  | lenOrig =>
    rw [hSite] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_17)
    rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := 3045) (w := 64)
      rfl rfl rfl rfl rfl] at hOk hout
    change out kernel Assumptions.all L g u =
      .ev (loadTmpl Assumptions.all L g u .global true 32 [2962] 3045 0) at hout
    obtain ⟨_, _, hTmpl⟩ := read_nc_of_load (dest := [2962]) hOk
    rw [hTmpl] at hout
    exact nc_extension hX hp.1 (.inl hn) hRel hRun hTau hout
  | lenExtra =>
    rw [hSite] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_18)
    rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := 3047) (w := 64)
      rfl rfl rfl rfl rfl] at hOk hout
    change out kernel Assumptions.all L g u =
      .ev (loadTmpl Assumptions.all L g u .global true 32 [2963] 3047 0) at hout
    obtain ⟨_, _, hTmpl⟩ := read_nc_of_load (dest := [2963]) hOk
    rw [hTmpl] at hout
    exact nc_extension hX hp.1 (.inl hn) hRel hRun hTau hout
  | coord k j =>
    rw [hSite] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (Wg1Tma.coordLoad_code k j))
    rw [Wg1Tma.coord_read_template hpre hSite ha hi] at hout
    exact shared_read_extension hX hp.1 hn hRel hRun hTau hout (sync_guarded hX hSafe)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
