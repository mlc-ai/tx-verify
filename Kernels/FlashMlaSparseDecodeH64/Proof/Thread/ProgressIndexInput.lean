-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbIndexData

public section

/-! # Issuing the index warp's non-coherent input reads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof Wg1Index

/-- The two optional lengths and each element of an index pair are launch-memory loads. -/
inductive IndexInput : Wg1Index.Site → Prop where
  | lenOrig : IndexInput .lenOrig
  | lenExtra : IndexInput .lenExtra
  | pair (extra first high : Bool) : IndexInput (.pair extra first high)

private theorem index_input_template {P : Params} {L : Launch} {mem0 : Mem0}
    {g : Nat} {d : D} {t : TState} {ins : Instr}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hd : IndexInput d.site)
    (ha : (Machine.code P L g).AtD (.index d) t) (hi : Inv P L g d)
    (hc : kernel.code[(Machine.code P L g).pc (.index d)]? = some ins) :
    ∃ a k, eventTmpl Assumptions.all L g t ins.op = .readNC a k := by
  have hOk := UbIndex.tmpl_ok hpre hg ha hi hc
  change kernel.code[d.site.pc]? = some ins at hc
  generalize hSite : d.site = s at hd
  cases hd with
  | lenOrig =>
    rw [hSite] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2360)
    rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := 3023) (w := 64)
      rfl rfl rfl rfl rfl] at hOk ⊢
    exact read_nc_of_load hOk
  | lenExtra =>
    rw [hSite] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2365)
    rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := 3025) (w := 64)
      rfl rfl rfl rfl rfl] at hOk ⊢
    exact read_nc_of_load hOk
  | pair extra first high =>
    rw [hSite] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (UbIndex.pair_code extra first high))
    rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := (pairOperands extra first).1)
      (w := 64) rfl rfl rfl rfl rfl] at hOk ⊢
    exact read_nc_of_load hOk

/-- A released index lane can read its selected length or the next element of an index pair. -/
theorem index_input_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : D} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hRel : PTX.Step.Released L X g)
    (hSigma : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.index d)))
    (hd : IndexInput d.site) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn : X.tr g ≠ [] := by
    intro hNil
    rw [hNil, List.length_nil, Frame.stateAt_zero] at hSigma
    cases hSigma
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hRun hSigma
  obtain ⟨_, _, hTemplate⟩ := index_input_template hpre hp.1 hd ha hi hc
  rw [hTemplate] at hout
  exact nc_extension hX hp.1 (.inl hn) hRel hRun hTau hout

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
