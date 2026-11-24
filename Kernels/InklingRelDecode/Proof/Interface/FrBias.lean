-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvBias

@[expose] public section

/-!
# The softmax region's bias loads rebuild

`Sm.next` at a bias load (`Sm.Site.pre j`, `Sm.Site.nxt j`) is `none` when the two bytes the load
returned do not rebuild (`rebuild 3 bs = .error _`). A load reads two bytes of `Rel`
(`Sm.shape_pre_spec`, `Sm.shape_nxt_spec`), which are launch bytes of the `bf16` number
`Pre.relInput` gives (`Sv.rel_read_value`), so they rebuild. The statements are the part of
`SvBias.lean` that does not use the value: no premise on the scores.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A preload's bytes rebuild.** -/
theorem rebuild_pre (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {d : D} {e : Event} {j : Fin 64}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hI : Sm.Inv L g d) (hs : d.site = .pre j) :
    ∃ ac bs x, e.kind = .rd ac bs ∧ rebuild 3 bs = .ok x := by
  obtain ⟨-, hm⟩ := hf.reach hg hσ
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨bs, hl, hev⟩ := Sm.shape_pre_spec hpre hm.ent hz hy (fired_sm hF) hs
  obtain ⟨hn, hrv, hit, hnb⟩ := Sm.pre_block hm.ent hI hs
  have hbl : ProA.cta L g .x < Q.blocks (ProA.cta L g .z) := by
    have := Sm.lt_blocks_of_iters (r := ProA.cta L g .z) (s := ProA.cta L g .x) (i := 0)
      hpre.splitsPos hit
    simpa using this
  obtain ⟨htok, hh, hc, -⟩ := Sm.biasAddr_spec hpre hm.ent hz hy hI.tid hrv j.isLt hbl hnb
  exact ⟨_, bs, _, by rw [hev], rel_read_value hpre hX hf hz htok hh hc hl
    (by rw [hev] at he; exact he)⟩

/-- **A loop load's bytes rebuild.** -/
theorem rebuild_nxt (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {d : D} {e : Event} {j : Fin 64}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hI : Sm.Inv L g d) (hs : d.site = .nxt j) :
    ∃ ac bs x, e.kind = .rd ac bs ∧ rebuild 3 bs = .ok x := by
  obtain ⟨-, hm⟩ := hf.reach hg hσ
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨bs, hl, hev⟩ := Sm.shape_nxt_spec hpre hm.ent hz hy (fired_sm hF) hs
  obtain ⟨hn, hrv, hit, hnb⟩ := Sm.nxt_block hm.ent hI hs
  have hbl := Sm.lt_blocks_of_iters hpre.splitsPos hit
  obtain ⟨htok, hh, hc, -⟩ := Sm.biasAddr_spec hpre hm.ent hz hy hI.tid hrv j.isLt hbl hnb
  exact ⟨_, bs, _, by rw [hev], rel_read_value hpre hX hf hz htok hh hc hl
    (by rw [hev] at he; exact he)⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
