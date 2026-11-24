-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Def
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Lanes
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Observed
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Bytes
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias loads end before their CTA's exit

The lane 0 of each softmax warp polls for every group of its stage (`bias_polled`), and the poll
observes both copies of the group (`bias_observes`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Life
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The bias loads end before their CTA's exit.** -/
theorem bias_loads_finished (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) : BiasLoadsFinished L kernel Assumptions.all X := by
  rintro ⟨g, k⟩ a sp ⟨pc, he⟩ ⟨st, hst, hm⟩ hx
  simp only at hm hx ⊢
  obtain ⟨t, rfl⟩ : ∃ t : Fin 2, st = t.val := ⟨⟨st, hst⟩, rfl⟩
  replace hm : sp.mbar = bF L g t := hm
  have hg := Frame.lt_of_get hX he
  have hb := hp.block
  -- a lane of the stage
  obtain ⟨h, hh⟩ : ∃ h, SoftIn L g t.val h := by
    have hc : (g / L.block * L.block + 128 * t.val) / L.block = g / L.block := by
      rw [hb]; omega
    have hw : Prologue.warpIndex L (g / L.block * L.block + 128 * t.val) = 4 * t.val := by
      simp only [Prologue.warpIndex, hb]; omega
    exact ⟨_, thread_lt_of_cta hg hc, hc, by omega, by omega⟩
  obtain ⟨pcx, hxh⟩ := exit_of_exited hx hh.1 hh.2.1
  have hlt := bias_polled hp hX hFw he hm rfl hh hxh
  obtain ⟨j, pcj, par, acq, sc, -, hje, hjn⟩ := nth_poll (X := X) (g := h) (l := bF L g t) hlt
  obtain ⟨hgt, -⟩ := tma_copy hp hX hFw (g := g) (b_tmaOff t) he hm
  have hmod : ((X.tr g).take k).countP (issuesTo (bF L g t)) % 2 < 2 := Nat.mod_lt _ (by omega)
  obtain ⟨i, pci, al, sp', hi', hm', hcnt, -, hob⟩ :=
    bias_observes hp hX hFw (tmaBytes hp hX hFw) hh hje hjn ⟨_, hmod⟩
  rw [← hgt] at hi' hcnt hob
  obtain rfl := nthEv_unique (p := issuesTo (bF L g t)) hi' (by simp [issuesTo, hm']) he
    (by simp only [issuesTo, decide_eq_true_eq]; exact hm)
    (hcnt.trans (Nat.div_add_mod _ 2))
  obtain ⟨o, ho, hnot⟩ := observed_load hX hob
  exact of_observed hX (i := (g, i)) (q := .notify .load) (c := g / L.block) ⟨o, ho, hnot⟩
    hh.1 hh.2.1 hje hob hx

end PTX.Kernels.TmlFa4Fwd.Proof.Life
