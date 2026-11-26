-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Bar12
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.StepPlumb
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.SuccLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EpiRd
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Ok
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceE
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.VoteCmp
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # A complete lane of warpgroup 0 below thread 64 makes its LSE store

The lane's barrier 12 (pc 1835) is made (`wg0_exitBar12`); before each event of pcs 1158 to 1839
there is an event at the row-sum read or later (`w0_pc_step`), and the event after the row-sum
read is the store at pc 1178. The descent from the barrier ends at the store. -/

/-! # The events of the epilogue's tail follow the code's chain

The previous event of an event at pcs 1158 to 1839 is at the row-sum read (pc 1157) or later, and
the event after the row-sum read is the LSE store (`w0_pc_step`). Moved out of `Chain.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0
open Wg0.Data

/-- The row-sum read goes to the LSE store for a thread index word below 64. -/
private theorem succ_eld_lse {c c' : Control.D} {f : Event}
    (h : Control.succ P L g (warpW L g) c f = some (some c')) (hs : c.site = .eld)
    (hb : scmp .ge .s (Control.r5W L g) (pw 64) = false) : c'.site = .lse := by
  simp only [Control.succ, hs, Control.dataRd] at h
  split at h
  all_goals first | (cases h; simp [Control.afterEld, hb]) | (cases h)

/-- **The event before an event of the epilogue's tail** (pcs 1158 to 1839; the lane's thread
index below 64): the previous event is at the row-sum read or later and not after the event, and
the event after the row-sum read is the LSE store. -/
theorem w0_pc_step_hub (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hlow : tidOf L g < 64) {k : Nat} {e' : Event}
    (he' : X.get (g, k) = some e') (hub : ∀ f, e'.kind ≠ .ub f)
    (hv : W0Valid P.scale ((X.tr g).take k)) (hge : 1158 ≤ e'.pc) (hlt : e'.pc < 1840) :
    ∃ j f, k = j + 1 ∧ X.get (g, j) = some f ∧ 1157 ≤ f.pc ∧ f.pc ≤ e'.pc ∧
      (f.pc = 1157 → e'.pc = 1178) := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he' hub
  obtain ⟨d0, n0, hσe, -⟩ := wg0_state hJ hi hev hpc ⟨by omega, by omega⟩
  rcases k with _ | j
  · exfalso
    rw [Frame.stateAt_zero] at hσ
    have h0 := Option.some.inj (Option.some.inj hσ)
    rw [hσe] at h0
    simp [thread, Code.roleThread, Code.enter, Code.gatedExit, startupEnter, Startup.exitOf] at h0
  obtain ⟨st, hst, hslot, hpre, hI, hPrev, -⟩ :=
    followW hp hX hFw hw he' hub (w0_scale_rd hp) hv (j + 1) le_rfl
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpc' := Frame.event_pcU hsD hX he' hst hub
  have hcd := control_of_data hst
  rw [hσ] at hcd
  have hσst : σ = eraseThread P L g st := Option.some.inj (Option.some.inj hcd)
  obtain ⟨q0, n⟩ := st
  rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q0 = .inl b := hb
    rw [hσe] at hσst
    simp [eraseThread, Code.eraseSum] at hσst
  obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
  rcases hPrev d rfl j rfl with ⟨hs, -⟩ | ⟨f, c, hf, hpcf, hsucc, -⟩
  · exfalso
    have : e'.pc = 103 := by
      rw [hpc', show (threadD P L g).pc (.inr ⟨.inl .wg0, d⟩, n) = d.c.site.pc from rfl, hs]
      rfl
    omega
  have hep : e'.pc = d.c.site.pc := hpc'
  refine ⟨j, f, rfl, hf, ?_⟩
  have hs : c.site ≠ .arrS := fun h => by
    rcases Control.succ_arrS hsucc h with hb | hb <;> rw [hb] at hep <;>
      simp [Site.pc] at hep <;> omega
  obtain ⟨h1, h2, h3⟩ := Control.succ_pc_step hsucc hs
  rw [hpcf] at h1 h2 h3
  rw [← hep] at h1 h2 h3
  have h4 : 1157 ≤ f.pc := by
    by_contra hlt'
    rcases h3 (by omega) with h | h <;> omega
  refine ⟨h4, h1, fun h5 => ?_⟩
  have hcs : c.site = .eld := Data.site_pc_1157 (hpcf.trans h5)
  have hb : scmp .ge .s (Control.r5W L g) (pw 64) = false := by
    have e4 : Control.r5W L g = W (tidOf L g % 128) :=
      andi_W_low (k := 7) (tidOf_lt hp g) (by decide)
    have e2 : pw 64 = W 64 := by
      simp only [pw, leNat_eq, pow_zero, Nat.div_one]; rfl
    rw [e4, e2, Nat.mod_eq_of_lt (show tidOf L g < 128 by omega)]
    simp only [scmp, PTX.compare, r32_W (show tidOf L g < 2 ^ 32 by omega),
      r32_W (show 64 < 2 ^ 32 by omega), toSigned, toNat_W (show tidOf L g < 2 ^ 64 by omega),
      toNat_W (show 64 < 2 ^ 64 by omega), decide_eq_false_iff_not]
    split_ifs <;> omega
  have := succ_eld_lse hsucc hcs hb
  rw [hep, this]
  rfl

/-- **The event before an event of the epilogue's tail** (from `¬ HasUb`). -/
theorem w0_pc_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L g < 4) (hv : W0Trace P X g)
    (hlow : tidOf L g < 64) {k : Nat} {e' : Event} (he' : X.get (g, k) = some e')
    (hge : 1158 ≤ e'.pc) (hlt : e'.pc < 1840) :
    ∃ j f, k = j + 1 ∧ X.get (g, j) = some f ∧ 1157 ≤ f.pc ∧ f.pc ≤ e'.pc ∧
      (f.pc = 1157 → e'.pc = 1178) :=
  w0_pc_step_hub hp hX hFw hw hlow he' (noUb_kind hnu he') (hv.take k) hge hlt

end Wg0

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The descent**: an event at pcs 1158 to 1839 has an event at pc 1178 at or before it. -/
theorem w0_descend (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L g < 4) (hv : W0Trace P X g)
    (hlow : tidOf L g < 64) :
    ∀ k e, X.get (g, k) = some e → 1158 ≤ e.pc → e.pc < 1840 →
      ∃ i f, i ≤ k ∧ X.get (g, i) = some f ∧ f.pc = 1178 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro e he h1 h2
    obtain ⟨j, f, rfl, hf, h3, h4, h5⟩ := Wg0.w0_pc_step hp hX hFw hnu hw hv hlow he h1 h2
    by_cases hc : f.pc = 1157
    · exact ⟨j + 1, e, le_rfl, he, h5 hc⟩
    · obtain ⟨i, f', hi, hf', hpc⟩ := ih j (by omega) f hf (by omega) (by omega)
      exact ⟨i, f', by omega, hf', hpc⟩

/-- **The LSE store exists**: a complete lane of warpgroup 0 with thread index below 64 has an
event `1178` that is a write. -/
theorem w0_lse_exists (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L g < 4) (hv : W0Trace P X g)
    (hlow : tidOf L g < 64) (hC : Complete L X) (hg : g < L.threads) :
    ∃ k a bs, X.get (g, k) = some ⟨1178, .wr a bs⟩ := by
  obtain ⟨pcx, hlast⟩ := (hC.1 g hg).resolve_left (noCanceled hX g)
  rw [List.getLast?_eq_getElem?] at hlast
  have hbar := wg0_exitBar12 hp hX hFw hw (j := (X.tr g).length - 1) hlast
  obtain ⟨b, hb, hbid⟩ := List.countP_pos_iff.mp hbar
  obtain ⟨kb, hkb⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨pcb, kd⟩ := b
  have hkd : ∃ cnt md, kd = .bar 12 cnt md := by
    cases kd <;> simp [Execution.isBarId] at hbid
    rename_i i cnt md
    exact ⟨cnt, md, by rw [hbid]⟩
  obtain ⟨cnt, md, rfl⟩ := hkd
  have hget : X.get (g, kb) = some ⟨pcb, .bar 12 cnt md⟩ := hkb
  have hpcb := wg0_bar12_pc hp hX hFw hw hget
  obtain ⟨i, f, -, hf, hpc⟩ := w0_descend hp hX hFw hnu hw hv hlow kb _ hget
    (by simp only [hpcb]; omega) (by simp only [hpcb]; omega)
  have hub : ∀ fl, f.kind ≠ .ub fl := noUb_kind hnu hf
  obtain ⟨d, -, ⟨hpc', hk⟩, -⟩ := wg0_at hp hX hFw hf hub (by omega)
  have hsite : d.site = .lse := Wg0.Data.site_pc_1178 (hpc.symm.trans hpc').symm
  have hk' := hk
  simp only [Wg0.EvK, hsite, GWrAt] at hk'
  rcases hk' with ⟨a, bs, hkd, -⟩ | ⟨fl, hfl⟩
  · obtain ⟨pcf, kdf⟩ := f
    simp only at hpc hkd
    subst hpc hkd
    exact ⟨i, a, bs, hf⟩
  · exact absurd hfl (hub fl)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
