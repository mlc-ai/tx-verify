-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSBase

@[expose] public section

/-!
# Event shapes of the softmax region: register request, barriers, polls, waits, shuffles

What the events of the region's synchronization sites are, in terms of the abstract state:

* `setMaxReg`: the request to increase the register budget to 256;
* `bar0`: `bar.sync 1`, the barrier of the whole CTA;
* `waitS`: the poll (`mbarrier.try_wait.parity`) of the barrier `s_ready (i % 2)` of the thread's
  own CTA, with parity `(i / 2) % 2`, acquire semantics at CTA scope (`waitS_loc` states the
  location as `EvD.Bar.loc` of the barrier `sReadyOf i`);
* `shfl4`: the full-warp `shfl.sync.idx` of the warp index `tid / 32` from lane 0;
* `waitLd`: `tcgen05.wait::ld`;
* `bar20`, `bar21`: `bar.sync 0, 128` (barrier 0, the 128 threads of the default partition's
  four warps);
* `tmemWait`, `waitStO`: `tcgen05.wait::st`;
* `shfl12`: the full-warp `shfl.sync.bfly` of the running minimum of the alphas with lane mask 1.

Every statement is about a continuing event (`Fired … (some u)`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- **The register budget request**: `setmaxnreg.inc 256`. -/
theorem shape_setMaxReg (hF : Fired L g d e (some u)) (hs : d.site = .setMaxReg) :
    ∃ inst, e = ⟨evPc d.site, .setMaxReg true 256 inst⟩ := by
  have hpc : d.site.pc = 574 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_setMaxReg_1) hF
  rw [hpc] at hf
  obtain ⟨inst, he⟩ := fires_of_setMaxReg_op (by decide) hf
  exact ⟨inst, by rw [he, evPc, hpc]⟩

/-- **The barrier before the preloads**: `bar.sync 1` of every thread of the CTA. -/
theorem shape_bar0 (hF : Fired L g d e (some u)) (hs : d.site = .bar0) :
    e = ⟨evPc d.site, .bar 1 none .sync⟩ := by
  have hpc : d.site.pc = 575 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_bar_19) hF
  rw [hpc] at hf
  rw [fires_barSync_imm (by decide) hf, evPc, hpc]

/-- **The poll of `s_ready`**: a poll of the object at `sharedBase + off` of the barrier
`sReady (i % 2)` (as a 32-bit shared address) in the thread's own CTA, parity `(i / 2) % 2`,
acquire at CTA scope; the poll's outcome is free. -/
theorem shape_waitS (hF : Fired L g d e (some u)) (hs : d.site = .waitS) :
    ∃ ok, e = ⟨evPc d.site, .wait ⟨.shared, g / L.block,
      (L.sharedBase + (sReadyOf d.i).off) % 2 ^ 32⟩ (d.i / 2 % 2) ok true .cta⟩ := by
  have hpc : d.site.pc = 1257 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_mbarWait_0) hF
  rw [hpc] at hf
  have h875 : t.regs 874 =
      some (b32 ((L.sharedBase + (sReadyOf d.i).off) % 2 ^ 32)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    have : valueOf L g d 874 = b32 ((L.sharedBase + d.i % 2 * 8 + 213280) % 2 ^ 32) := by sm_vals
    have e : L.sharedBase + (sReadyOf d.i).off = L.sharedBase + d.i % 2 * 8 + 213280 := by
      simp only [sReadyOf, Bar.off]
      omega
    rw [this, e]
  have h876 : t.regs 875 = some (b32 (d.i / 2 % 2)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  have hq := readBits_b32 (L := L) (g := g) h876 (by omega)
  obtain ⟨ok, he⟩ := fires_wait_at h875 (Nat.mod_lt _ (by decide)) hq (by omega)
    (asms_noWiden _) hf
  exact ⟨ok, by rw [he, evPc, hpc, Nat.mod_mod]⟩

/-- **The poll of `s_ready`, by function**: the barrier `EvD.Bar.sReady (i % 2)` of the thread's
own CTA, where the launch's shared window does not wrap. -/
theorem shape_waitS_loc (hS : SharedOk L) (hF : Fired L g d e (some u))
    (hs : d.site = .waitS) :
    ∃ ok, e = ⟨evPc d.site, .wait ((sReadyOf d.i).loc L (g / L.block)) (d.i / 2 % 2) ok true
      .cta⟩ := by
  obtain ⟨ok, he⟩ := shape_waitS hF hs
  refine ⟨ok, ?_⟩
  rw [he]
  have : (L.sharedBase + (sReadyOf d.i).off) % 2 ^ 32 = L.sharedBase + (sReadyOf d.i).off := by
    apply Nat.mod_eq_of_lt
    have := Bar.off_lt (sReadyOf d.i)
    have := hS.2
    simp only [sharedBytes] at *
    omega
  rw [this]
  rfl

/-- **The broadcast of the warp index**: a full-warp `shfl.sync.idx` of `tid / 32` from lane 0. -/
theorem shape_shfl4 (hF : Fired L g d e (some u)) (hs : d.site = .shfl4) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩ := by
  have hpc : d.site.pc = 1261 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_shfl_4) hF
  rw [hpc] at hf
  have hr : t.regs 464 = some (b32 (g % L.block / 32)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  obtain ⟨recv', ok', he'⟩ := fires_shfl_idx (p := none) hr hf hsh
  exact ⟨recv', ok', by rw [he', evPc, hpc]⟩

/-- **The wait for the S-tile load**: `tcgen05.wait::ld`. -/
theorem shape_waitLd (hb : L.block % 32 = 0) (hF : Fired L g d e (some u))
    (hs : d.site = .waitLd) : e = ⟨evPc d.site, .tc .waitLd⟩ := by
  have hpc : d.site.pc = 1298 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_tmemWait_1) hF
  rw [hpc] at hf
  rw [fires_tcWaitLd hb hf, evPc, hpc]

/-- **The named barriers of the P store**: `bar.sync 0, 128` (barrier 0, 128 threads) in a block
of another size. -/
theorem shape_bar20 (hb : L.block ≠ 128) (hF : Fired L g d e (some u)) (hs : d.site = .bar20) :
    e = ⟨evPc d.site, .bar 0 (some 128) .sync⟩ := by
  have hpc : d.site.pc = 999 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_bar_20) hF
  rw [hpc] at hf
  rw [fires_barSyncN_128 hb hf, evPc, hpc]

theorem shape_bar21 (hb : L.block ≠ 128) (hF : Fired L g d e (some u)) (hs : d.site = .bar21) :
    e = ⟨evPc d.site, .bar 0 (some 128) .sync⟩ := by
  have hpc : d.site.pc = 1012 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_bar_21) hF
  rw [hpc] at hf
  rw [fires_barSyncN_128 hb hf, evPc, hpc]

/-- **The wait for the P store**: `tcgen05.wait::st`. -/
theorem shape_tmemWait (hF : Fired L g d e (some u)) (hs : d.site = .tmemWait) :
    e = ⟨evPc d.site, .tc .waitSt⟩ := by
  have hpc : d.site.pc = 1010 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_tmemWait_0) hF
  rw [hpc] at hf
  rw [(fires_tcWaitSt hf).2, evPc, hpc]

/-- **The wait for the O rescale's store**: `tcgen05.wait::st`. -/
theorem shape_waitStO (hF : Fired L g d e (some u)) (hs : d.site = .waitStO) :
    e = ⟨evPc d.site, .tc .waitSt⟩ := by
  have hpc : d.site.pc = 2329 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_tmemWait_3) hF
  rw [hpc] at hf
  rw [(fires_tcWaitSt hf).2, evPc, hpc]

/-- **The last exchange of the rescale test**: a full-warp `shfl.sync.bfly` of the running minimum
(`D.stg.m2`) with lane mask 1; the received value and the validity are free. -/
theorem shape_shfl12 (hF : Fired L g d e (some u)) (hs : d.site = .shfl12) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .bfly d.stg.m2 1 31 recv ok⟩ := by
  have hpc : d.site.pc = 2255 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_shfl_12) hF
  rw [hpc] at hf
  have hr : t.regs 1544 = some d.stg.m2 := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  obtain ⟨recv', ok', he'⟩ := fires_shfl_bfly1 (p := none) hr hf hsh
  exact ⟨recv', ok', by rw [he', evPc, hpc]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
