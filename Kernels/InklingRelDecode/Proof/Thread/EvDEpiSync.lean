-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDEpiBase

@[expose] public section

/-!
# Event shapes of the epilogue: poll, broadcast, load, barriers, release

What the events of the epilogue's non-store sites are, in terms of the abstract state:

* `wait`: the poll (`mbarrier.try_wait.parity`) of the object at the address `Prm.mb`, in the
  thread's own CTA, with parity 0, acquire semantics at CTA scope; `Prm.mb` is `o_final`'s address
  (`EvDEpiMeans`);
* `shfl`: the full-warp `shfl.sync.idx` of the warp index `Prm.w` from lane 0;
* `ld`: `tcgen05.ld` of 64 words from the Tensor Memory address `Prm.taddr`
  (`.16x32bx2`); the machine's successor state holds exactly the 64 returned words as `D.o`
  (`ld_next`);
* `waitLd`: `tcgen05.wait::ld`;
* `bar1`, `bar2`: `bar.sync 1` (every thread of the CTA); `bar3`: `bar.sync 0`;
* `setMaxInc`: the request to increase the register budget to 256;
* `stTab`: the 4-byte write `0x03030303` to the dispatch table word at `sharedBase + 213336` of
  the thread's CTA (the byte list is `storeValue 32` of the constant, [3, 3, 3, 3]);
* `dealloc`: `tcgen05.dealloc` with `cta_group::1` of the 512 columns at the Tensor Memory base
  `Prm.tm`;
* `exit`: the return.

Every statement is about a continuing event (`Fired … (some u)`); the event that ends the thread
(a fault) is undefined behaviour and has no shape here.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- **The poll of `o_final`**: a poll of the object at the address `Prm.mb` of the thread's own
CTA, parity 0, with acquire semantics at CTA scope; the poll's outcome is free. -/
theorem shape_wait (hF : Fired L g d e (some u)) (hs : d.site = .wait) :
    ∃ ok, e = ⟨evPc d.site, .wait ⟨.shared, g / L.block, d.pr.mb⟩ 0 ok true .cta⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2565 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_5)
  have hmb : t.regs 624 = some (b32 d.pr.mb) := by
    have := reg_at (d := d) (r := 624) (by rw [hpc]; exact h) (by rw [hpc]; table_decide)
    rw [this]; rfl
  have hq : t.regs 1760 = some (b32 0) := by
    have := reg_at (d := d) (r := 1760) (by rw [hpc]; exact h) (by rw [hpc]; table_decide)
    rw [this]; rfl
  have hq' := readBits_b32 (L := L) (g := g) hq (by decide)
  obtain ⟨ok, he⟩ := fires_wait_at hmb hi.ok.mb hq' (by decide) (asms_noWiden _) hf
  exact ⟨ok, by rw [he, evPc, hpc]⟩

/-- **The broadcast of the warp index**: a full-warp `shfl.sync.idx` of `Prm.w` from lane 0. -/
theorem shape_shfl (hF : Fired L g d e (some u)) (hs : d.site = .shfl) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .idx (b32 d.pr.w) 0 31 recv ok⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2603 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_15)
  have hr : t.regs 464 = some (b32 d.pr.w) := by
    have := reg_at (d := d) (r := 464) (by rw [hpc]; exact h) (by rw [hpc]; table_decide)
    rw [this]; rfl
  obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
  have hsh : Execution.isShfl e = true := by rw [he]; rfl
  obtain ⟨recv', ok', he'⟩ := fires_shfl_idx (p := none) hr hf hsh
  exact ⟨recv', ok', by rw [he', evPc, hpc]⟩

/-- **The Tensor Memory load**: 64 values from the address `Prm.taddr`, as `.16x32bx2`. -/
theorem shape_ld (hF : Fired L g d e (some u)) (hs : d.site = .ld) :
    ∃ vals, vals.length = 64 ∧
      e = ⟨evPc d.site, .tc (.ld d.pr.taddr vals (.s16x32bx2 64))⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2607 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans code_ld)
  have hr : t.regs 1827 = some (b32 d.pr.taddr) := by
    have := reg_at (d := d) (r := 1827) (by rw [hpc]; exact h) (by rw [hpc]; table_decide)
    rw [this]; rfl
  obtain ⟨vals, hl, he⟩ := fires_tcLd_at (L := L) (g := g) (by intro s hs; cases hs) hr
    (Nat.mod_lt _ (by decide)) hf (asms_noLdWait _)
  exact ⟨vals, by rw [hl, ldRegs_length], by rw [he, evPc, hpc]⟩

/-- **The machine's state after the load holds the returned words**: they are `D.o`. -/
theorem ld_next (hs : d.site = .ld) {a : Nat} {vals : List Value} {sh : TcShape}
    (hl : vals.length = 64) :
    next d ⟨evPc d.site, .tc (.ld a vals sh)⟩ =
      some (some { d with site := .waitLd, o := vals }) := by
  simp [next, hs, hl]

/-- **The wait for the load**: `tcgen05.wait::ld`. -/
theorem shape_waitLd (hb : L.block % 32 = 0) (hF : Fired L g d e (some u))
    (hs : d.site = .waitLd) : e = ⟨evPc d.site, .tc .waitLd⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2608 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_4)
  rw [fires_tcWaitLd hb hf, evPc, hpc]

/-- **The barriers**: `bar.sync 1` of the whole CTA at `bar1` and `bar2`, `bar.sync 0` at
`bar3`. -/
theorem shape_bar1 (hF : Fired L g d e (some u)) (hs : d.site = .bar1) :
    e = ⟨evPc d.site, .bar 1 none .sync⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2846 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_34)
  rw [fires_barSync_imm (by decide) hf, evPc, hpc]

theorem shape_bar2 (hF : Fired L g d e (some u)) (hs : d.site = .bar2) :
    e = ⟨evPc d.site, .bar 1 none .sync⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2849 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_35)
  rw [fires_barSync_imm (by decide) hf, evPc, hpc]

theorem shape_bar3 (hF : Fired L g d e (some u)) (hs : d.site = .bar3) :
    e = ⟨evPc d.site, .bar 0 none .sync⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2850 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_36)
  rw [fires_barSync_imm (by decide) hf, evPc, hpc]

/-- **The register budget request**: `setmaxnreg.inc 256`. -/
theorem shape_setMaxInc (hF : Fired L g d e (some u)) (hs : d.site = .setMaxInc) :
    ∃ inst, e = ⟨evPc d.site, .setMaxReg true 256 inst⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2847 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_9)
  obtain ⟨inst, he⟩ := fires_of_setMaxReg_op (by decide) hf
  exact ⟨inst, by rw [he, evPc, hpc]⟩

/-- **The return**: the event is the thread's exit, whatever the continuation. -/
theorem shape_exit {o : Option TState} (hF : Fired L g d e o) (hs : d.site = .exit) :
    e = ⟨evPc d.site, .exit⟩ ∧ o = none := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2855 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
  obtain ⟨he, ho⟩ := hf
  exact ⟨by rw [he, evPc, hpc], ho⟩

/-- **The Tensor Memory release**: `tcgen05.dealloc.cta_group::1` of 512 columns at `Prm.tm`. -/
theorem shape_dealloc (hF : Fired L g d e (some u)) (hs : d.site = .dealloc) :
    e = ⟨evPc d.site, .tc (.resource .one none (.dealloc d.pr.tm 512))⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2851 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
  have hr : t.regs 463 = some (b32 d.pr.tm) := by
    have := reg_at (d := d) (r := 463) (by rw [hpc]; exact h) (by rw [hpc]; table_decide)
    rw [this]; rfl
  have ha := readBits_b32 (L := L) (g := g) hr hi.ok.tm
  have hn := readBits_imm (L := L) (g := g) (t := t) (n := 512) (by decide)
  obtain ⟨dst, act, hk⟩ := fires_tcDealloc_some hf
  obtain ⟨-, rfl, rfl⟩ := fires_tcDealloc_at ha hn hf hk
  have hp := fires_pc hf
  obtain ⟨epc, ek⟩ := e
  simp only at hp hk
  subst hk
  have h1 : (BitVec.ofNat 64 d.pr.tm).toNat = d.pr.tm := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := hi.ok.tm; unfold M32 at this; omega)
  have h2 : (BitVec.ofNat 64 512).toNat = 512 := by
    rw [BitVec.toNat_ofNat]
  rw [h1, h2, hp, evPc, hpc]

/-- **The dispatch-table write**: the four bytes of `0x03030303` (`storeValue 32` of the constant)
at `sharedBase + 213336` of the thread's own CTA. -/
theorem shape_stTab (hF : Fired L g d e (some u)) (hs : d.site = .stTab) :
    ∃ v', storeValue 32 (b32 50529027) = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc ⟨.shared, g / L.block, (L.sharedBase + 213336) % 2 ^ 32⟩)
        v'.toBytes⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2848 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  have hins := Option.some.inj (hc.symm.trans (isSymStore_spec
    (by decide +kernel : isSymStore 2848 1 213336 [Opnd.imm 50529027] = true)))
  have hop : ins.op = .mem (symStore 1 213336 [Opnd.imm 50529027]) := congrArg Instr.op hins
  obtain ⟨v', hsv, he⟩ := fires_st_sym (hf := hf) (j := 0) (hop := hop) (by decide) h.2.1 rfl
    (readValue_imm32 (n := 50529027) (by decide)) rfl (Or.inl rfl)
  refine ⟨v', hsv, ?_⟩
  rw [he, evPc, hpc]
  simp [wordAcc]

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
