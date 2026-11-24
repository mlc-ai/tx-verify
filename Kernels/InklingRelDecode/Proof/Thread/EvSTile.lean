-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSBase
public import Kernels.InklingRelDecode.Proof.Thread.SmS
public import Lemmas.Flow.TcStBytes
public import Lemmas.Flow.ElemAccess

@[expose] public section

/-!
# Event shapes of the softmax region: the S tile load, the P tile store and the `p_ready` arrival

* `ldS`: `tcgen05.ld` of 64 words from the Tensor Memory address `tileAddr` in shape `.16x32bx2`.
  The address is the stage's base `tm + 128 (i % 2)` plus the recorded lane bits shifted to bit 21
  (`r45`: the lane field of a Tensor Memory address, bits 16 to 31, is `32 · warp`, so
  `warp · 2 ^ 21` where the bits are the warp index).
  `ld_next` says the machine's successor holds exactly the 64 returned words as `D.sv`, and
  `ld_sv` that word `k` is the `k`-th returned value.
* `tmemSt`: `tcgen05.st` of 32 words to the same address in shape `.16x32bx2`; the words are the
  conversions `D.pwV w` of the probability words `Stg.pv` (columns `2 w` and `2 w + 1`); where
  those are the `.f32` values of `D.pf` this is `D.pw w`, the packed `bf16` pair (`pwV_real`).
* `arrive`: `mbarrier.arrive` with release semantics at CTA scope, byte count 0 and arrival count
  1 on the barrier `p_ready (i % 2)` of the thread's own CTA, issued by thread 0 of the block
  (the guard `%p177`, which `Inv.lead` records).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000
set_option linter.deprecated false

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- The sites from the S load to the end of the iteration: the recorded lane bits are those of
the iteration's broadcast of the warp index (`Interface.sm_bw`). -/
def BwSite : Site → Prop
  | .setMaxReg | .bar0 | .pre _ | .nxt _ | .waitS | .shfl4 => False
  | _ => True

/-- The Tensor Memory address of the thread's S and P tile in the state's iteration (`%r1215`):
the Tensor Memory base `tm`, 128 columns per stage, and the lane bits the broadcast of the warp
index returned (`Stg.bw`, the warp index after tracking: `Interface.sm_bw`). -/
def tileAddr (_L : Launch) (_g : Nat) (d : D) : Nat :=
  (d.i % 2 * 128 + d.e.tm + r45 d.stg.bw) % 2 ^ 32

/-- The address's three parts: the base `tm`, `128` columns per stage and the warp's lanes
(`warp · 2 ^ 21`, the lane field of a Tensor Memory address starting at bit 16), when the recorded
lane bits are the warp index and the base's columns leave room for the stage
(`tm + 256 ≤ 2 ^ 21`). -/
theorem tileAddr_eq (hT : g % L.block < 128) (htm : d.e.tm + 256 ≤ 2 ^ 21)
    (hb : d.stg.bw = g % L.block / 32) :
    tileAddr L g d = d.e.tm + 128 * (d.i % 2) + g % L.block / 32 * 2 ^ 21 := by
  unfold tileAddr r45
  rw [hb]
  omega

/-- **The Tensor Memory load of the S tile**: 64 values from `tileAddr`, as `.16x32bx2`. -/
theorem shape_ldS (hF : Fired L g d e (some u)) (hs : d.site = .ldS) :
    ∃ vals, vals.length = 64 ∧
      e = ⟨evPc d.site, .tc (.ld (tileAddr L g d) vals (.s16x32bx2 64))⟩ := by
  have hpc : d.site.pc = 1265 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact code_ldS) hF
  rw [hpc] at hf
  have hr : t.regs 1676 = some (b32 (tileAddr L g d)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
    rfl
  obtain ⟨vals, hl, he⟩ := fires_tcLd_at (L := L) (g := g) (by intro s hs; cases hs) hr
    (Nat.mod_lt _ (by decide)) hf (asms_noLdWait _)
  exact ⟨vals, by rw [hl, ldRegs_length], by rw [he, evPc, hpc]⟩

/-- **The machine's state after the load holds the returned words**: they are `D.sv`. -/
theorem ld_next (hs : d.site = .ldS) {a : Nat} {vals : List Value} {sh : TcShape}
    (hl : vals.length = 64) (hb : ∀ x ∈ vals, x.bytes = 4) :
    next L g d ⟨evPc d.site, .tc (.ld a vals sh)⟩ =
      some (some { d with site := .waitLd, sv := svOf vals hb }) := by
  simp only [next, hs]
  rw [dif_pos ⟨hl, hb⟩]

/-- **The Tensor Memory store of the P tile**: 32 values to `tileAddr`, as `.16x32bx2`; word `w`
is `D.pwV w`, the conversion of the probability words of the columns `2 w` and `2 w + 1`. -/
theorem shape_tmemSt (hF : Fired L g d e (some u)) (hs : d.site = .tmemSt) :
    ∃ vals, vals.length = 32 ∧ (∀ w, w < 32 → vals[w]? = some (d.pwV w)) ∧
      (∀ v ∈ vals, v.bytes = 4) ∧
      e = ⟨evPc d.site, .tc (.st (tileAddr L g d) vals (.s16x32bx2 32))⟩ := by
  have hpc : d.site.pc = 1009 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_tmemStore_0) hF
  rw [hpc] at hf
  have hr : t.regs 1676 = some (b32 (tileAddr L g d)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
    rfl
  obtain ⟨⟨vals, he⟩, -⟩ := fires_tcSt (A := asms) hr (Nat.mod_lt _ (by decide)) hf
  have hk : e.kind = .tc (.st (tileAddr L g d) vals (.s16x32bx2 32)) := by rw [he]
  refine ⟨vals, ?_, ?_, fires_tcSt_bytes hf hk (by intro s hs; cases hs), by rw [he, evPc, hpc]⟩
  · rw [fires_tcSt_len (by intro s hs; cases hs) hf hk]
    rfl
  · intro w hw
    have hv : t.regs (1677 + w) = some (d.pwV w) := by
      rw [reg_at h (by rw [hpc]; revert w; decide +kernel), valueOf_pw d hw]
    exact fires_tcSt_vals (by intro s hs; cases hs) hf hk (p := w) (r := 1677 + w)
      (by interval_cases w <;> rfl) hv

/-- **The arrival on `p_ready`**: byte count 0, arrival count 1, release at CTA scope, on the
barrier `p_ready (i % 2)` of the thread's own CTA, by thread 0 of the block. -/
theorem shape_arrive (hS : SharedOk L) (hF : Fired L g d e (some u)) (hs : d.site = .arrive) :
    g % L.block = 0 ∧
      e = ⟨evPc d.site, .arrive ((pReadyOf d.i).loc L (g / L.block)) 0 1 true .cta⟩ := by
  have hpc : d.site.pc = 1013 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_mbarArrive_3) hF
  rw [hpc] at hf
  refine ⟨hi.lead hs, ?_⟩
  have hlt : L.sharedBase + (pReadyOf d.i).off < 2 ^ 32 := by
    have := Bar.off_lt (pReadyOf d.i)
    have := hS.2
    simp only [sharedBytes] at *
    omega
  have hmod : (L.sharedBase + (pReadyOf d.i).off) % 2 ^ 32 =
      L.sharedBase + (pReadyOf d.i).off := Nat.mod_eq_of_lt hlt
  have hr : t.regs 1709 = some (b32 ((L.sharedBase + (pReadyOf d.i).off) % 2 ^ 32)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    have : valueOf L g d 1709 = b32 ((L.sharedBase + d.i % 2 * 8 + 213296) % 2 ^ 32) := by sm_vals
    have e : L.sharedBase + (pReadyOf d.i).off = L.sharedBase + d.i % 2 * 8 + 213296 := by
      simp only [pReadyOf, Bar.off]
      omega
    rw [this, e]
  have hal : (L.sharedBase + (pReadyOf d.i).off) % 8 = 0 := by
    have h1 := hS.1
    simp only [pReadyOf, Bar.off]
    omega
  have := fires_arrive_at (L := L) (g := g) (t := t) hr (by rw [hmod]; exact hlt)
    (by rw [hmod]; exact hal) (by decide) (by decide) (asms_noWiden _) hf
  rw [this, evPc, hpc, hmod]
  rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
