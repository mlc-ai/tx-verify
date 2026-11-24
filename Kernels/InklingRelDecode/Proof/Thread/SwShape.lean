-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSAll
public import Kernels.InklingRelDecode.Proof.Thread.SmAll

@[expose] public section

/-!
# Event shapes of the softmax region's rescale: the load and the store of the `O` tile

The sites after the rescale test (`ldO`, `stO`) had a step lemma (`SmStgE`) but no event shape
(row S2 and S3 of the gap table). Both use the Tensor Memory address `oAddr`: the base `tm + 256`
and the thread's warp lanes (`warp · 2 ^ 21`).

* `shape_ldO`: `tcgen05.ld` of 64 words from `oAddr` in shape `.16x32bx2`;
* `shape_stO`: `tcgen05.st` of 64 words to `oAddr` in shape `.16x32bx2`; word `k` is the product
  `prodO al (ow k)` of `alpha` (`%r46`) and the word the preceding `ldO` returned (`D.stg.ow`).

`Sm.Shape` itself is not extended (`EvSShape.lean` is not edited): `ShapeO` is the same kind of
statement for these two sites and `shapeO` the theorem.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- The Tensor Memory address of the `O` tile's words of the thread (`%r1150`): the base `tm + 256`
and the lane bits the broadcast of the warp index returned (`Stg.bw`). -/
def oAddr (_L : Launch) (_g : Nat) (d : D) : Nat :=
  (d.stg.bw * 2097152 + (d.e.tm + 256) % 2 ^ 32) % 2 ^ 32

/-- The address's two parts: the base `tm + 256` and the warp's lanes, for a softmax thread
(`g % block < 128`) whose recorded lane bits are the warp index and whose base's columns leave
room (`tm + 256 < 2 ^ 21`). -/
theorem oAddr_eq (hT : g % L.block < 128) (htm : d.e.tm + 256 < 2 ^ 21)
    (hb : d.stg.bw = g % L.block / 32) :
    oAddr L g d = d.e.tm + 256 + g % L.block / 32 * 2 ^ 21 := by
  unfold oAddr
  rw [hb]
  omega

/-- **The Tensor Memory load of `O`** (the rescale): 64 values from `oAddr`, as `.16x32bx2`. -/
theorem shape_ldO (hF : Fired L g d e (some u)) (hs : d.site = .ldO) :
    ∃ vals, vals.length = 64 ∧
      e = ⟨evPc d.site, .tc (.ld (oAddr L g d) vals (.s16x32bx2 64))⟩ := by
  have hpc : d.site.pc = 2260 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact code_ldO) hF
  rw [hpc] at hf
  have hr : t.regs 1611 = some (b32 (oAddr L g d)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
    rfl
  obtain ⟨vals, hl, he⟩ := fires_tcLd_at (L := L) (g := g) (by intro s hs; cases hs) hr
    (Nat.mod_lt _ (by decide)) hf (asms_noLdWait _)
  exact ⟨vals, by rw [hl, ldORegs_length], by rw [he, evPc, hpc]⟩

/-- **The Tensor Memory store of the rescaled `O` words**: 64 values to `oAddr`, as `.16x32bx2`;
word `k` is the product of `alpha` and the loaded word `ow k` (`prodO`). -/
theorem shape_stO (hF : Fired L g d e (some u)) (hs : d.site = .stO) :
    ∃ vals, vals.length = 64 ∧
      (∀ k, k < 64 → vals[k]? = some (prodO d.stg.al (d.stg.ow k))) ∧
      (∀ v ∈ vals, v.bytes = 4) ∧
      e = ⟨evPc d.site, .tc (.st (oAddr L g d) vals (.s16x32bx2 64))⟩ := by
  have hpc : d.site.pc = 2328 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_tmemStore_1) hF
  rw [hpc] at hf
  have hr : t.regs 1611 = some (b32 (oAddr L g d)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
    rfl
  obtain ⟨⟨vals, he⟩, -⟩ := fires_tcSt (A := asms) hr (Nat.mod_lt _ (by decide)) hf
  have hk : e.kind = .tc (.st (oAddr L g d) vals (.s16x32bx2 64)) := by rw [he]
  refine ⟨vals, ?_, ?_, fires_tcSt_bytes hf hk (by intro s hs; cases hs), by rw [he, evPc, hpc]⟩
  · rw [fires_tcSt_len (by intro s hs; cases hs) hf hk]
    rfl
  · intro k hk'
    have hv : t.regs (1612 + k) = some (prodO d.stg.al (d.stg.ow k)) := by
      rw [reg_at h (by rw [hpc]; revert k; decide +kernel), valueOf_prod d hk']
    exact fires_tcSt_vals (by intro s hs; cases hs) hf hk (p := k) (r := 1612 + k)
      (by interval_cases k <;> rfl) hv

/-- The event shape of the two rescale sites. -/
def ShapeO (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .ldO => ∃ vals, vals.length = 64 ∧
      e = ⟨evPc d.site, .tc (.ld (oAddr L g d) vals (.s16x32bx2 64))⟩
  | .stO => ∃ vals, vals.length = 64 ∧
      (∀ k, k < 64 → vals[k]? = some (prodO d.stg.al (d.stg.ow k))) ∧
      (∀ v ∈ vals, v.bytes = 4) ∧
      e = ⟨evPc d.site, .tc (.st (oAddr L g d) vals (.s16x32bx2 64))⟩
  | _ => True

/-- **Every continuing event of the rescale's load and store has its shape.** -/
theorem shapeO (hF : Fired L g d e (some u)) : ShapeO L g d e := by
  unfold ShapeO
  split
  · rename_i hs; exact shape_ldO hF hs
  · rename_i hs; exact shape_stO hF hs
  · trivial

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
