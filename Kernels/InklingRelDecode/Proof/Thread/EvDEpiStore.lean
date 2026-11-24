-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDEpiSync

@[expose] public section

/-!
# Event shapes of the epilogue: the output stores

The epilogue writes its row of `OPart` with 64 `st.global.b32` and its `LsePart` word with one:

* `stO k` (`k < 64`): a write of the four bytes `storeValue 32 (D.word k)` at the address
  `Prm.oAddr + 4 k` (modulo `2^64`) of global memory;
* `stLse`: a write of the four bytes `storeValue 32 (Prm.lseWord)` at the address `Prm.lAddr`.

Both are plain (weak) writes of the footprint `wordAcc ⟨.global, 0, address⟩`. `D.word k` is the
low or high half of the product pair `k / 2` (`D.prod`): the product of the pair `(1/l, 1/l)` with
the loaded pair, or the zero pair on the `num_iters < 1` path; `EpiValue.word_fin` evaluates it.
`Prm.lseWord` is the pattern of `-inf` for an empty row and `Prm.lse` otherwise.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- The instruction at `pc` is `@p st.global.b32 [%rd base], %r src`. -/
def isGstore (pc p base src : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨some (q, neg), .mem a⟩ => q == p && !neg && decide (a = gstore32 base src)
  | _ => false

theorem isGstore_spec {pc p base src : Nat} (h : isGstore pc p base src = true) :
    kernel.code[pc]? = some ⟨some (p, false), .mem (gstore32 base src)⟩ := by
  unfold isGstore at h
  split at h
  · rename_i q neg a hc
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨⟨hq, hn⟩, ha⟩ := h
    subst hq; subst hn; subst ha
    exact hc
  · cases h

/-- The 64 stores of `OPart` are the global 32-bit stores of the words `1833 + k` to the
addresses `2381 + k`, guarded by the row-valid predicate. -/
theorem code_stO (k : Nat) (hk : k < 64) : kernel.code[stPc k]? =
    some ⟨some (175, false), .mem (gstore32 (2380 + k) (1832 + k))⟩ :=
  isGstore_spec ((by decide +kernel : ∀ k < 64, isGstore (stPc k) 175 (2380 + k) (1832 + k) = true)
    k hk)

/-- The store of `LsePart` is the global 32-bit store of register 1832 to the address of 2380. -/
theorem code_stLse : kernel.code[(Site.stLse).pc]? =
    some ⟨some (174, false), .mem (gstore32 2379 1831)⟩ :=
  isGstore_spec (by decide +kernel : isGstore 2682 174 2379 1831 = true)

theorem st_addr_live : ∀ k < 64, 2380 + k ∈ Flow.live (stPc k) := by decide +kernel

theorem st_word_live : ∀ k < 64, 1832 + k ∈ Flow.live (stPc k) := by decide +kernel

/-- **A store of `OPart`**: the four bytes of word `k` at `Prm.oAddr + 4 k`. -/
theorem shape_stO {k : Fin 64} (hF : Fired L g d e (some u)) (hs : d.site = .stO k) :
    ∃ v', storeValue 32 (d.word k.val) = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc ⟨.global, 0, (d.pr.oAddr + 4 * k.val) % M64⟩) v'.toBytes⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = stPc k.val := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans (code_stO k.val k.isLt))
  have hr : t.regs (2380 + k.val) = some (b64 ((d.pr.oAddr + 4 * k.val) % M64)) := by
    have := reg_at (d := d) (r := 2380 + k.val) (by rw [hpc]; exact h)
      (by rw [hpc]; exact st_addr_live k.val k.isLt)
    rw [this, valueOf_addr d k.isLt]
  have hv : t.regs (1832 + k.val) = some (d.word k.val) := by
    have := reg_at (d := d) (r := 1832 + k.val) (by rw [hpc]; exact h)
      (by rw [hpc]; exact st_word_live k.val k.isLt)
    rw [this, valueOf_word d k.isLt]
  obtain ⟨v', hsv, he, -⟩ := fires_st_global32 h.2.1 hr (Nat.mod_lt _ (by decide)) hv hf
  exact ⟨v', hsv, by rw [he, evPc, hpc]; rfl⟩

/-- **The store of `LsePart`**: the four bytes of `Prm.lseWord` at `Prm.lAddr`. -/
theorem shape_stLse (hF : Fired L g d e (some u)) (hs : d.site = .stLse) :
    ∃ v', storeValue 32 d.pr.lseWord = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc ⟨.global, 0, d.pr.lAddr⟩) v'.toBytes⟩ := by
  obtain ⟨t, ins, h, hi, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 2682 := by rw [hs]; rfl
  rw [hpc] at hc hf h
  obtain rfl := Option.some.inj (hc.symm.trans code_stLse)
  have hr : t.regs 2379 = some (b64 d.pr.lAddr) := by
    have := reg_at (d := d) (r := 2379) (by rw [hpc]; exact h) (by rw [hpc]; table_decide)
    rw [this]; rfl
  have hv : t.regs 1831 = some d.pr.lseWord := by
    have := reg_at (d := d) (r := 1831) (by rw [hpc]; exact h) (by rw [hpc]; table_decide)
    rw [this]; rfl
  obtain ⟨v', hsv, he, -⟩ := fires_st_global32 h.2.1 hr (Nat.mod_lt _ (by decide)) hv hf
  exact ⟨v', hsv, by rw [he, evPc, hpc]; rfl⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
