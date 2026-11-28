-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SldSite
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem

@[expose] public section

/-! # The columns of the score loads

The score loads of a lane of warpgroup 0 at pcs 278 and 283 read the Tensor Memory column 400,
those at pcs 280 and 285 the column 432 (`sld arm k` loads column `400 + 32 k`). With the arm of
`w0_sld_arm`: the high half is loaded at pcs 278 (column 400) and 285 (column 432), the low half
at pcs 280 (column 432) and 283 (column 400). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A score load's event**: an event of a lane of warpgroup 0 at pc 278, 280, 283 or 285 is a
Tensor Memory load of the column 400 (pcs 278 and 283) or 432 (pcs 280 and 285). -/
theorem wg0_sldKind (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 278 ∨ e.pc = 280 ∨ e.pc = 283 ∨ e.pc = 285) :
    ∃ (a : Nat) (vals : List Value), e.kind = .tc (.ld a vals .s32x32b) ∧
      ((e.pc = 278 ∨ e.pc = 283) → a = 400) ∧ ((e.pc = 280 ∨ e.pc = 285) → a = 432) := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc' (by omega)
  have hE2 := hE.2
  have hsp : d.site.pc = e.pc := hpc'.symm
  have hs := Wg0.site_sld_of_pc d.site (by omega)
  unfold Wg0.EvK at hE2
  have key : ∀ (b : Bool) (k' : Fin 2), d.site = .sld b k' →
      ∃ (a : Nat) (vals : List Value), e.kind = .tc (.ld a vals .s32x32b) ∧
        a = 400 + 32 * k'.val := by
    intro b k' hk'
    rw [hk'] at hE2
    rcases hE2 with ⟨v, hv⟩ | ⟨f, hf⟩
    · exact ⟨_, v, hv, rfl⟩
    · exact absurd hf (hub f)
  rcases hs with h | h | h | h <;> obtain ⟨a, v, hv, ha⟩ := key _ _ h <;>
    simp [h, Wg0.Site.pc] at hsp ha <;> exact ⟨a, v, hv, by omega, by omega⟩

/-- **The column of a score load**: a Tensor Memory load event of a lane of warpgroup 0 at pc 278
or 283 reads the column 400, at pc 280 or 285 the column 432. -/
theorem wg0_sldCol (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc a : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩)
    (hpc : pc = 278 ∨ pc = 280 ∨ pc = 283 ∨ pc = 285) :
    ((pc = 278 ∨ pc = 283) → a = 400) ∧ ((pc = 280 ∨ pc = 285) → a = 432) := by
  obtain ⟨a', v', hk, h1, h2⟩ := wg0_sldKind hp hX hFw he (fun _ h => by cases h) hpc
  simp only [Kind.tc.injEq, TcKind.ld.injEq] at hk
  obtain ⟨rfl, -, -⟩ := hk
  exact ⟨h1, h2⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
