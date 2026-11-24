-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.FootSm
public import Lemmas.Flow.LoadShared
public import Lemmas.Flow.LoadSharedSize

@[expose] public section

/-!
# The footprint of the softmax region's shared load

`Sm.Site.ldL` is the load of the four warps' minima: `ld.shared.b32 %r, [%r500 + 212992]` with
`%r500 = sharedBase + 4 (tid % 4)`. It reads the four bytes at `sharedBase + 212992 + 4 (tid % 4)`
of the thread's CTA, one of the four scratch words `[sharedBase + 212992, sharedBase + 213008)`
(`store10`'s words). The word of a thread with `tid % 4 = 1` is `(num_iters)`'s, so the read is
not a read of `num_iters` (`Interface.NumReader` excludes it).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

theorem ldL_code : kernel.code[2252]? = some ⟨none, .mem
    { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
      addr := ⟨.reg 500 32, ((212992 : Nat) : Int)⟩, dsts := [some 1542] }⟩ :=
  Flow.code_load_202

/-- **The softmax region's shared load.** A read at `sharedBase + 212992 + 4 (tid % 4)` of the
thread's CTA. -/
theorem shape_ldL_foot (hS : SharedOk L) (hF : Fired L g d e (some u)) (hs : d.site = .ldL) :
    ∃ ac bs, e = ⟨evPc d.site, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase + g % L.block % 4 * 4 + 212992⟩ ∧
      ac.size = 4 := by
  have hpc : d.site.pc = 2252 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact ldL_code) hF
  rw [hpc] at hf
  have hr : t.regs 500 = some (b32 ((L.sharedBase + g % L.block % 4 * 4) % 2 ^ 32)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  have hsub : t.sub = 0 := by
    have h2 := h.2.1
    exact h2
  have hlt : L.sharedBase + g % L.block % 4 * 4 + 212992 < 2 ^ 32 := by
    have := hS.2
    have : g % L.block % 4 < 4 := Nat.mod_lt _ (by omega)
    omega
  have hmod : (L.sharedBase + g % L.block % 4 * 4) % 2 ^ 32 =
      L.sharedBase + g % L.block % 4 * 4 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hr
  obtain ⟨ac, bs, he, hl, -⟩ := fires_ld_shared (ik := .b) (d := 1542) hr hlt hsub hf
  have hz := fires_ld_shared_size (ik := .b) (d := 1542) hr hlt hsub hf ac bs (by rw [he])
  exact ⟨ac, bs, by rw [he, evPc, hpc], hl, hz⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
