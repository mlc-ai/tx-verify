-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvSAll

@[expose] public section

/-!
# The softmax region's `o_done` poll

`Sm.Shape` is `True` at `Sm.Site.waitO` (the poll of `o_done` at pc 2239). The poll's barrier
register (`%r162`, `623`) and parity register (`%r1071`, `1532`) have table values at the site
(`Sm.valueOf`: `sharedBase + 213312` and `(i + 1) % 2`), so the event is a poll of the barrier
`EvD.Bar.oDone` of the thread's CTA (`shape_waitO`). This is the premise of
`Safety.OdoneWait`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- **The poll of `o_done`**: a poll of the object `Bar.oDone` of the thread's own CTA, with
parity `(i + 1) % 2`, acquire at CTA scope; the poll's outcome is free. -/
theorem shape_waitO (hS : SharedOk L) (hF : Fired L g d e (some u)) (hs : d.site = .waitO) :
    ∃ ok, e = ⟨evPc d.site, .wait (Bar.oDone.loc L (g / L.block)) ((d.i + 1) % 2) ok true
      .cta⟩ := by
  have hpc : d.site.pc = 2239 := by rw [hs]; rfl
  obtain ⟨t, h, hi, hf⟩ := fired_unpack (by rw [hpc]; exact Flow.code_mbarWait_1) hF
  rw [hpc] at hf
  have h623 : t.regs 623 = some (b32 ((L.sharedBase + 213312) % 2 ^ 32)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  have h1532 : t.regs 1532 = some (b32 ((d.i + 1) % 2)) := by
    rw [reg_at h (by rw [hpc]; decide +kernel)]
    sm_vals
  have hq := readBits_b32 (L := L) (g := g) h1532 (by omega)
  obtain ⟨ok, he⟩ := fires_wait_at h623 (Nat.mod_lt _ (by decide)) hq (by omega)
    (asms_noWiden _) hf
  have hm : (L.sharedBase + 213312) % 2 ^ 32 = L.sharedBase + 213312 := by
    apply Nat.mod_eq_of_lt
    have := hS.2
    omega
  refine ⟨ok, ?_⟩
  rw [he, evPc, hpc, hm, Nat.mod_eq_of_lt (by omega : (d.i + 1) % 2 < 2)]
  rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
