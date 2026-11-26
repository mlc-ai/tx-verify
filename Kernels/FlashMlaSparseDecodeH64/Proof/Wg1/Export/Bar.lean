-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Wg1
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # Warpgroup 1's head and idle code: the CTA barrier

`wg1_bar`: a CTA-barrier event of a warpgroup-1 lane at a pc of the head or the idle code is the
idle code's `bar.sync 12` over the whole CTA (no count), at pc 2604 (`wg1_state`,
`Common/Where.lean`); `barRow_wg1` is the row `BarRow.Wg1`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **Warpgroup 1's barrier is `bar.sync 12` of the CTA at pc 2604.** -/
theorem wg1_bar (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hat : Wg1At L g e.pc) {id : Nat}
    {cnt : Option Nat} {md : BarMode} (hk : e.kind = .bar id cnt md) :
    e.pc = 2604 ∧ id = 12 ∧ cnt = none ∧ md = .sync := by
  obtain ⟨σ, -, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he (fun f h => by rw [hk] at h; cases h)
  obtain ⟨-, -, hr⟩ := hat
  rcases wg1_state hJ hi hev hpc hr with ⟨s, hs, hev, -⟩ | ⟨s, hne, hev, hpc', -⟩
  · rcases hs with rfl | rfl
    · obtain ⟨inst, hk'⟩ := hev
      rw [hk] at hk'
      cases hk'
    · obtain ⟨r, ok, hk'⟩ := hev
      rw [hk] at hk'
      cases hk'
  · cases s with
    | ldA | ldB =>
      rcases hev with ⟨a, bs, hk'⟩ | ⟨f, hk'⟩ <;> rw [hk] at hk' <;> cases hk'
    | bar =>
      have hk' : e.kind = .bar 12 none .sync := hev
      rw [hk] at hk'
      cases hk'
      exact ⟨hpc', rfl, rfl, rfl⟩
    | ret => exact absurd rfl hne

/-- **Row `BarRow.Wg1`**: a barrier event of warpgroup 1 is `everyone_sync` at 2604. -/
theorem barRow_wg1 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : BarRow.Wg1 P L X := by
  intro g k e _ he hat hb
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | bar id cnt md =>
    obtain ⟨hpc, rfl, rfl, rfl⟩ := wg1_bar hp hX hFw he hat rfl
    exact ⟨hpc, rfl⟩
  | _ => simp [Execution.isBar] at hb

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
