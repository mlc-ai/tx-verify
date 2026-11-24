-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcCount
public import Kernels.Fp16Gemm8192.Proof.Thread.Machine

@[expose] public section

/-! # The MMA threads of a non-leader CTA poll no CLC response

An MMA state of an odd CTA is at the common exit: the thread's machine invariant of an MMA
state includes `Mma.Lead`, which every step keeps (`Mma.next_lead`), so its site is `exitArrive`,
`exitWait` or `exit`. Only the CLC poll site polls the CLC response barrier (`Mma.clc_sites`),
so no event fired from such a state waits on that barrier (`mma_odd_quiet`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- An MMA thread of a non-leader CTA (odd CTA index) polls no CLC response: the state its event
fires from is at the common exit, and only the CLC poll site polls the response barrier. -/
theorem mma_odd_quiet {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat} {e : Event}
    {d : ThreadD} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hm : ∃ m, d = .inr (.mma m))
    (hodd : g / L.block % 2 = 1) :
    ∀ p ok acq sc, e.kind ≠ .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p ok acq sc := by
  obtain ⟨m, rfl⟩ := hm
  obtain ⟨_, hfo⟩ := (Frame.trace (fun _ => sound hpre) hX hg).fired_at he hσ
  obtain ⟨t, ins, hat, hinv, hc, hfire⟩ := Code.fired_site (sound hpre hg) hfo
  obtain ⟨hi, -, hlead⟩ : Mma.Inv m ∧ Mma.QReset m ∧ Mma.Lead L g m := hinv
  have hsite : m.site = .exitArrive ∨ m.site = .exitWait ∨ m.site = .exit := by
    rcases hlead with h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · omega
  intro p ok acq sc hk
  have hc' := ((Mma.clc_sites (g := g) hpre hi hat hc hfire).1 p ok acq sc hk).1
  rcases hsite with h | h | h <;> rw [h] at hc' <;> cases hc'

end
end PTX.Kernels.Fp16Gemm8192.Proof
