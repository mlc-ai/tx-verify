-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerAcc
public import Kernels.Fp16Gemm8192.Proof.Thread.RingUsers
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked

@[expose] public section

/-! # The consumers' accumulator counts, and the role state before their accumulator polls

A consumer polls the full barrier of its own accumulator only (`okPolls_other`). So its successful
accumulator-full polls are its arrivals on its accumulator's empty barrier plus the accumulator it
holds (`cons_acc_count`). A consumer at its accumulator poll was entered from a role state, so the
ring of its accumulator was initialized before that state (`prior_role`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- A consumer's successful polls of the full barrier of another accumulator than its own are
none: a poll of a full barrier is by the thread's own accumulator. -/
theorem okPolls_other (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {j : Nat} (hj : j < 2) (hne : j ≠ accIdx L g) :
    okPolls (accFull L g j) (X.tr g) = 0 := by
  unfold okPolls
  rw [List.countP_eq_zero]
  intro e he hok
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  have hget : X.get (g, k) = some e := hk
  obtain ⟨p, acq, sc, hw⟩ := okPoll_wait_form hok
  have hfa : (∃ σ, Frame.stateAt (code L) X g k = some σ) ∨ ∃ pc f, e = ⟨pc, .ub f⟩ := by
    rcases (Frame.trace (fun _ => sound hpre) hX hg).fired hget with
      ⟨τ, -, ha, -⟩ | ⟨-, hub⟩
    · exact .inl ⟨τ, ha⟩
    · exact .inr hub
  rcases hfa with ⟨σ, hσ⟩ | ⟨pc, f, hf⟩
  · cases σ with
    | none => exact absurd hσ (tracked hpre hX g k hg)
    | some d =>
      have hr := ring_event hpre hX hg hget hσ
      have hvalid : (⟨.acc, j, true⟩ : Bar).Valid := by
        simp only [Bar.Valid, Ring.slots]
        omega
      obtain ⟨hby, -⟩ := hr.wait ⟨.acc, j, true⟩ (g / L.block) p true acq sc hw hvalid
      simp only [Bar.pollBy] at hby
      exact hne hby.2
  · rw [hf] at hw
    simp at hw

/-- **The consumer's accumulator count.** A consumer at its trace's end has as many successful
accumulator-full polls as its arrivals on its accumulator's empty barrier plus the accumulator it
holds. -/
theorem cons_acc_count (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c)))) :
    consCount L g (X.tr g) = arrivals (accEmpty L g (accIdx L g)) (X.tr g) + holds c := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hA := Consumer.accInv hpre hg htr (X.tr g).length _ hσ
  rw [List.take_length] at hA
  obtain ⟨hC, -, -⟩ := hA
  have hw := role_warp hpre hX hg (X.tr g).length le_rfl (.cons c) hσ
  simp only [roleWarp, Prologue.warpOf] at hw
  have hi : accIdx L g < 2 := by
    simp only [accIdx, tidOf]
    omega
  have h1 := hC (accIdx L g) hi
  simp only [ite_true] at h1
  unfold consCount
  rw [Finset.sum_eq_single (⟨accIdx L g, hi⟩ : Fin 2)]
  · exact h1
  · intro b _ hb
    have hbv : b.val ≠ accIdx L g := by
      intro h
      exact hb (Fin.ext h)
    exact okPolls_other hpre hX hg b.isLt hbv
  · intro h
    exact absurd (Finset.mem_univ _) h

end Consumer

end
end PTX.Kernels.Fp16Gemm8192.Proof
