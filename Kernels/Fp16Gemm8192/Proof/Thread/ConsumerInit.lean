-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RingUsers
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun

@[expose] public section

/-! # A consumer's accumulator-full barrier is initialized before its accumulator wait

The prologue enters the consumers only at their register increase (`Prologue.next_cons`), and a
consumer machine's successor is a consumer state. So a consumer state other than the register
increase follows a consumer state one event earlier, and the ring initialization before that
event (`ring_initialized`) covers the consumer's accumulator-full barrier in its own CTA. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A consumer state after one more event is the register increase, or follows a consumer state
one event earlier. -/
theorem cons_pred {g k : Nat} {e : Event} {c : Consumer.D}
    (he : (X.tr g)[k]? = some e)
    (hσ : Frame.stateAt (code L) X g (k + 1) = some (some (.inr (.cons c)))) :
    (∃ c', Frame.stateAt (code L) X g k = some (some (.inr (.cons c')))) ∨ c = Prologue.consStart :=
    by
  have hs1 := Frame.stateAt_succ (C := code L) (X := X) he
  rw [hσ] at hs1
  cases hs : Frame.stateAt (code L) X g k with
  | none => rw [hs] at hs1; simp at hs1
  | some σ =>
    cases σ with
    | none =>
      rw [hs] at hs1
      have hdead : (code L g).toMachine.next none e = some none := rfl
      cases hs1.trans hdead
    | some d =>
      cases d with
      | inl p =>
        have hp : Prologue.next L g p e = some (some (.inr (.cons c))) :=
          (stateAt_succ_inl he hs).symm.trans hσ
        exact .inr (Prologue.next_cons hp)
      | inr r =>
        rw [hs] at hs1
        cases r with
        | cons c' => exact .inl ⟨c', rfl⟩
        | loader l =>
          have hn : (code L g).toMachine.next (some (.inr (.loader l))) e =
              some (some (.inr (.cons c))) := hs1.symm
          obtain ⟨l', -, h⟩ := next_of_loader (d' := .inr (.cons c)) hn
          cases h
        | mma m =>
          have hn : (code L g).toMachine.next (some (.inr (.mma m))) e =
              some (some (.inr (.cons c))) := hs1.symm
          obtain ⟨m', -, h⟩ := next_of_mma (d' := .inr (.cons c)) hn
          cases h
        | sched s =>
          have hn : (code L g).toMachine.next (some (.inr (.sched s))) e =
              some (some (.inr (.cons c))) := hs1.symm
          obtain ⟨s', -, h⟩ := next_of_sched (d' := .inr (.cons c)) hn
          cases h

/-- **The consumer's accumulator-full barrier is initialized before its accumulator wait.** A
consumer at its accumulator-full wait is in a consumer state, which CTA thread 0 of its own CTA
initialized (`ring_initialized`, at the event before its state). -/
theorem cons_acc_init_thm (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g : Nat} {c : Consumer.D} (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))))
    (hs : c.site = .accWait) :
    ∃ ipc, X.get (g / L.block * L.block, Bar.initIndex ⟨.acc, g % L.block / 32 / 4, true⟩) =
      some ⟨ipc, .mbInit (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 / 4, true⟩)
        (Bar.count ⟨.acc, g % L.block / 32 / 4, true⟩)⟩ := by
  have hblock : 0 < L.block := by rw [hpre.block]; norm_num
  have hlen : (X.tr g).length ≠ 0 := by
    intro h0
    rw [h0, stateAt_zero] at hσ
    cases hσ
  obtain ⟨k, hk⟩ : ∃ k, (X.tr g).length = k + 1 := ⟨(X.tr g).length - 1, by omega⟩
  have hkl : k < (X.tr g).length := by omega
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hkl⟩
  rw [hk] at hσ
  rcases cons_pred he hσ with ⟨c', hc'⟩ | hcs
  · -- the state before the last event is a consumer state, whose warp is below eight
    have hwarp := role_warp hpre hX hg k (by omega) (.cons c') hc'
    simp only [roleWarp, Prologue.warpOf] at hwarp
    have hvalid : (⟨.acc, g % L.block / 32 / 4, true⟩ : Bar).Valid := by
      simp only [Bar.Valid, Ring.slots]
      omega
    have hgrid : g / L.block < L.grid := by
      have hg' : g < L.grid * L.block := hg
      rw [Nat.div_lt_iff_lt_mul hblock]
      exact hg'
    have he' : X.get (g, k) = some e := he
    obtain ⟨pc, hpc, -⟩ := ring_initialized hpre hX (b := ⟨.acc, g % L.block / 32 / 4, true⟩)
      (cta := g / L.block) hg he' hc' hvalid hgrid rfl
    exact ⟨pc, hpc⟩
  · -- the register increase is not an accumulator wait
    rw [hcs] at hs
    simp [Prologue.consStart] at hs

end
end PTX.Kernels.Fp16Gemm8192.Proof
