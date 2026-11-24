-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # The times of a consumer's data events in the rank table

A consumer outside its exit stage and past its start has its next event at an offset in the block
of one task (`vtime_decomp`), and has made, with the accumulator it holds, thirty-two data events
per accumulator released plus its position in the tile it is loading. Its data events made, less the
thirty-two of the accumulator it holds, are the block's thirty-two per task and the phase of its
offset (`tcPhase`): the data events a consumer has made grow with its time (`tc_vtime_lt`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX

noncomputable section

/-- The data events of a block's tile that have been made by an offset in the block: none before the
loads (at 4202), one per two, all thirty-two after the last wait. -/
def tcPhase (o : Nat) : Nat := min 32 ((o - 4202) / 2)

theorem tcPhase_le (o : Nat) : tcPhase o ≤ 32 := by
  unfold tcPhase
  omega

theorem tcPhase_mono {o o' : Nat} (h : o ≤ o') : tcPhase o ≤ tcPhase o' := by
  unfold tcPhase
  omega

/-- A consumer in its task loop has its next event in a block, and has made the block's data events
and the phase of the offset. -/
theorem vtime_decomp {c : Consumer.D} {T : Nat} (hx : Consumer.exitOff c = none)
    (hs0 : c.site ≠ .setMaxReg) (hT : c.started + Consumer.holds c ≤ T) :
    ∃ n, blockAt n ≤ Consumer.vtime T c ∧ Consumer.vtime T c < blockAt n + blockSpan ∧
      32 * T + c.tcPos =
        32 * n + tcPhase (Consumer.vtime T c - blockAt n) + 32 * Consumer.holds c := by
  unfold Consumer.D.started at hT
  unfold Consumer.exitOff at hx
  unfold Consumer.vtime Consumer.D.tcPos tcPhase blockAt blockSpan Consumer.holds
  unfold Consumer.holds at hT
  cases hs : c.site <;> simp only [hs] at hT hx hs0 ⊢
  all_goals first
    | exact absurd rfl hs0
    | (exfalso; revert hx; simp; done)
    | (refine ⟨T, ?_, ?_, ?_⟩ <;> omega)
    | (refine ⟨T - 1, ?_, ?_, ?_⟩ <;> omega)

/-- A consumer's data events made, with the thirty-two of the accumulator it holds, are at most its
polls: the position in the tile is within the accumulator held. -/
theorem tcPos_le (c : Consumer.D) : c.tcPos ≤ 32 * Consumer.holds c := by
  unfold Consumer.D.tcPos Consumer.holds
  cases hs : c.site <;> simp
  · omega
  · omega

/-- **Fewer data events made, earlier in the rank table.** -/
theorem tc_vtime_lt {c c' : Consumer.D} {T T' : Nat} (hx : Consumer.exitOff c = none)
    (hs0 : c.site ≠ .setMaxReg) (hT : c.started + Consumer.holds c ≤ T)
    (hx' : Consumer.exitOff c' = none) (hs0' : c'.site ≠ .setMaxReg)
    (hT' : c'.started + Consumer.holds c' ≤ T') {a a' : Nat}
    (ha : a + 32 * Consumer.holds c = 32 * T + c.tcPos)
    (ha' : a' + 32 * Consumer.holds c' = 32 * T' + c'.tcPos) (hlt : a' < a) :
    Consumer.vtime T' c' < Consumer.vtime T c := by
  obtain ⟨n, hv1, hv2, hn⟩ := vtime_decomp hx hs0 hT
  obtain ⟨n', hv1', hv2', hn'⟩ := vtime_decomp hx' hs0' hT'
  by_contra hge
  push Not at hge
  have hmono : (n = n' ∧ tcPhase (Consumer.vtime T c - blockAt n) ≤
      tcPhase (Consumer.vtime T' c' - blockAt n')) ∨ n + 1 ≤ n' := by
    simp only [blockAt, blockSpan] at hv1 hv2 hv1' hv2'
    by_cases hnn : n = n'
    · subst hnn
      exact .inl ⟨rfl, tcPhase_mono (by omega)⟩
    · exact .inr (by omega)
  have h1 := tcPhase_le (Consumer.vtime T c - blockAt n)
  have h2 := tcPhase_le (Consumer.vtime T' c' - blockAt n')
  omega

/-- A consumer in its task loop is after the prologue and the register request in the rank table. -/
theorem tc_vtime_big {c : Consumer.D} {T : Nat} (hx : Consumer.exitOff c = none)
    (hs0 : c.site ≠ .setMaxReg) (hT : c.started + Consumer.holds c ≤ T) :
    58 < Consumer.vtime T c := by
  obtain ⟨n, hv1, -, -⟩ := vtime_decomp hx hs0 hT
  simp only [blockAt] at hv1
  omega

/-- A consumer in its exit stage is at no position of a tile. -/
theorem tcPos_exit {c : Consumer.D} (hx : Consumer.exitOff c ≠ none) : c.tcPos = 0 := by
  unfold Consumer.exitOff at hx
  unfold Consumer.D.tcPos
  cases hs : c.site <;> simp_all

/-- The paired Tensor Memory operations of a consumer state are at least its warp's one, and exactly
it in the task loop. -/
theorem tmemOps_cons_ge (w0 : Bool) (c : Consumer.D) :
    (if w0 then 1 else 0) ≤ ThreadD.tmemOps w0 (.inr (.cons c)) := by
  unfold ThreadD.tmemOps
  cases w0 <;> simp
  split <;> omega

theorem tmemOps_cons_loop (w0 : Bool) {c : Consumer.D} (hx : Consumer.exitOff c = none) :
    ThreadD.tmemOps w0 (.inr (.cons c)) = if w0 then 1 else 0 := by
  unfold Consumer.exitOff at hx
  unfold ThreadD.tmemOps
  cases w0 <;> simp
  cases hs : c.site <;> simp_all

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
