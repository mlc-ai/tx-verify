-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.MmaExit

@[expose] public section

/-! # The MMAs' operand reads finish before the CTA they read exits

An MMA of slot `s` reads the stage bytes of both CTAs of its pair (`mma_byteLoc`). Once the CTA of
a byte has exited, a commit of the MMA thread after the MMA tracks it and notified that CTA's empty
barrier before an exit of it (`mma_exit_commit`); the MMA completed, after its reads: so did the
MMA's reads (`readsFinished`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A completed MMA has read its operand bytes: a byte its issue addresses is present. -/
theorem mmaRead_of_done (hX : Consistent L kernel Prod mem0 X) {i : EvId}
    (hdone : X.async.mmaDone i = true) {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue i d sp acc mask) {isB : Bool} {idx : Nat} {l : Loc}
    (hl : sp.byteLoc (if isB then .b else .a) idx = some l)
    (hidx : idx < (if isB then TcMma.Operand.b else .a).bytes sp.descriptor) :
    X.AsyncPresent i (.mmaRead isB idx) := by
  rcases hX.tma.2.1.1 i (hX.tma.2.1.2 i hdone) with
    ⟨d', sp', acc', mask', ops, hi', hops, -, ha, hb⟩ | ⟨c, ops, hc, -⟩ | ⟨c, ops, hc, -⟩
  · obtain ⟨pc, he⟩ := hi
    obtain ⟨pc', he'⟩ := hi'
    rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
    obtain ⟨-, -, rfl, -, -⟩ := he'
    have hlt : idx < (if isB then ops.b else ops.a).length := by
      cases isB <;> simp_all
    obtain ⟨b, hb'⟩ : ∃ b, (if isB then ops.b else ops.a)[idx]? = some b :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    exact ⟨l, b, Or.inl ⟨d, sp, acc, mask, ⟨pc, he⟩, hl⟩, ops, hops, hb'⟩
  · obtain ⟨pc, he⟩ := hi
    obtain ⟨pc', he'⟩ := hc
    rw [he] at he'
    simp at he'
  · obtain ⟨pc, he⟩ := hi
    obtain ⟨pc', he'⟩ := hc
    rw [he] at he'
    simp at he'

/-- **The MMAs' operand reads.** -/
theorem readsFinished (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hcn : CommitNotified L X) : ReadsFinished L X := by
  intro ⟨g, k⟩ isB idx l hfp hex
  rcases hfp with ⟨dst, sp, acc, mask, ⟨pc, he⟩, hl⟩ | ⟨a, src, cta, ⟨pc, he⟩, -, -⟩
  swap
  · exfalso
    have hg := Frame.lt_of_get hX he
    obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
    exact ht.no_tc_cp hg he hσ rfl
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he (by simp)
  obtain ⟨m, s, j, rfl, -, heven, hsp, -⟩ := ht.mma_issue hg he hσ rfl
  -- the byte lies in CTA `g / L.block + idx / 32 / 128` of the pair
  have hsb : L.sharedBase % 128 = 0 := by have := hpre.sharedAlignment; omega
  have hl0 := hl
  rw [hsp] at hl
  obtain ⟨hrow, rfl⟩ := mma_byteLoc L (g / L.block) (g % L.block / 32) s j _ hsb hl
  simp only [stageByte] at hex ⊢
  have hr : idx / 32 / 128 < 2 := by omega
  have hT : g / L.block / 2 * 2 + idx / 32 / 128 =
      g / L.block + (⟨idx / 32 / 128, by omega⟩ : Fin 16).val := by
    show _ = g / L.block + idx / 32 / 128
    omega
  rw [hT] at hex ⊢
  -- the commit after the MMA completed it, and its notification finished before the exit
  obtain ⟨kc, htrack, ⟨hnot, finish, pcx, hft, hfc, hfx, hchain⟩, hdone⟩ :=
    mma_exit_commit hpre hX ht hcn he (r := ⟨idx / 32 / 128, by omega⟩) hr hex
  have hidx : idx < (if isB then TcMma.Operand.b else .a).bytes sp.descriptor := by
    rw [hsp]
    cases isB <;> simp [TcMma.Operand.bytes, TcMma.Operand.rows, TcMma.Operand.extent, mmaSpec,
      mmaDescriptor, TcMma.Kind.k, TcMma.Kind.width] <;> omega
  have hrp := mmaRead_of_done hX hdone ⟨pc, he⟩ hl0 hidx
  have hdp : X.AsyncPresent (g, k) .mmaDone := hdone
  have hnp : X.AsyncPresent (g, kc) (.tcNotify ⟨idx / 32 / 128, by omega⟩) := hnot
  refine ⟨hrp, finish, pcx, hft, hfc, hfx, ?_⟩
  have hdone : CompletedBefore L kernel Prod X (.async (g, k) .mmaDone) (.thread finish, false) :=
    CompletedBefore.of_stage hchain hnp (.inr ⟨rfl, rfl, htrack, hdp, hnp⟩)
  exact CompletedBefore.of_stage hdone hdp (.inr ⟨rfl, rfl, rfl, hrp, hdp⟩)

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
