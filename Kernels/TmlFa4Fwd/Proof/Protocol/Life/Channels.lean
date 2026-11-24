-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Def
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.KV
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Q
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Use
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Mbar
import Lemmas.Kernel.SharedLifetime

@[expose] public section

/-! # The channels' asynchronous uses end before their CTA's exit

The empty barriers' releases are the K/V ring's and the Q stages' (`empties_finished`). A tensor
load is a Q stage's or a bias stage's, and its writes precede its arrival (`loads_finished`). So
shared memory has no unsafe use once the bias loads end (`no_sharedLifetime`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The empty barriers' commits' arrive-ons end before their CTA's exit.** -/
theorem empties_finished : EmptiesFinished L kernel Assumptions.all X := by
  rintro ⟨h, k⟩ s rank l ⟨pc, he⟩ ht hno hx
  simp only at hno hx ⊢
  have hbase : ∀ o, (⟨.shared, h / L.block, L.sharedBase + o⟩ : Loc) = obj L h o := fun _ => rfl
  have hw : Prologue.warpIndex L h = 12 := by
    have h16 := Prologue.warpIndex_lt hp h
    rcases show Prologue.warpIndex L h < 8 ∨
        (8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11) ∨ Prologue.warpIndex L h = 12 ∨
        Prologue.warpIndex L h = 13 ∨
        (Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15) by omega with
      hw | hw | hw | hw | hw
    · rcases soft_mbar_use hp hX hFw hw he (l := l) ⟨rank, ht⟩ (fun _ h => by cases h) with
        ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;> cases hk
    · rcases corr_mbar_use hp hX hFw hw.1 hw.2 he (l := l) ⟨rank, ht⟩ (fun _ h => by cases h) with
        ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;> cases hk
    · exact hw
    · rcases epi_mbar_use hp hX hFw hw he (l := l) ⟨rank, ht⟩ (fun _ h => by cases h) with
        ⟨_, _, _, hk, _⟩ | ⟨_, _, hk, _⟩ <;> cases hk
    · rcases ld_mbar_use hp hX hFw hw he (l := l) ⟨rank, ht⟩ (fun _ h => by cases h) with
        ⟨_, _, _, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, _, hk, _⟩ <;> cases hk
  rcases mma_mbar_use hp hX hFw hw he (l := l) ⟨rank, ht⟩ (fun _ h => by cases h) with
    ⟨_, _, _, _, hk⟩ | ⟨o, s', ho, rfl, -, -, -, -⟩
  · cases hk
  have h0 := hno 0 (by omega)
  have h1 := hno 1 (by omega)
  have hkv : ∀ t : Fin 3, o = 56 + 8 * t.val → SharedFinished L kernel Assumptions.all X
      (.async (h, k) (.tcNotify rank)) (h / L.block) := by
    rintro t rfl
    exact kv_empty_finished hp hX hFw t he ht hx
  have hq : ∀ t : Fin 2, o = 8 * t.val + 16 → SharedFinished L kernel Assumptions.all X
      (.async (h, k) (.tcNotify rank)) (h / L.block) := by
    rintro t rfl
    exact q_empty_finished hp hX hFw t he ht hx
  rcases ho with h | h | h | h | h | h | h | h | h
  · exact hq 0 h
  · exact hq 1 h
  · exact hkv 0 h
  · exact hkv 1 h
  · exact hkv 2 h
  · exact absurd (by rw [h]) h0.1
  · exact absurd (by rw [h]) h1.1
  · exact absurd (by rw [h]) h0.2
  · exact absurd (by rw [h]) h1.2

/-- **The tensor loads end before their CTA's exit**, once the bias loads do. -/
theorem loads_finished (hb : BiasLoadsFinished L kernel Assumptions.all X) :
    LoadsFinished L kernel Assumptions.all X := by
  rintro ⟨h, k⟩ a s ⟨pc, he⟩ hx
  simp only at hx ⊢
  have hfin : SharedFinished L kernel Assumptions.all X (.async (h, k) (.notify .load))
      (h / L.block) := by
    have hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15 := by
      have h16 := Prologue.warpIndex_lt hp h
      rcases show Prologue.warpIndex L h < 8 ∨
          (8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11) ∨ Prologue.warpIndex L h = 12 ∨
          Prologue.warpIndex L h = 13 ∨
          (Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15) by omega with
        hw | hw | hw | hw | hw
      · rcases soft_mbar_use hp hX hFw hw he (l := s.mbar) rfl (fun _ h => by cases h) with
          ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;> cases hk
      · rcases corr_mbar_use hp hX hFw hw.1 hw.2 he (l := s.mbar) rfl (fun _ h => by cases h) with
          ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ <;> cases hk
      · rcases mma_mbar_use hp hX hFw hw he (l := s.mbar) rfl (fun _ h => by cases h) with
          ⟨_, _, _, _, hk⟩ | ⟨_, _, _, _, hk, _⟩ <;> cases hk
      · rcases epi_mbar_use hp hX hFw hw he (l := s.mbar) rfl (fun _ h => by cases h) with
          ⟨_, _, _, hk, _⟩ | ⟨_, _, hk, _⟩ <;> cases hk
      · exact hw
    rcases ld_mbar_use hp hX hFw hw he (l := s.mbar) rfl (fun _ h => by cases h) with
      ⟨_, _, _, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, _, _, hk⟩ | ⟨o, _, _, ho, hl, hk, -⟩
    · cases hk
    · cases hk
    · cases hk
    rcases ho with rfl | rfl | rfl | rfl
    · exact q_load_finished hp hX hFw 0 ⟨pc, he⟩ hl hx
    · exact q_load_finished hp hX hFw 1 ⟨pc, he⟩ hl hx
    · exact hb _ _ _ ⟨pc, he⟩ ⟨0, by omega, hl⟩ hx
    · exact hb _ _ _ ⟨pc, he⟩ ⟨1, by omega, hl⟩ hx
  refine ⟨fun x y kk hsl => ?_, hfin⟩
  obtain ⟨o, hto, hnot⟩ := hfin.1
  obtain ⟨slot, hslot⟩ := Option.isSome_iff_exists.mp hsl
  have hspec : o.spec = s := by
    obtain ⟨a', pc', hio⟩ := (hX.effectValidity.tensor (h, k) o hto).1
    rw [he] at hio
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hio
    exact hio.2.2.symm
  subst hspec
  obtain ⟨v, hv⟩ := (hX.effectValidity.tensor (h, k) o hto).2.1.complete hnot slot
  have hwp : X.AsyncPresent (h, k) (.write (.load x y kk)) := ⟨o, slot, v, hto, hslot, hv⟩
  exact SharedFinished.of_stage (j := (h, k)) (q := .notify .load) hwp
    (.inr ⟨rfl, rfl, rfl, rfl, hwp, o, hto, hnot⟩) hfin

/-- **No use of a CTA's shared memory is unsafe**, once the bias loads end before their CTA's
exit. -/
theorem no_sharedLifetime (hb : BiasLoadsFinished L kernel Assumptions.all X) :
    ¬ SharedLifetimeUnsafe L kernel Assumptions.all X :=
  no_sharedLifetimeUnsafe hp hX hFw (loads_finished hp hX hFw hb) (rows_finished hp hX hFw)
    (arrives_finished hp hX hFw) (empties_finished hp hX hFw)

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Life
