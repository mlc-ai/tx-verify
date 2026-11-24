-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.EpBcast
public import Kernels.InklingRelDecode.Proof.Interface.FrEpi
public import Kernels.InklingRelDecode.Proof.Interface.Lk4Static
public import Kernels.InklingRelDecode.Proof.Interface.SmBw

@[expose] public section

/-!
# The epilogue's load is at the warp's lanes

The epilogue's machine records the lane bits its broadcast returned (`Epi.Prm.bw`) and loads at
`Prm.taddr`, the lane bits shifted to bit 21 plus the column base. The state at the load comes
from the broadcast (`Epi.next`), whose received word is the warp index (`epi_recv`), so the lane
bits are the warp index (`epi_bw`) and every epilogue state's lane bits are 0 or the warp index.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The state the epilogue's machine reaches from its broadcast has the received word's lane
bits. -/
theorem epi_next_ld {d0 d : Epi.D} {e : Event} (h : Epi.next d0 e = some (some d))
    (hs : d.site = .ld) :
    d0.site = .shfl ∧ ∃ pc m av b c recv ok, e = ⟨pc, .shfl m av b c recv ok⟩ ∧
      Raw.laneOk d0.pr.w recv = some d.pr.bw := by
  obtain ⟨site, pr, o, sk⟩ := d0
  obtain ⟨pc, kd⟩ := e
  cases site <;> simp only [Epi.next] at h
  all_goals try (
    exfalso
    repeat' split at h
    all_goals first
      | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
      | (simp only [Option.some.injEq] at h; subst h; simp [Epi.D.stores] at hs
         repeat' split at hs
         all_goals simp_all)
      | (simp only [Option.some.injEq] at h; subst h; simp [Epi.stNext] at hs
         split at hs <;> simp_all)
    done)
  refine ⟨rfl, ?_⟩
  cases kd
  case shfl m av b c recv ok =>
    refine ⟨pc, m, av, b, c, recv, ok, rfl, ?_⟩
    cases hl : Raw.laneOk pr.w recv with
    | none => simp [hl] at h
    | some x =>
      simp only [hl, Option.some.injEq] at h
      subst h
      rfl
  all_goals simp at h

/-- **At the epilogue's load the recorded lane bits are the warp index.** -/
theorem epi_bw (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {d : Epi.D}
    (hσ : St Q L X g k = some (some (.d (.epi d)))) (hs : d.site = .ld) :
    d.pr.bw = d.pr.w := by
  obtain ⟨k', hk', hσ'⟩ : ∃ k', k' ≤ (X.tr g).length ∧
      St Q L X g k' = some (some (.d (.epi d))) := by
    by_cases h : k ≤ (X.tr g).length
    · exact ⟨k, h, hσ⟩
    · exact ⟨_, le_rfl, (Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := k)
        (by omega)).symm.trans hσ⟩
  rcases pred_d hk' hσ' with ⟨-, hs0⟩ | ⟨k0, e, s0, rfl, he, hσ0, hn⟩
  · simp [DStart.D.start] at hs0
  · rcases dnext_epi_pr hn with ⟨dsm, rfl, hpr⟩ | ⟨d0, rfl, hn'⟩
    · exfalso
      change DComp.smNext L g dsm e = _ at hn
      unfold DComp.smNext at hn
      split at hn
      · unfold DComp.exitNext at hn
        split at hn
        · simp only [Option.some.injEq, DComp.St.epi.injEq] at hn
          subst hn
          split at hs <;> simp [Epi.D.entry, Epi.D.start, Epi.D.startSk] at hs
        · cases hn
      · obtain ⟨a, -, ha⟩ := map_map_eq_some_some hn
        cases ha
    · obtain ⟨hs0, pc, m, av, b, c, recv, ok, rfl, hl⟩ := epi_next_ld hn' hs
      have hget : X.get (g, k0) = some ⟨pc, .shfl m av b c recv ok⟩ := he
      have hr := epi_recv hpre hX hf hg hget hσ0 hs0
      have hm0 : Epi.Means Q L g d0.pr := (hf.reach hg hσ0).2
      have hw4 : d0.pr.w < 4 := by
        have : g % L.block < 128 := (hf.reach hg hσ0).1
        rw [hm0.w]
        omega
      have hpr := Epi.next_pr hn'
      rw [hr, ← hm0.w] at hl
      simp only [Raw.laneOk, Raw.word32Of_b32] at hl
      have h1 : d0.pr.w % 2 ^ 32 % 4 = d0.pr.w := by omega
      simp only [h1, or_true, ↓reduceIte, Option.some.injEq] at hl
      rw [hpr]
      exact hl.symm

/-- **`BwW` at every state of a thread.** -/
theorem bwW_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {s : TSt}
    (hσ : St Q L X g k = some (some s)) : BwW L g s := by
  cases s with
  | d s =>
    cases s with
    | epi d => exact fun hs => epi_bw hpre hX hf hg hσ hs
    | sm d => exact fun hs => sm_bw' hpre hX hf hg hσ hs
    | _ => trivial
  | w s => trivial

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
