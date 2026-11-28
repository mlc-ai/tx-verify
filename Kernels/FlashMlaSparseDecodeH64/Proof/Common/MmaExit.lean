-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWords
import Lemmas.Step.ExitLast

@[expose] public section

/-! # The MMA lane's exit is the closing one

The reference invariant of the MMA role allows two exits (`Mma/Ref.lean`): the early return of a
CTA beyond the batch right after the election, and the exit after the CTA barrier. For a lane with
an event of the MMA code after the election, only the second is reached: the machine enters the
exit from a state after the election only from the barrier (`mma_exit_from`), so an exit state
after that event follows a barrier state (`mma_bar_before`), whose counts (eight Q loads) rule out
the early return's (none); the exit's counts are the full ones (`mma_exit_counts`), those of the
CTA's block count behind an `exit` event (`mma_exit_full`). For the MMA
role's time exports (`Mma/Export/Time.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **From a state after the election the machine enters the exit only from the barrier.** -/
theorem mma_exit_from {d d' : Mma.D} {f : Event} (hP : Mma.Post d.site)
    (h : Mma.succ P L g d f = some (some d')) (hx : d'.site = .exit) (hd : d.site ≠ .exit) :
    d.site = .outBar := by
  obtain ⟨hs, hl⟩ := hP
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp only [Mma.succ, Mma.ncWord, Mma.poll] at h
  case elect => exact absurd rfl hs
  case leave i => exact absurd rfl (hl i)
  case exit => exact absurd rfl hd
  case outBar => rfl
  all_goals ((repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h)
  all_goals simp [Mma.afterTopk, Mma.lensD, Mma.loopEntry, Mma.loopEnd] at hx
  all_goals split_ifs at hx

/-- The counts at the barrier. -/
private theorem bar_cnt {d : Mma.D} {n : Mma.Cnt → Nat} (hc : Mma.RefCore L g d n)
    (hs : d.site = .outBar) : ∀ c, c ≠ .ub → n c = Mma.cntAt (Mma.objs L g) 31
      (Mma.rounds d.l0 d.l1) 0 false c := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  subst hs
  exact hc

/-- The state firing an MMA event after the election is not at the exit. -/
private theorem fire_ne (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (hr : 1853 < e.pc ∧ e.pc < 2162) :
    ∃ d0 n0, Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d0⟩⟩, n0)) ∧ Mma.Post d0.site ∧
      d0.site ≠ .exit := by
  obtain ⟨σ0, hσ0, hJ0, hi0, hev0, hpc0⟩ := ev_at hp hX hFw he hu
  obtain ⟨d0, n0, rfl, -, hE0, hl0, -⟩ := mma_state hJ0 hi0 hev0 hpc0 ⟨by omega, hr.2⟩
  have h1 := hE0.1
  refine ⟨d0, n0, hσ0, ⟨fun h => ?_, hl0⟩, fun h => ?_⟩ <;> rw [h] at h1 <;>
    simp only [Mma.Site.pc] at h1 <;> omega

/-- **An exit state after an MMA event after the election follows a barrier state.** -/
theorem mma_bar_before (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (hr : 1853 < e.pc ∧ e.pc < 2162) :
    ∀ i, k ≤ i → ∀ (d : Mma.D) n, Frame.stateAt (thread P L) X g i =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)) → d.site = .exit →
      ∃ i' < i, ∃ d' : Mma.D, ∃ n', Frame.stateAt (thread P L) X g i' =
        some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d'⟩⟩, n')) ∧ d'.site = .outBar := by
  obtain ⟨d0, n0, hσ0, hP0, hx0⟩ := fire_ne hp hX hFw he hu hr
  have hreg := region_stays PostR post_next hσ0 ⟨d0, n0, rfl, hP0⟩
  intro i
  induction i with
  | zero =>
    intro hk d n hσ hx
    rw [show k = 0 by omega] at hσ0
    rw [hσ0] at hσ
    simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq,
      true_and] at hσ
    rw [hσ.1] at hx0
    exact absurd hx hx0
  | succ i ih =>
    intro hki d n hσ hx
    by_cases hk : k = i + 1
    · subst hk
      rw [hσ0] at hσ
      simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq,
        true_and] at hσ
      rw [hσ.1] at hx0
      exact absurd hx hx0
    cases hf : (X.tr g)[i]? with
    | none =>
      have hl : (X.tr g).length ≤ i := List.getElem?_eq_none_iff.mp hf
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hl] at hσ
      obtain ⟨i', hi', h⟩ := ih (by omega) d n hσ hx
      exact ⟨i', by omega, h⟩
    | some f =>
      rw [Frame.stateAt_succ hf] at hσ
      cases hs : Frame.stateAt (thread P L) X g i with
      | none => rw [hs] at hσ; cases hσ
      | some o =>
        rw [hs] at hσ
        cases o with
        | none => simp [Code.toMachine] at hσ
        | some σ1 =>
          obtain ⟨d1, n1, rfl, hP1⟩ := hreg i (by omega) σ1 hs
          by_cases hx1 : d1.site = .exit
          · obtain ⟨i', hi', h⟩ := ih (by omega) d1 n1 hs hx1
            exact ⟨i', by omega, h⟩
          · obtain ⟨a, ha, hσa⟩ := sub_step hσ fun a ha =>
              by simp [subBack, (Mma.succ_post (P := P) (L := L) (g := g) hP1 ha).2 _]
            simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hσa
            rw [← hσa.1] at ha
            exact ⟨i, by omega, d1, n1, hs, mma_exit_from hP1 ha hx hx1⟩

/-- **The counts at an exit state after an MMA event after the election are the full ones**
(before undefined behaviour). -/
theorem mma_exit_counts (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (hr : 1853 < e.pc ∧ e.pc < 2162) {i : Nat} (hki : k ≤ i) {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g i =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)))
    (hx : d.site = .exit) (hu0 : ((X.tr g).take i).countP (cls .ub) = 0)
    (hu1 : ((X.tr g).take i).countP (Mma.cls .ub) = 0) :
    ∀ c, c ≠ .ub → ((X.tr g).take i).countP (Mma.cls c) =
      Mma.cntAt (Mma.objs L g) 31 (Mma.rounds d.l0 d.l1) 0 true c := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨i', hi', d', n', hσ', hb⟩ := mma_bar_before hp hX hFw he hu hr i hki d n hσ hx
  have hmono : ∀ c, ((X.tr g).take i').countP c ≤ ((X.tr g).take i).countP c := fun c =>
    (List.take_sublist_take_left hi'.le).countP_le
  have href : ∀ {j} {d : Mma.D} {n : Cls → Nat}, Frame.stateAt (thread P L) X g j =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)) → j ≤ i →
      Mma.RefCore L g d (fun c => ((X.tr g).take j).countP (Mma.cls c)) := by
    intro j d n hs hj
    obtain ⟨-, ⟨-, -, ⟨hR, -⟩, -⟩, -, -⟩ := (follow_iff.mp hFw g hg j).2 _ hs
    have hc : ∀ c, n c = ((X.tr g).take j).countP (cls c) := state_count hs
    simp only [hc] at hR
    have h0 : ((X.tr g).take j).countP (cls .ub) = 0 := by
      have := (List.take_sublist_take_left (l := X.tr g) hj).countP_le (p := cls .ub); omega
    have h1 : ((X.tr g).take j).countP (Mma.cls .ub) = 0 := by
      have := (List.take_sublist_take_left (l := X.tr g) hj).countP_le (p := Mma.cls .ub); omega
    exact hR h0 h1
  have hb8 := (bar_cnt (href hσ' hi'.le) hb) .tma (by simp)
  rcases Mma.exit_cnt (href hσ (Nat.le_refl i)) hx with h0 | h0
  · have ha := h0 .tma (by simp)
    have hm := hmono (Mma.cls .tma)
    have z0 : Mma.cntAt (Mma.objs L g) 1 0 0 false .tma = 0 := by
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt]
    have z8 : Mma.cntAt (Mma.objs L g) 31 (Mma.rounds d'.l0 d'.l1) 0 false .tma = 8 := by
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt]
    exfalso
    omega
  · exact h0

/-- **The counts behind an `exit` of a lane with an MMA event after the election** are the full
ones of the CTA's block count. -/
theorem mma_exit_full (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (hr : 1853 < e.pc ∧ e.pc < 2162) {x pc : Nat} (hx : X.get (g, x) = some ⟨pc, .exit⟩) :
    ∀ c, c ≠ .ub → ((X.tr g).take x).countP (Mma.cls c) =
      Mma.cntAt (Mma.objs L g) 31 (blocksOf P L (g / L.block)) 0 true c := by
  have hg := Frame.lt_of_get hX hx
  have hl := Execution.exit_last hX hg hx
  have hk : k ≤ x := by
    have : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    omega
  obtain ⟨d0, n0, hσ0, hP0, -⟩ := fire_ne hp hX hFw he hu hr
  obtain ⟨σ, hσ, -, -, hev, -⟩ := ev_at hp hX hFw hx (fun _ h => by cases h)
  obtain ⟨d, n, rfl, hP⟩ :=
    region_stays PostR post_next hσ0 ⟨d0, n0, rfl, hP0⟩ x hk σ hσ
  have hs : d.site = .exit := by
    obtain ⟨-, hk'⟩ : Mma.Ev L g d ⟨pc, .exit⟩ := hev
    obtain ⟨-, hl'⟩ := hP
    obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
    cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hk' ⊢
    case leave i => exact hl' i rfl
  have hR := mma_rounds hp hX hFw he hu hr hk hσ (by rw [hs]; decide) (by rw [hs]; decide)
  rw [← hR]
  exact mma_exit_counts hp hX hFw he hu hr hk hσ hs
    ((state_count hσ .ub).symm.trans (state_ub hX hσ hx)) (take_noUb hX hx)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
