-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLen
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Tma
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Nc

@[expose] public section

/-! # The TMA lane's length words are the launch's
-- domain: consistent

After the election the winner records the parameters (the CTA is inside the batch, `batch_in`)
and then the words its two `.nc` length loads read, the row's words in a consistent execution
(`load_next`, `Common/TmaLen.lean`); every other step keeps them (`Tma.words_step`). So from the
wait on `bar_q_utccp` on the words are `lenWA`, `lenWB` (`tma_words`) and the role's block count
is the CTA's (`tma_rounds_of`). With the reference invariant (`tma_win_state`), the state behind
the winner's exit follows its CTA barrier with every block's counts (`tma_exit_full`). For the
TMA role's time exports (`Tma/Export/Time.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **The words a TMA state after the election has recorded.** -/
def tmaWordsOk (P : Params) (L : Launch) (g : Nat) (d : Tma.D) : Prop :=
  match d.site with
  | .loadTopk => d.l1 = pw P.extra_topk
  | .loadExtra => d.l0 = lenWA P L (g / L.block)
  | _ => d.l0 = lenWA P L (g / L.block) ∧ d.l1 = lenWB P L (g / L.block)

private theorem ok_of {d : Tma.D} (ht : d.site ≠ .loadTopk) (hx : d.site ≠ .loadExtra)
    (h0 : d.l0 = lenWA P L (g / L.block)) (h1 : d.l1 = lenWB P L (g / L.block)) :
    tmaWordsOk P L g d := by
  obtain ⟨site, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
  cases site with
  | loadTopk => exact absurd rfl ht
  | loadExtra => exact absurd rfl hx
  | _ => exact ⟨h0, h1⟩

/-- The words of a state off the length loads. -/
theorem tma_words_of_ok {d : Tma.D} (ht : d.site ≠ .loadTopk) (hx : d.site ≠ .loadExtra)
    (h : tmaWordsOk P L g d) :
    d.l0 = lenWA P L (g / L.block) ∧ d.l1 = lenWB P L (g / L.block) := by
  obtain ⟨site, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ := d
  cases site with
  | loadTopk => exact absurd rfl ht
  | loadExtra => exact absurd rfl hx
  | _ => exact h

private theorem ok_after {d : Tma.D} {a : BitVec 64} (ha : a = lenWA P L (g / L.block))
    (hb : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true → d.l1 = lenWB P L (g / L.block)) :
    tmaWordsOk P L g (Tma.afterTopk P d a) := by
  unfold Tma.afterTopk
  split
  · exact ⟨ha, hb ‹_›⟩
  · exact ha

/-- **The elected lane's first state records the launch's words** (or the parameters before
the loads). -/
theorem tma_lead_ok (hp : Pre P L m) (d : Tma.D) : tmaWordsOk P L g (Tma.leadNext P L g d) := by
  unfold Tma.leadNext
  simp only [batch_in hp g, Bool.false_eq_true, ite_false]
  split
  · rename_i hA
    apply ok_after
    · simp only [lenWA, hA, ite_true]
    · intro hB
      simp only [lenWB, hB, ite_true]
  · simp only [tmaWordsOk]

/-- A step of the winner keeps its words. -/
private theorem step_ok (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i : Nat} {f : Event} {d a : Tma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g i = some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)))
    (hf : (X.tr g)[i]? = some f) (hP : Tma.Post d.site) (hok : tmaWordsOk P L g d)
    (ha : Tma.succ P L g d f = some (some a)) : tmaWordsOk P L g a := by
  by_cases ht : d.site = .loadTopk
  · obtain ⟨⟨hA, -, -⟩, h1, -⟩ := load_next hp hX hFw (.inl ht) hσ hf ha
    rw [h1 ht]
    simp only [tmaWordsOk, ht] at hok
    apply ok_after
    · simp only [lenWA, hA ht, rowOf_cta, Bool.false_eq_true, ite_false]
    · intro hB
      simp only [lenWB, hB, hok, ite_true]
  by_cases hx : d.site = .loadExtra
  · obtain ⟨⟨-, hB, -⟩, -, h2⟩ := load_next hp hX hFw (.inr hx) hσ hf ha
    rw [h2 hx]
    simp only [tmaWordsOk, hx] at hok
    exact ⟨hok, by simp only [Tma.lensD, lenWB, hB hx, rowOf_cta, Bool.false_eq_true, ite_false]⟩
  obtain ⟨h0, h1, ht', hx'⟩ := Tma.words_step hP.1 ht hx ha
  obtain ⟨w0, w1⟩ := tma_words_of_ok ht hx hok
  exact ok_of ht' hx' (h0.trans w0) (h1.trans w1)

/-- **The winner's states after its election record the launch's words.** -/
theorem tma_words (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j inst : Nat}
    (hj : X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩) {i : Nat}
    (hji : j < i) {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    SubR .tma (fun d => Tma.Post d.site ∧ tmaWordsOk P L g d) σ :=
  tma_region hp hX hFw _ hj (tma_lead_ok hp)
    (fun hσ0 hP hq hf ha => step_ok hp hX hFw hσ0 hf hP hq ha) hji hσ

/-- **The TMA lane's block count is the CTA's** at a state off the length loads. -/
theorem tma_rounds_of {d : Tma.D} (ht : d.site ≠ .loadTopk) (hx : d.site ≠ .loadExtra)
    (h : tmaWordsOk P L g d) : Tma.rounds d.l0 d.l1 = blocksOf P L (g / L.block) := by
  obtain ⟨h0, h1⟩ := tma_words_of_ok ht hx h
  rw [h0, h1]
  rfl

/-- No undefined behaviour in a shorter prefix, in the glued and the role's ledger. -/
theorem ub_zero {i i' : Nat} (h : ((X.tr g).take i).countP (cls .ub) = 0) (hi : i' ≤ i) :
    ((X.tr g).take i').countP (cls .ub) = 0 ∧ ((X.tr g).take i').countP (Tma.cls .ub) = 0 := by
  have hs := List.take_sublist_take_left hi (l := X.tr g)
  have h0 := List.countP_eq_zero.mp h
  refine ⟨List.countP_eq_zero.mpr fun f hf => h0 f (hs.subset hf),
    List.countP_eq_zero.mpr fun f hf hc => h0 f (hs.subset hf) ?_⟩
  obtain ⟨pc, kd⟩ := f
  cases kd with
  | wait l q ok a sc => cases ok <;> simp_all [Tma.cls, Tma.kindOf, cls]
  | _ => simp_all [Tma.cls, Tma.kindOf, cls]

/-- **A later state of the election's winner** is a TMA state after the election with its words
and the reference invariant at the lane's prefix counts, before undefined behaviour. -/
theorem tma_win_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j inst : Nat}
    (hj : X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩) {i : Nat}
    (hji : j < i) {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ))
    (hu : ((X.tr g).take i).countP (cls .ub) = 0) :
    ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n) ∧ Tma.Post d.site ∧
      tmaWordsOk P L g d ∧ Tma.RefCore L g d (fun c => ((X.tr g).take i).countP (Tma.cls c)) := by
  obtain ⟨d, n, rfl, hP, hw⟩ := tma_words hp hX hFw hj hji hσ
  have hJ := (follow_iff.mp hFw g (Frame.lt_of_get hX hj) i).2 _ hσ
  obtain ⟨-, ⟨-, -, ⟨hR, -⟩, -⟩, -, -⟩ := hJ
  obtain ⟨u0, u1⟩ := ub_zero hu (Nat.le_refl i)
  have hR := hR ((state_count hσ .ub).trans u0)
  have hc : ∀ c, n c = ((X.tr g).take i).countP (cls c) := state_count hσ
  simp only [hc] at hR
  exact ⟨d, n, rfl, hP, hw, hR u1⟩

/-- **The state behind the winner's exit follows its CTA barrier**: at an earlier prefix the
lane's counts are every block's (`cntAt` of the CTA's block count, before the barrier). -/
theorem tma_exit_full (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j inst : Nat}
    (hj : X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩) {i : Nat}
    (hji : j < i) (hil : i ≤ (X.tr g).length) (hu : ((X.tr g).take i).countP (cls .ub) = 0)
    {d : Tma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g i = some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)))
    (hx : d.site = .exit) :
    ∃ i', j < i' ∧ i' < i ∧ ∀ c, c ≠ .ub → ((X.tr g).take i').countP (Tma.cls c) =
      Tma.cntAt (Tma.objs L g) 3 (blocksOf P L (g / L.block)) 0 0 0 false c := by
  have hi1 : j + 1 ≠ i := by
    intro h
    subst h
    rcases tma_lead hp hX hFw hj with hn | ⟨dj, nj, hn⟩
    · rw [hn] at hσ
      cases hσ
    · rw [hn] at hσ
      simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff,
        heq_eq_eq] at hσ
      obtain ⟨⟨-, -, -, rfl⟩, -⟩ := hσ
      exact Tma.lead_ne_exit dj (batch_in hp g) hx
  obtain ⟨f, hf⟩ : ∃ f, (X.tr g)[i - 1]? = some f := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hn := Frame.stateAt_succ (C := thread P L) hf
  rw [Nat.sub_add_cancel (by omega), hσ] at hn
  cases hs : Frame.stateAt (thread P L) X g (i - 1) with
  | none => rw [hs] at hn; cases hn
  | some o =>
    cases o with
    | none => exact absurd hs (follow_iff.mp hFw g (Frame.lt_of_get hX hj) _).1
    | some σ0 =>
      rw [hs, Option.bind_some] at hn
      obtain ⟨d0, n0, rfl, hP, hw, hR⟩ := tma_win_state hp hX hFw hj (show j < i - 1 by omega) hs
        (ub_zero hu (show i - 1 ≤ i by omega)).1
      obtain ⟨a, ha, ha'⟩ := sub_step hn.symm fun a ha =>
        by simp [subBack, (Tma.succ_post (P := P) (L := L) (g := g) hP ha).2 _]
      simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq] at ha'
      obtain ⟨⟨-, -, -, rfl⟩, -⟩ := ha'
      have hb := Tma.succ_exit hP ha hx
      have hrd := tma_rounds_of (by rw [hb]; simp) (by rw [hb]; simp) hw
      simp only [Tma.RefCore, hb] at hR
      refine ⟨i - 1, by omega, by omega, fun c hc => ?_⟩
      rw [hR c hc, hrd]

/-- **The winner has an event of the TMA code after the election** once it is past its first
state: its event at `j + 1`, fired from the elected lane's first state. -/
theorem tma_on_of (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j inst : Nat}
    (hj : X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩) {i : Nat}
    (hji : j + 1 < i) (hil : i ≤ (X.tr g).length) (hu : ((X.tr g).take i).countP (cls .ub) = 0) :
    ∃ k e, X.get (g, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ TmaOn L g e.pc := by
  obtain ⟨f, hf⟩ : ∃ f, (X.tr g)[j + 1]? = some f := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hget : X.get (g, j + 1) = some f := hf
  have hm : f ∈ (X.tr g).take i :=
    List.mem_iff_getElem?.mpr ⟨j + 1, by rw [List.getElem?_take_of_lt hji]; exact hf⟩
  have hfu : ∀ fl, f.kind ≠ .ub fl := fun fl hk => List.countP_eq_zero.mp hu f hm (by
    obtain ⟨pc, kd⟩ := f
    simp only at hk
    subst hk
    simp [cls])
  obtain ⟨σ, hσ, -, -, -, hpc⟩ := ev_at hp hX hFw hget hfu
  obtain ⟨σj, hσj, hJj, hij, hevj, hpcj⟩ := ev_at hp hX hFw hj (fun _ h => by cases h)
  obtain ⟨-, -, -, -, -, -, -, hw⟩ := tma_state hJj hij hevj hpcj
    ⟨show 2162 ≤ 2165 by decide, show 2165 < 2332 by decide⟩
  rcases tma_lead hp hX hFw hj with hn | ⟨dj, nj, hn⟩
  · rw [hn] at hσ
    cases hσ
  rw [hn, Option.some.injEq, Option.some.injEq] at hσ
  subst hσ
  have h1 : f.pc = (Tma.leadNext P L g dj).site.pc := hpc
  refine ⟨j + 1, f, hget, hfu, ⟨hw, ?_, ?_⟩, ?_⟩ <;>
    rcases Tma.lead_site dj (batch_in hp g) with h | h | h <;>
    rw [h1, h] <;> decide

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
