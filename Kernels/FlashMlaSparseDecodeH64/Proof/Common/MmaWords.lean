-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWon
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Machine
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Nc

@[expose] public section

/-! # The MMA lane's length words are the launch's
-- domain: consistent

After the election the MMA lane records the parameters (the CTA is inside the batch,
`batch_in`) and then the words its two `.nc` length loads read, the row's words in a consistent
execution (`next_topk`, `next_extra`, `Mma/Nc.lean`); every other step keeps them
(`Mma.words_step`). So from the first Q load on the words are `lenWA`, `lenWB`
(`mma_words`), and the role's block count is the CTA's (`mma_rounds`). -/

/-! # The MMA warp reaches the trap only below the total's test

-- domain: consistent

Every state the machine reaches by a step that is at the trap records the two length words
whose padded total fails the test of the code (pcs 1887-1895): `succ_trapC`. The trap is built
only by `lensD`; no other transition builds it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The trap's total test: the padded total of the recorded lengths is not above 63. -/
def TrapC (x : Mma.D) : Prop :=
  x.site = .trap → Arith32.scmpi .gt .s (Mma.r27 x.l0 x.l1) 63 = false

theorem lensD_trapC (d : Mma.D) (a b : BitVec 64) : TrapC (Mma.lensD d a b) := by
  unfold TrapC Mma.lensD
  split_ifs with h
  · intro h'; cases h'
  · intro _; simpa using h

theorem afterTopk_trapC (d : Mma.D) (a : BitVec 64) : TrapC (Mma.afterTopk P d a) := by
  unfold Mma.afterTopk
  split
  · exact lensD_trapC _ _ _
  · intro h; cases h

theorem leadNext_trapC (d : Mma.D) : TrapC (Mma.leadNext P L g d) := by
  unfold Mma.leadNext
  split
  · intro h; cases h
  · split
    · exact afterTopk_trapC _ _
    · intro h; cases h

theorem loopEntry_trapC (d : Mma.D) : TrapC (Mma.loopEntry d) := by
  unfold Mma.loopEntry
  split <;> intro h <;> cases h

theorem loopEnd_trapC (d : Mma.D) : TrapC (Mma.loopEnd d) := by
  unfold Mma.loopEnd
  split <;> intro h <;> cases h

theorem succ_trapC {d a : Mma.D} {f : Event} (h : Mma.succ P L g d f = some (some a)) :
    TrapC a := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp only [Mma.succ, Mma.poll, Mma.ncWord] at h
  all_goals ((repeat' split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h)
  all_goals subst h
  all_goals first
    | with_reducible exact leadNext_trapC _
    | with_reducible exact afterTopk_trapC _ _
    | with_reducible exact lensD_trapC _ _ _
    | with_reducible exact loopEntry_trapC _
    | with_reducible exact loopEnd_trapC _
    | (simp only [TrapC]; intro h; cases h)
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **The words an MMA state after the election has recorded.** -/
def mmaWordsOk (P : Params) (L : Launch) (g : Nat) (d : Mma.D) : Prop :=
  match d.site with
  | .loadTopk => d.l1 = pw P.extra_topk
  | .loadExtra => d.l0 = lenWA P L (g / L.block)
  | .trap => d.l0 = lenWA P L (g / L.block) ∧ d.l1 = lenWB P L (g / L.block) ∧
      Arith32.scmpi .gt .s (Mma.r27 d.l0 d.l1) 63 = false
  | _ => d.l0 = lenWA P L (g / L.block) ∧ d.l1 = lenWB P L (g / L.block)

/-- The MMA states after the election with their words. -/
def MmaWordsR : (thread P L g).D → Prop :=
  SubR .mma fun d => Mma.Post d.site ∧ mmaWordsOk P L g d

private theorem ok_of {d : Mma.D} (ht : d.site ≠ .loadTopk) (hx : d.site ≠ .loadExtra)
    (h0 : d.l0 = lenWA P L (g / L.block)) (h1 : d.l1 = lenWB P L (g / L.block))
    (hq : TrapC d) : mmaWordsOk P L g d := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site with
  | loadTopk => exact absurd rfl ht
  | loadExtra => exact absurd rfl hx
  | trap => exact ⟨h0, h1, hq rfl⟩
  | _ => exact ⟨h0, h1⟩

private theorem words_of {d : Mma.D} (ht : d.site ≠ .loadTopk) (hx : d.site ≠ .loadExtra)
    (h : mmaWordsOk P L g d) :
    d.l0 = lenWA P L (g / L.block) ∧ d.l1 = lenWB P L (g / L.block) := by
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site with
  | loadTopk => exact absurd rfl ht
  | loadExtra => exact absurd rfl hx
  | trap => exact ⟨h.1, h.2.1⟩
  | _ => exact h

/-- The lengths' words after the first length `a`, the launch's. -/
private theorem ok_lens {d : Mma.D} {a b : BitVec 64} (ha : a = lenWA P L (g / L.block))
    (hb : b = lenWB P L (g / L.block)) : mmaWordsOk P L g (Mma.lensD d a b) := by
  unfold Mma.lensD
  split
  · exact ⟨ha, hb⟩
  · exact ⟨ha, hb, Bool.eq_false_iff.mpr ‹_›⟩

private theorem ok_after {d : Mma.D} {a : BitVec 64} (ha : a = lenWA P L (g / L.block))
    (hb : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = true → d.l1 = lenWB P L (g / L.block)) :
    mmaWordsOk P L g (Mma.afterTopk P d a) := by
  unfold Mma.afterTopk
  split
  · exact ok_lens ha (hb ‹_›)
  · exact ha

/-- **The elected lane's first state records the launch's words** (or the parameters before
the loads). -/
theorem lead_ok (hp : Pre P L m) (d : Mma.D) : mmaWordsOk P L g (Mma.leadNext P L g d) := by
  unfold Mma.leadNext
  simp only [batch_in hp g, Bool.false_eq_true, ite_false]
  split
  · rename_i hA
    apply ok_after
    · simp only [lenWA, hA, ite_true]
    · intro hB
      simp only [lenWB, hB, ite_true]
  · simp only [mmaWordsOk]

/-- **The thread state behind an MMA event.** -/
theorem mma_fired (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {d : Mma.D} {n : Cls → Nat} (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hσ : Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n))) :
    ∃ t ins o, (Mma.code P L g).AtD d t ∧ kernel.code[(Mma.code P L g).pc d]? = some ins ∧
      Fires ((Mma.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
  exact ⟨t, ins, o, hat, hc, hf⟩

/-- A step of the MMA lane after the election keeps its words. -/
private theorem step_ok (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i : Nat} {f : Event} {d a : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g i =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)))
    (hf : (X.tr g)[i]? = some f) (hP : Mma.Post d.site) (hok : mmaWordsOk P L g d)
    (ha : Mma.succ P L g d f = some (some a)) : mmaWordsOk P L g a := by
  have hget : X.get (g, i) = some f := hf
  have hJ := (follow_iff.mp hFw g (Frame.lt_of_get hX hget) i).2 _ hσ
  obtain ⟨-, ⟨-, -, ⟨-, hso⟩, -⟩, -, -⟩ := hJ
  have nub {s : Mma.Site} (hs : d.site = s) (hs' : s = .loadTopk ∨ s = .loadExtra) :
      ∀ fl, f.kind ≠ .ub fl := by
    intro fl hk
    rcases hs' with rfl | rfl <;> simp [Mma.succ, hs, Mma.ncWord, hk] at ha
  by_cases ht : d.site = .loadTopk
  · obtain ⟨t, ins, o, hat, hc, hf'⟩ := mma_fired hp hX hget (nub ht (.inl rfl)) hσ
    obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
    simp only at ht
    subst ht
    rw [Mma.next_topk hp hX hget hso hat hc hf', Option.some.injEq, Option.some.injEq] at ha
    subst ha
    have hA := hso.1 rfl
    simp only [mmaWordsOk] at hok
    apply ok_after
    · simp only [lenWA, hA, rowOf_cta, Bool.false_eq_true, ite_false]
    · intro hB
      simp only [lenWB, hB, hok, ite_true]
  by_cases hx : d.site = .loadExtra
  · obtain ⟨t, ins, o, hat, hc, hf'⟩ := mma_fired hp hX hget (nub hx (.inr rfl)) hσ
    obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
    simp only at hx
    subst hx
    rw [Mma.next_extra hp hX hget hso hat hc hf', Option.some.injEq, Option.some.injEq] at ha
    subst ha
    have hB := hso.2.1 rfl
    simp only [mmaWordsOk] at hok
    apply ok_lens hok
    simp only [lenWB, hB, rowOf_cta, Bool.false_eq_true, ite_false]
  obtain ⟨h0, h1, ht', hx'⟩ := Mma.words_step hP.1 ht hx ha
  obtain ⟨w0, w1⟩ := words_of ht hx hok
  exact ok_of ht' hx' (h0.trans w0) (h1.trans w1) (succ_trapC ha)

/-- **The MMA lane's states after its election record the launch's words**
(`mmaWordsOk`). -/
theorem mma_words_of (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j i : Nat} {inst : Nat}
    (hj : X.get (g, j) = some ⟨1853, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩) (hji : j < i)
    {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    MmaWordsR σ := by
  obtain ⟨σj, hσj, hJj, hij, hevj, hpcj⟩ := ev_at hp hX hFw hj (fun _ h => by cases h)
  obtain ⟨dj, nj, rfl, -, hEj, hlj, -⟩ := mma_state hJj hij hevj hpcj
    ⟨show 1850 ≤ 1853 by decide, show 1853 < 2162 by decide⟩
  obtain ⟨hsj, -, -⟩ := Mma.ev_elect hlj hEj
  have hn : Frame.stateAt (thread P L) X g (j + 1) = (thread P L g).toMachine.next (some
      (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, dj⟩⟩, nj)) ⟨1853, .elect (2 ^ 32 - 1) inst
        (PTX.laneOf L g)⟩ := by
    rw [Frame.stateAt_succ hj, hσj]
    rfl
  have hb : ∀ a, (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g) (.inl .mma)).next dj
      ⟨1853, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩ = some (some a) →
      subBack P L g .mma a = none := fun a ha => by
    simp only [Code.withStubsAt] at ha
    simp [Mma.succ, hsj] at ha
    subst ha
    simp [subBack, (Mma.lead_post (P := P) (L := L) (g := g) dj).2 _]
  cases hn' : (thread P L g).toMachine.next (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, dj⟩⟩, nj))
      ⟨1853, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩ with
  | none =>
    rw [hn'] at hn
    have := Frame.stateAt_none_mono hn (show j + 1 ≤ i by omega)
    rw [hσ] at this
    cases this
  | some o =>
    cases o with
    | none => simp [Code.toMachine, Mma.succ, hsj] at hn'
    | some σ1 =>
      rw [hn'] at hn
      obtain ⟨a, ha, rfl⟩ := sub_step hn' (hb)
      simp only [Code.withStubsAt] at ha
      simp only [Mma.succ, hsj, ↓reduceIte, Option.some.injEq] at ha
      subst ha
      refine region_stays_ev MmaWordsR (j := j + 1) ?_ hn
        ⟨_, _, rfl, Mma.lead_post dj, lead_ok hp dj⟩ i (by omega) σ hσ
      rintro i0 σ0 σ' f - hσ0 ⟨d, n, rfl, hP, hl⟩ hf hn0
      obtain ⟨a, ha, rfl⟩ := sub_step hn0 fun a ha =>
        by simp [subBack, (Mma.succ_post (P := P) (L := L) (g := g) hP ha).2 _]
      exact ⟨a, _, rfl, Mma.succ_post hP ha, step_ok hp hX hFw hσ0 hf hP hl ha⟩

/-- **The MMA lane's states after an event of the MMA code after the election record the
launch's words** (`mmaWordsOk`). -/
theorem mma_words (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 1853 < e.pc ∧ e.pc < 2162) {i : Nat} (hki : k ≤ i)
    {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    MmaWordsR σ := by
  obtain ⟨j, hjk, inst, hj⟩ := mma_won hp hX hFw he hub hr
  exact mma_words_of hp hX hFw hj (by omega) hσ

/-- **The MMA lane's block count is the CTA's**: at a state after the length loads of a lane
with an event of the MMA code after the election, the blocks of the recorded words are
`blocksOf P L (g / L.block)`. -/
theorem mma_rounds (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 1853 < e.pc ∧ e.pc < 2162) {i : Nat} (hki : k ≤ i) {d : Mma.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g i =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)))
    (ht : d.site ≠ .loadTopk) (hx : d.site ≠ .loadExtra) :
    Mma.rounds d.l0 d.l1 = blocksOf P L (g / L.block) := by
  obtain ⟨d', n', heq, -, hok⟩ := mma_words hp hX hFw he hub hr hki hσ
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at heq
  obtain ⟨rfl, -⟩ := heq
  obtain ⟨h0, h1⟩ := words_of ht hx hok
  rw [h0, h1]
  simp only [Mma.rounds, blocksOf, roundsOf, nblkL, totL_eq, Mma.r27, Mma.nblk, Mma.pad, padL]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
