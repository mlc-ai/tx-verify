-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmReuseSingle

@[expose] public section

/-! # The first dequantized write belongs to block zero -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmReuseBlockZero

open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

private def passedFirstStore : Wg2.Site → Bool
  | .scale r _ => decide (0 < r.val)
  | .raw r k => decide (0 < r.val ∨ 1 < k.val)
  | .store r k => decide (0 < r.val ∨ 0 < k.val)
  | .fence | .ready | .free | .barrier => true
  | _ => false

private def passedZeroStore (d : Wg2.D) : Prop :=
  0 < d.block ∨ passedFirstStore d.site = true

private theorem follows_store {d d' : Wg2.D} {e : Event}
    (hn : Wg2.next P L g d e = some (some d')) (h : passedZeroStore d') :
    passedZeroStore d ∨
      (d.block = 0 ∧ d.site = .store 0 0 ∧ ∃ a bs, e.kind = .wr a bs) := by
  by_cases hb : 0 < d.block
  · exact .inl (.inl hb)
  cases hd : d.site <;> simp only [Wg2.next, Wg2.nextSite, hd] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp only [passedZeroStore, hd, passedFirstStore, decide_eq_true_eq] at h ⊢
    try simp only [Wg2.lenOrigNext, Wg2.lenExtraNext, Wg2.init, Wg2.afterScale, Wg2.afterRaw,
      Wg2.afterStore, Wg2.afterFree] at h
    repeat' split_ifs at h
    all_goals try (simp_all; done)
    all_goals try (left; omega)
    all_goals by_cases hzero : d.site = .store 0 0
    all_goals first
      | (right; exact ⟨by omega, hd.symm.trans hzero, ⟨_, _, by assumption⟩⟩)
      | (left; rw [hd, Wg2.Site.store.injEq] at hzero
         simp only [Fin.ext_iff, Fin.val_zero] at hzero
         omega)

private def witness (P : Params) (L : Launch) (g : Nat) (pre : List Event) : Prop :=
  ∃ j d e u, pre[j]? = some e ∧
    (Machine.machine P L g).after (some (.prologue .shfl0)) (pre.take j) =
      some (some (.wg2 d)) ∧
    d.site = .store 0 0 ∧ d.block = 0 ∧
    (Machine.machine P L g).Fired (some (.wg2 d)) e (some u)

private def needsWitness : Option Machine.ThreadD → Prop
  | some (.wg2 d) => passedZeroStore d
  | _ => False

private def history (P : Params) (L : Launch) (g : Nat)
    (s : Option Machine.ThreadD) (pre : List Event) : Prop :=
  (Machine.machine P L g).after (some (.prologue .shfl0)) pre = some s ∧
    (needsWitness s → witness P L g pre)

private theorem witness_append {pre : List Event} {e : Event} (h : witness P L g pre) :
    witness P L g (pre ++ [e]) := by
  obtain ⟨j, d, f, u, hf, ha, hd, hb, hfire⟩ := h
  have hj := (List.getElem?_eq_some_iff.mp hf).1
  refine ⟨j, d, f, u, ?_, ?_, hd, hb, hfire⟩
  · rwa [List.getElem?_append_left hj]
  · rwa [List.take_append_of_le_length hj.le]

private theorem witness_step {d : Wg2.D} {pre : List Event} {e : Event} {o : Option TState}
    (ha : (Machine.machine P L g).after (some (.prologue .shfl0)) pre =
      some (some (.wg2 d)))
    (hf : (Machine.machine P L g).Fired (some (.wg2 d)) e o)
    (hs : d.site = .store 0 0) (hb : d.block = 0) (hk : ∃ a bs, e.kind = .wr a bs) :
    witness P L g (pre ++ [e]) := by
  cases o with
  | none =>
    obtain ⟨t, _, hf⟩ := hf
    obtain ⟨a, bs, hk⟩ := hk
    rcases fires_none_ends hf with ⟨f, h⟩ | h <;> rw [hk] at h <;> cases h
  | some u =>
    exact ⟨pre.length, d, e, u, by simp, by
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      exact ha, hs, hb, hf⟩

private theorem history_step {s s' : Option Machine.ThreadD}
    {pre : List Event} {e : Event} {o : Option TState}
    (h : history P L g s pre) (hf : (Machine.machine P L g).Fired s e o)
    (hn : (Machine.machine P L g).next s e = some s') :
    history P L g s' (pre ++ [e]) := by
  refine ⟨?_, ?_⟩
  · rw [Machine.after_snoc (M := Machine.machine P L g) (some (.prologue .shfl0)) pre e, h.1]
    exact hn
  intro hw
  cases s with
  | none =>
    change some none = some s' at hn
    cases hn
    exact hw.elim
  | some s =>
    change Machine.next P L g s e = some s' at hn
    cases s
    case wg2 d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hnext
        cases hn
        rcases follows_store hnext hw with hp | ⟨hb, hs, hk⟩
        · exact witness_append (h.2 hp)
        · exact witness_step h.1 hf hs hb hk
      · split_ifs at hn <;> cases hn <;> exact hw.elim
      · cases hn
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        exact hw.elim
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn
            all_goals try exact hw.elim
            change passedZeroStore (Wg2.init P L g) at hw
            simp only [passedZeroStore, Wg2.init, Wg2.firstSite] at hw
            split_ifs at hw <;> simp [passedFirstStore] at hw
          · cases hn
            exact hw.elim
        · cases hn
          exact hw.elim
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> exact hw.elim
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals exact hw.elim

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmReuseBlockZero

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX PTX.Flow

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
