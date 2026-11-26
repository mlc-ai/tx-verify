-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndex
import Lemmas.Flow.RoleStep

@[expose] public section

/-! # Where the index warp's states come from

`next_into_index`: a step of the thread machine into a state of the index warp is a step of an
index state, or of the head's shuffle (the index warp is entered only by the head's dispatch on
the word `7`). `index_origin`: along a lane's trace, the state before any event at an index state
follows the head's shuffle state at an earlier event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The startup's entry never lands on an index state. -/
theorem enter_top_ne_index {s : (startupCode P L g).D} {d' : Index.D}
    (ha : (startupCode P L g).enter (Code.withStubs (frag P L g) Entry.pc)
      (Code.gatedExit (startupEnter P L g) (sel P L g)) s =
      Sum.inr ⟨Sum.inl Entry.wg1, Sum.inr ⟨Sum.inl SubEntry.index, d'⟩⟩) : False := by
  unfold Code.enter at ha
  split at ha
  · rename_i i _
    simp only [Sum.inr.injEq] at ha
    cases i with
    | inl e =>
      cases e <;> simp only [Sigma.mk.inj_iff, Sum.inl.injEq, reduceCtorEq, false_and] at ha
      obtain ⟨-, h2⟩ := ha
      have h3 := eq_of_heq h2
      simp [Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf] at h3
    | inr r => simp at ha
  · simp at ha

/-- **The index warp is entered from the head's shuffle.** -/
theorem next_into_index {σ σ' : (thread P L g).D} {e : Event}
    (h : (thread P L g).next σ e = some (some σ')) {d' : Index.D} {n' : Cls → Nat}
    (hσ' : σ' = idxState P L g d' n') :
    (∃ d n, σ = idxState P L g d n) ∨ ∃ n, σ = hshState P L g n := by
  obtain ⟨x, n⟩ := σ
  obtain ⟨h1, -⟩ := Code.counted_next_some h
  subst hσ'
  rcases x with s | ⟨i, y⟩
  · exfalso
    simp only [Code.glue, Option.map_eq_some_iff] at h1
    obtain ⟨a, -, a1, rfl, ha⟩ := h1
    exact enter_top_ne_index ha
  · obtain ⟨d2, hd2, hs1⟩ := Code.roleThread_next_role h
    rcases i with i | r
    · cases i
      · simp at hs1
      · simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hs1
        obtain rfl := hs1
        rcases y with s | ⟨j, dj⟩
        · right
          cases s
          all_goals first
            | exact ⟨n, rfl⟩
            | simp [Code.withStubs, frag, wg1Code, Code.roleLoop, Code.loopGlue, Wg1.succ,
                Code.enter, Code.gatedExit, wg1Enter, Wg1.exitOf] at hd2
        · rcases j with j | r
          · have hk : ∀ (i : SubEntry) (dd : (subFrag P L g i).D),
                (wg1Code P L g).next (.inr ⟨Sum.inl i, dd⟩) e =
                  some (some (.inr ⟨Sum.inl SubEntry.index, d'⟩)) → i = SubEntry.index := by
              intro i dd hh
              cases i
              all_goals first
                | rfl
                | (exfalso
                   change (((subFrag P L g _).next dd e).map _) = _ at hh
                   simp only [Option.map_eq_some_iff] at hh
                   obtain ⟨a, -, a1, rfl, ha⟩ := hh
                   unfold Code.backEnter at ha
                   split at ha
                   · rename_i p hp
                     first
                       | (simp only [subBack] at hp; simp at hp; done)
                       | (simp only [subBack] at hp
                          split_ifs at hp
                          obtain rfl := Option.some.inj hp
                          unfold Code.enter at ha
                          simp [Code.gatedExit, wg1Enter, Wg1.exitOf] at ha
                          split at ha
                          · rename_i hs
                            obtain ⟨h5, -⟩ := ha
                            obtain rfl := Sum.inl.inj h5
                            simp only [subSel] at hs
                            split_ifs at hs; simp at hs
                          · simp at ha)
                   · simp at ha)
            obtain rfl := hk j dj hd2
            exact .inl ⟨dj, n, rfl⟩
          · simp [Code.withStubs, frag, wg1Code, Code.roleLoop, Code.loopGlue] at hd2
      · simp at hs1
    · simp at hs1

/-- **An index state follows the head's shuffle state** along a lane's trace. -/
theorem index_origin {d : Index.D} {n : Cls → Nat} :
    ∀ {k : Nat}, Frame.stateAt (thread P L) X g k = some (some (idxState P L g d n)) →
      ∃ k0 n0, k0 < k ∧ Frame.stateAt (thread P L) X g k0 = some (some (hshState P L g n0)) := by
  intro k
  induction k generalizing d n with
  | zero =>
    intro h
    rw [Frame.stateAt_zero] at h
    have h1 := congrArg Prod.fst (Option.some.inj (Option.some.inj h))
    exact (enter_top_ne_index (s := (startupCode P L g).init) h1).elim
  | succ k ih =>
    intro h
    cases hg : (X.tr g)[k]? with
    | none =>
      have hl : (X.tr g).length ≤ k := List.getElem?_eq_none_iff.mp hg
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hl] at h
      obtain ⟨k0, n0, hk, h0⟩ := ih h
      exact ⟨k0, n0, by omega, h0⟩
    | some f =>
      rw [Frame.stateAt_succ hg] at h
      cases hs : Frame.stateAt (thread P L) X g k with
      | none => simp [hs] at h
      | some o =>
        rw [hs] at h
        cases o with
        | none => simp [Code.toMachine] at h
        | some σ0 =>
          rcases next_into_index h rfl with ⟨d0, n0, rfl⟩ | ⟨n0, rfl⟩
          · obtain ⟨k0, n1, hk, h0⟩ := ih hs
            exact ⟨k0, n1, by omega, h0⟩
          · exact ⟨k, n0, by omega, hs⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
