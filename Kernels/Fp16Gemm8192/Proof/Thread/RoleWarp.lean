-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueIndex
public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # Roles follow the warp index

The prologue routes a thread by the warp index its shuffle returned, which in an execution
is the thread's own warp index: warp 11 becomes the loader, warps 8 and 9 the MMA warps, warp
10 the scheduler. A thread keeps its role to the end. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-- The prologue enters a role by its own warp index. -/
theorem Prologue.next_role {L : Launch} {g : Nat} {p : Prologue.D} {e : Event} {r : Prologue.Role}
    (hn : Prologue.next L g p e = some (some (.inr r))) : roleWarp p.w r := by
  obtain ⟨s, w⟩ := p
  unfold Prologue.next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Sum.inr.injEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all [roleWarp, Prologue.mmaStart]
  all_goals omega

/-- An MMA step keeps the thread's warp. -/
theorem Mma.next_w {L : Launch} {g : Nat} {m m' : Mma.D} {e : Event}
    (hn : Mma.next L g m e = some (some m')) : m'.w = m.w := by
  unfold Mma.next at hn
  repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at hn; obtain ⟨_, -, rfl⟩ :=
    hn))
  all_goals (try subst hn)
  all_goals (try rfl)
  all_goals (unfold Mma.endOfTrip; split_ifs <;> rfl)

/-- A role's successor has the same role. -/
theorem role_next {L : Launch} {g : Nat} {r r' : Prologue.Role} {e : Event}
    (hn : (code L g).toMachine.next (some (.inr r)) e = some (some (.inr r'))) (w : Nat) :
    roleWarp w r → roleWarp w r' := by
  cases r with
  | loader l =>
    change (Loader.next L g l e).map (Option.map (fun l' =>
      (Sum.inr (Prologue.Role.loader l') : ThreadD))) =
      some (some (.inr r')) at hn
    cases h : Loader.next L g l e with
    | none => rw [h] at hn; cases hn
    | some o => rw [h] at hn; cases o <;> simp at hn; subst hn; exact id
  | mma m =>
    change (Mma.next L g m e).map (Option.map (fun m' =>
      (Sum.inr (Prologue.Role.mma m') : ThreadD))) =
      some (some (.inr r')) at hn
    cases h : Mma.next L g m e with
    | none => rw [h] at hn; cases hn
    | some o =>
      rw [h] at hn
      cases o <;> simp at hn
      subst hn
      rename_i m'
      simp only [roleWarp, Mma.next_w h]
      exact id
  | sched s =>
    change (Scheduler.next L g s e).map (Option.map (fun s' =>
      (Sum.inr (Prologue.Role.sched s') : ThreadD))) =
      some (some (.inr r')) at hn
    cases h : Scheduler.next L g s e with
    | none => rw [h] at hn; cases hn
    | some o => rw [h] at hn; cases o <;> simp at hn; subst hn; exact id
  | cons c =>
    change (Consumer.next L g c e).map (Option.map (fun c' =>
      (Sum.inr (Prologue.Role.cons c') : ThreadD))) =
      some (some (.inr r')) at hn
    cases h : Consumer.next L g c e with
    | none => rw [h] at hn; cases hn
    | some o => rw [h] at hn; cases o <;> simp at hn; subst hn; exact id

/-- In an execution, a thread in a role state runs on that role's warp. -/
theorem role_warp {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads) :
    ∀ k, k ≤ (X.tr g).length → ∀ r, Frame.stateAt (code L) X g k = some (some (.inr r)) →
      roleWarp (Prologue.warpOf L g) r := by
  intro k
  induction k with
  | zero =>
    intro _ r h
    have h0 : Frame.stateAt (code L) X g 0 = some (some (.inl ⟨.shfl, 0⟩)) := rfl
    rw [h0] at h
    cases h
  | succ k ih =>
    intro hk r h
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at h
    cases hs : Frame.stateAt (code L) X g k with
    | none => rw [hs] at h; cases h
    | some σ =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      cases σ with
      | none => cases h
      | some τ =>
        cases τ with
        | inl p =>
          have hn : Prologue.next L g p e = some (some (.inr r)) := h
          have hr := Prologue.next_role hn
          rcases Nat.eq_zero_or_pos k with rfl | hpos
          · have h0 : Frame.stateAt (code L) X g 0 = some (some (.inl ⟨.shfl, 0⟩)) := rfl
            rw [h0] at hs
            cases hs
            simp only [Prologue.next] at hn
            split at hn <;> (try split_ifs at hn) <;> simp_all
          · rw [(stateAt_prologue hpre hX hg (by omega) hs).2 hpos] at hr
            exact hr
        | inr r0 => exact role_next h _ (ih (by omega) r0 hs)

end
end PTX.Kernels.Fp16Gemm8192.Proof
