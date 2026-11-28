-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIxN
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexOrigin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.ValStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.IndexVal
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StrictIndexEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The words an index lane keeps are its shuffles' receives

`ix_rv`: at every state of an index lane before undefined behaviour, the words `rv1` and `rv2`
the machine keeps (past the first and the second shuffle of the block) are the received words of
the lane's shuffles number `N - soff` and `N - 1` (counting from 0), `N` the shuffles the lane
has made. `RecvAt X g c v`: the lane's shuffle with `c` shuffles before it received `v`. -/

/-! # The words an index state keeps are the shuffles it received

A state of the index warp past its block's first shuffle (`soff d.site ≥ 1`) keeps the word that
shuffle received in `rv1`, and past the second (`soff = 2`) the second's in `rv2`. With `N` the
shuffles the lane has made, they are the receives number `N - soff` and `N - 1` (counting from
0): `RvInv R N d` for a relation `R` of a count and a received word. `rv_step`: a step of the
machine on an event keeps it, given that the event's received word, if it is a shuffle's, is
related to the count `N`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- **The receive invariant**: the words the state keeps are receives number `N - soff` and
`N - 1`. -/
def RvInv (R : Nat → Value → Prop) (N : Nat) (d : D) : Prop :=
  (1 ≤ soff d.site → R (N - soff d.site) d.c.rv1) ∧ (soff d.site = 2 → R (N - 1) d.c.rv2)

theorem rvInv_zero {R : Nat → Value → Prop} {N : Nat} {d : D} (h : soff d.site = 0) :
    RvInv R N d := ⟨fun h1 => by omega, fun h2 => by omega⟩

theorem soff_vac {s : IxSite} (h : Vac s) : soff s = 0 := by
  cases s <;> simp only [Vac] at h <;> rfl

theorem rvInv_of {R : Nat → Value → Prop} {N : Nat} {d d' : D} (hs : soff d'.site = soff d.site)
    (hc : d'.c = d.c) (h : RvInv R N d) : RvInv R N d' := by
  unfold RvInv at h ⊢
  rw [hs, hc]
  exact h

theorem shflNext_ev {e : Event} {f : Value → D} {a : D} (h : shflNext e f = some (some a)) :
    ∃ md av b c r ok, e.kind = .shfl md av b c r ok ∧ a = f r := by
  unfold shflNext at h
  split at h
  · rename_i md av b c r ok hk
    exact ⟨md, av, b, c, r, ok, hk, (Option.some.inj (Option.some.inj h)).symm⟩
  · cases h

/-- **A step keeps the receive invariant.** -/
theorem rv_step {R : Nat → Value → Prop} {N : Nat} {d a : D} {e : Event}
    (hI : RvInv R N d) (hev : Ev P L g d e)     (hs : succ P L g d e = some (some a))
    (hf : ∀ md av b c r ok, e.kind = .shfl md av b c r ok → R N r) :
    RvInv R (N + if Execution.isShfl e then 1 else 0) a := by
  obtain ⟨site, el, ac, c⟩ := d
  obtain ⟨hpc, hk⟩ := hev
  obtain ⟨pc, kd⟩ := e
  dsimp only at hk hs hI hf
  cases site with
  | exit => simp [succ] at hs
  | lenA | lenB =>
    simp only [succ] at hs
    obtain ⟨x, rfl⟩ := lenNext_some hs
    first
      | exact rvInv_zero (soff_of_incW (incW_ixAfterA P _))
      | exact rvInv_zero (soff_of_incW (incW_ixLens _))
  | pre | pf | xpre | xpf =>
    all_goals
      simp only [succ] at hs
      have e1 := fun c' => soff_of_incW (incW_afterPre P L g c')
      have e2 := fun c' => soff_of_incW (incW_afterXpre L g c')
      refine rvInv_zero ?_
      rcases pair_cases hs with ⟨h1, -⟩ | ⟨y0, y1, h⟩
      · simp [h1, soff]
      · simp [h, e1, e2]
  | wA | wB =>
    all_goals
      simp only [succ] at hs
      refine rvInv_zero ?_
      rcases poll_cases hs with rfl | rfl <;> rfl
  | sA1 | sA2 | sB1 | sB2 =>
    all_goals
      simp only [succ] at hs
      obtain ⟨md, av, b, c', r, ok, hk', rfl⟩ := shflNext_ev hs
      dsimp only at hk'
      subst hk'
      have hr := hf md av b c' r ok rfl
      simp only [Execution.isShfl, ite_true]
      first
        | exact ⟨fun _ => by simpa [soff] using hr, fun h => by simp [soff] at h⟩
        | exact ⟨fun _ => by simpa [soff] using hI.1 (by simp [soff]),
            fun _ => by simpa [soff] using hr⟩
  | bA | bB =>
    all_goals
      simp only [succ, Option.some.injEq] at hs
      subst hs
      rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩ <;>
        simp only [Execution.isShfl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;>
        exact rvInv_of (by simp [soff]) rfl hI
  | stA =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    have hn : (if Execution.isShfl ⟨pc, kd⟩ then 1 else 0) = 0 := by
      rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩ <;> simp [Execution.isShfl]
    rw [hn, Nat.add_zero]
    rcases stNext_cases (⟨.stA, el, ac, c⟩ : D) (ofC (afterSt L g .bA .arrA, c)) with
      ⟨h1, h2⟩ | h
    · exact rvInv_of (d := ⟨.stA, el, ac, c⟩) (by rw [h1]) h2 hI
    · rw [h]
      rcases afterSt_cases (L := L) (g := g) .bA .arrA with e | e <;> rw [e] <;>
        exact rvInv_of (d := ⟨.stA, el, ac, c⟩) (by simp [soff]) rfl hI
  | stB =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    have hn : (if Execution.isShfl ⟨pc, kd⟩ then 1 else 0) = 0 := by
      rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩ <;> simp [Execution.isShfl]
    rw [hn, Nat.add_zero]
    rcases stNext_cases (⟨.stB, el, ac, c⟩ : D) (ofC (afterSt L g .bB .arrB, c)) with
      ⟨h1, h2⟩ | h
    · exact rvInv_of (d := ⟨.stB, el, ac, c⟩) (by rw [h1]) h2 hI
    · rw [h]
      rcases afterSt_cases (L := L) (g := g) .bB .arrB with e | e <;> rw [e] <;>
        exact rvInv_of (d := ⟨.stB, el, ac, c⟩) (by simp [soff]) rfl hI
  | bar =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact rvInv_zero rfl
  | arrA =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact rvInv_zero (soff_of_incW (incW_mainEnd c))
  | arrB =>
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact rvInv_zero (soff_of_incW (incW_xEnd c))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow Index

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The receive of a shuffle**: the lane's shuffle with `c` shuffles before it received `v`. -/
def RecvAt (X : Execution) (g c : Nat) (v : Value) : Prop :=
  ∃ j pc md a b cc ok, X.get (g, j) = some ⟨pc, .shfl md a b cc v ok⟩ ∧
    ((X.tr g).take j).countP Execution.isShfl = c

/-- **The words an index lane's state keeps are its receives.** -/
theorem ix_rv (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) :
    ∀ {k : Nat} {d : Index.D} {n : Cls → Nat}, NoUbBefore X g k →
      Frame.stateAt (thread P L) X g k = some (some (idxState P L g d n)) →
      RvInv (RecvAt X g) (((X.tr g).take k).countP Execution.isShfl) d := by
  intro k
  induction k with
  | zero =>
    intro d n _ h
    rw [Frame.stateAt_zero] at h
    have h1 := congrArg Prod.fst (Option.some.inj (Option.some.inj h))
    exact (enter_top_ne_index (s := (startupCode P L g).init) h1).elim
  | succ k ih =>
    intro d n hub h
    cases hg : (X.tr g)[k]? with
    | none =>
      have hl : (X.tr g).length ≤ k := List.getElem?_eq_none_iff.mp hg
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hl] at h
      have := ih (hub.mono (by omega)) h
      rw [List.take_of_length_le hl] at this
      rw [List.take_of_length_le (by omega)]
      exact this
    | some f =>
      rw [Frame.stateAt_succ hg] at h
      have hget : X.get (g, k) = some f := hg
      have hfub := hub.ne (by omega) hget
      cases hs : Frame.stateAt (thread P L) X g k with
      | none => simp [hs] at h
      | some o =>
        rw [hs] at h
        cases o with
        | none => simp [Code.toMachine] at h
        | some σ0 =>
          rcases next_into_index h rfl with ⟨d0, n0, rfl⟩ | ⟨n0, rfl⟩
          · obtain ⟨d3, n', hsucc, heq⟩ := thread_next_index h
            obtain ⟨rfl, -⟩ : d = d3 ∧ n = n' := by
              simp only [idxState, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq,
                true_and] at heq
              exact ⟨heq.1, heq.2⟩
            have hI := ih (hub.mono (by omega)) hs
            obtain ⟨hev, -, -⟩ := ix_evAt hp hX hFw hget hfub hs
            have hcnt : ((X.tr g).take (k + 1)).countP Execution.isShfl =
                ((X.tr g).take k).countP Execution.isShfl +
                  if Execution.isShfl f then 1 else 0 := by
              rw [List.take_add_one, hg, List.countP_append]
              simp
            rw [hcnt]
            refine rv_step hI hev hsucc fun md av b c r ok hk => ?_
            obtain ⟨pc, kd⟩ := f
            simp only at hk
            subst hk
            exact ⟨k, pc, md, av, b, c, ok, hget, rfl⟩
          · obtain rfl := thread_next_hsh_idx h rfl
            exact rvInv_zero (soff_vac (vac_ixFirst P L g))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
