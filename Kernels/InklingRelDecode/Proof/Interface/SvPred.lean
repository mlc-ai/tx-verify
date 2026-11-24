-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvBias

@[expose] public section

/-!
# The predecessor of a softmax-region state along a thread's trace

A state `.d (.sm d)` of a thread before its `k`-th event is the region's first state (the
prologue's last event) or the successor `Sm.next` returns at the state before the previous event
(`pred_sm`); the region's second shuffle of the stage is only reached from the first
(`prev_shfl6`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000
open Classical

theorem afterSetup_site {L : Launch} {g : Nat} {d d' : D}
    (h : Sm.afterSetup L g d = some (some d')) : d'.site = .nxt 0 ∨ d'.site = .waitS := by
  unfold Sm.afterSetup at h
  split at h
  · cases h
  · split at h <;> (simp only [Option.some.injEq] at h; subst h; simp)

theorem toBar20_site {d d' : D} (h : Sm.toBar20 d = some (some d')) : d'.site = .bar20 := by
  unfold Sm.toBar20 at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · cases h

/-- **Only the first shuffle of the stage leads to the second.** -/
theorem prev_shfl6 {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : Sm.next L g d e = some (some d')) (h6 : d'.site = .shfl6) : d.site = .shfl5 := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterSum] at h6)
    | (have := afterSetup_site hn; rcases this with h | h <;> simp_all)
    | (have := toBar20_site hn; simp_all)

/-- The softmax region's state after a component's step is the region's first state or the
region's own step. -/
theorem dcomp_next_sm {L : Launch} {g : Nat} {Q : Params} {s0 : DComp.St} {d : D} {e : Event}
    (h : DComp.next L g Q s0 e = some (some (DComp.St.sm d))) :
    (∃ dt, d = SmEntry.d0 (SmEntry.entOf Q L g dt)) ∨
      ∃ d0, s0 = .sm d0 ∧ Sm.next L g d0 e = some (some d) := by
  cases s0 with
  | dstart dd =>
    change DComp.dstartNext L g Q dd e = _ at h
    unfold DComp.dstartNext at h
    obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
    split at ha <;> cases ha
  | pro dp =>
    change DComp.proNext L g Q dp e = _ at h
    unfold DComp.proNext at h
    split at h
    · split at h
      · simp only [Option.some.injEq, DComp.St.sm.injEq] at h
        exact Or.inl ⟨dp.dt, h.symm⟩
      · cases h
    · obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
      cases ha
  | sm d0 =>
    change DComp.smNext L g d0 e = _ at h
    unfold DComp.smNext at h
    split at h
    · unfold DComp.exitNext at h
      split at h
      · cases h
      · cases h
    · obtain ⟨a, ha, hs⟩ := map_map_eq_some_some h
      simp only [DComp.St.sm.injEq] at hs
      subst hs
      exact Or.inr ⟨d0, rfl, ha⟩
  | epi de =>
    change (Epi.next de e).map (Option.map DComp.St.epi) = _ at h
    obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
    cases ha

variable {Q : Params} {L : Launch} {X : Execution} {g : Nat}

/-- **The predecessor of a softmax-region state.** The state before the `k`-th event (with `k` at
most the trace's length) is the region's first state (after the prologue's last event) or the
successor of the region's state before the previous event. -/
theorem pred_sm {k : Nat} {d : D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    (∃ dt, d = SmEntry.d0 (SmEntry.entOf Q L g dt)) ∨
      ∃ (k0 : Nat) (d0 : D) (e : Event), k = k0 + 1 ∧ (X.tr g)[k0]? = some e ∧
        St Q L X g k0 = some (some (.d (.sm d0))) ∧ Sm.next L g d0 e = some (some d) := by
  cases k with
  | zero =>
    exfalso
    have h0 := hσ
    rw [St, Frame.stateAt_zero] at h0
    have h1 := Option.some.inj (Option.some.inj h0)
    change (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
      else TSt.w (WComp.code L g Q).init) = TSt.d (DComp.St.sm d) at h1
    split at h1
    · simp at h1
    · cases h1
  | succ k0 =>
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k0]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs' := hσ
    rw [St, Frame.stateAt_succ he] at hs'
    cases hk0 : St Q L X g k0 with
    | none => simp [St] at hk0 hs'; simp [hk0] at hs'
    | some σ0 =>
      cases σ0 with
      | none =>
        have : Frame.stateAt (code L Q) X g k0 = some none := hk0
        rw [this] at hs'
        simp [Code.toMachine] at hs'
      | some s0 =>
        have : Frame.stateAt (code L Q) X g k0 = some (some s0) := hk0
        rw [this] at hs'
        have hn : (threadCode L g Q).next s0 e = some (some (.d (.sm d))) := hs'
        cases s0 with
        | d s =>
          rw [next_d] at hn
          obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
          cases h
          rcases dcomp_next_sm ha with h | ⟨d0, hd0, hn0⟩
          · exact Or.inl h
          · subst hd0
            exact Or.inr ⟨k0, d0, e, rfl, he, hk0, hn0⟩
        | w s =>
          rw [next_w] at hn
          obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
          cases h

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
