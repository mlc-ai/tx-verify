-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvPred

@[expose] public section

/-!
# The predecessor of a default-partition state, and of a softmax state with its class

* `pred_d`: a state `.d s` of a thread before its `k`-th event (`k` at most the trace's length)
  is the machine's first state or the successor `DComp.next` returns at the state before the
  previous event, which is a default-partition state.
* `dnext_pre`, `dnext_sm`: the states a default-partition state can come from: the common start
  and the prologue come only from the common start and the prologue; the softmax region from the
  prologue (its first state) or from itself.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {X : Execution} {g : Nat}

/-- The states before the softmax region: the common start and the prologue. -/
def PreSt : DComp.St → Prop
  | .dstart _ => True
  | .pro _ => True
  | _ => False

/-- **The default-partition state before the previous event.** -/
theorem pred_d {k : Nat} {s : DComp.St} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d s))) :
    (k = 0 ∧ s = (DComp.code L g Q).init) ∨
      ∃ (k0 : Nat) (e : Event) (s0 : DComp.St), k = k0 + 1 ∧ (X.tr g)[k0]? = some e ∧
        St Q L X g k0 = some (some (.d s0)) ∧ DComp.next L g Q s0 e = some (some s) := by
  cases k with
  | zero =>
    left
    refine ⟨rfl, ?_⟩
    have h0 := hσ
    rw [St, Frame.stateAt_zero] at h0
    have h1 := Option.some.inj (Option.some.inj h0)
    change (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
      else TSt.w (WComp.code L g Q).init) = TSt.d s at h1
    split at h1
    · exact (TSt.d.inj h1).symm
    · cases h1
  | succ k0 =>
    right
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k0]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨k0, e, ?_⟩
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
        have hn : (threadCode L g Q).next s0 e = some (some (.d s)) := hs'
        cases s0 with
        | d s1 =>
          rw [next_d] at hn
          obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
          cases h
          exact ⟨s1, rfl, he, rfl, ha⟩
        | w s1 =>
          rw [next_w] at hn
          obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
          cases h

/-- **The states a pre-softmax state comes from.** -/
theorem dnext_pre {s0 s : DComp.St} {e : Event}
    (h : DComp.next L g Q s0 e = some (some s)) (hs : PreSt s) : PreSt s0 := by
  cases s0 with
  | dstart d => trivial
  | pro d => trivial
  | sm d0 =>
    change DComp.smNext L g d0 e = _ at h
    unfold DComp.smNext at h
    split at h
    · unfold DComp.exitNext at h
      split at h
      · cases h; exact absurd hs (by simp [PreSt])
      · cases h
    · obtain ⟨a, -, hs'⟩ := map_map_eq_some_some h
      cases hs'; exact absurd hs (by simp [PreSt])
  | epi de =>
    change (Epi.next de e).map (Option.map DComp.St.epi) = _ at h
    obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
    cases ha; exact absurd hs (by simp [PreSt])

/-- **The states a softmax state comes from**: the prologue (the region's first state) or the
region itself. -/
theorem dnext_sm {s0 : DComp.St} {d : D} {e : Event}
    (h : DComp.next L g Q s0 e = some (some (DComp.St.sm d))) :
    (∃ dp, s0 = .pro dp ∧ d = SmEntry.d0 (SmEntry.entOf Q L g dp.dt)) ∨
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
        exact Or.inl ⟨dp, rfl, h.symm⟩
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

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
