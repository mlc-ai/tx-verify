-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvPred
public import Kernels.InklingRelDecode.Proof.Thread.SwShape

@[expose] public section

/-!
# The rescale store's state: the load it follows and the words of its event

A softmax state at the rescale store (`stO`) is reached from the state at the rescale load (`ldO`)
by the load's event, the wait for the load (`waitLdO`) and the named barrier (`bar24`): `stO_pred`.
The state keeps the iteration and the entry numbers of the load's state, and its words of `O`
(`stg.ow`) are the words the load returned. `ostore_event`: the store's event is the 64-word store
to `Sm.oAddr` whose word `k` is the float of `alr · bfR (ow k)`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000
open Classical

/-- **Only `bar24` leads to the rescale store**, with the state unchanged. -/
theorem prev_stO {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : Sm.next L g d e = some (some d')) (h : d'.site = .stO) :
    d.site = .bar24 ∧ d' = { d with site := .stO } := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterSum] at h)
    | (have := afterSetup_site hn; rcases this with h' | h' <;> simp_all)
    | (have := toBar20_site hn; simp_all)

/-- **Only `waitLdO` leads to `bar24`**, with the state unchanged. -/
theorem prev_bar24 {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : Sm.next L g d e = some (some d')) (h : d'.site = .bar24) :
    d.site = .waitLdO ∧ d' = { d with site := .bar24 } := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterSum] at h)
    | (have := afterSetup_site hn; rcases this with h' | h' <;> simp_all)
    | (have := toBar20_site hn; simp_all)

/-- **Only `ldO` leads to `waitLdO`**, by the load's event, which puts its words into `stg.ow`. -/
theorem prev_waitLdO {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hn : Sm.next L g d e = some (some d')) (h : d'.site = .waitLdO) :
    d.site = .ldO ∧ ∃ (a : Nat) (vals : List Value) (sh : TcShape),
      e.kind = .tc (.ld a vals sh) ∧
      d' = { d with site := .waitLdO, stg := { d.stg with ow := owOf vals } } := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterSum] at h)
    | (have := afterSetup_site hn; rcases this with h' | h' <;> simp_all)
    | (have := toBar20_site hn; simp_all)

variable {Q : Params} {L : Launch} {X : Execution} {g : Nat}

/-- **The state at the rescale store follows the load.** A state at `stO` (before the `k`-th event,
`k` at most the trace's length) is three events after the state at the rescale load `ldO` (the
load's event, the wait, the barrier), and holds the words the load returned. -/
theorem stO_pred {k : Nat} {d : D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .stO) :
    ∃ (k0 : Nat) (d0 : D) (a : Nat) (vals : List Value) (sh : TcShape), k = k0 + 3 ∧
      St Q L X g k0 = some (some (.d (.sm d0))) ∧ d0.site = .ldO ∧
      (∃ pc, X.get (g, k0) = some ⟨pc, .tc (.ld a vals sh)⟩) ∧
      d = { d0 with site := .stO, stg := { d0.stg with ow := owOf vals } } := by
  rcases pred_sm hk hσ with ⟨dt, h⟩ | ⟨k1, d1, e1, hk1, he1, hσ1, hn1⟩
  · subst h
    simp [SmEntry.d0] at hs
  obtain ⟨hs1, hd1⟩ := prev_stO hn1 hs
  rcases pred_sm (by omega) hσ1 with ⟨dt, h⟩ | ⟨k2, d2, e2, hk2, he2, hσ2, hn2⟩
  · subst h
    simp [SmEntry.d0] at hs1
  obtain ⟨hs2, hd2⟩ := prev_bar24 hn2 hs1
  rcases pred_sm (by omega) hσ2 with ⟨dt, h⟩ | ⟨k3, d3, e3, hk3, he3, hσ3, hn3⟩
  · subst h
    simp [SmEntry.d0] at hs2
  obtain ⟨hs3, a, vals, sh, hke, hd3⟩ := prev_waitLdO hn3 hs2
  obtain ⟨pc3, kd3⟩ := e3
  simp only at hke
  subst hke
  refine ⟨k3, d3, a, vals, sh, by omega, hσ3, hs3, ⟨pc3, he3⟩, ?_⟩
  rw [hd1, hd2, hd3]

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
