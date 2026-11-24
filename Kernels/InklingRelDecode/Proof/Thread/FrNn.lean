-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Lk3Num
public import Kernels.InklingRelDecode.Proof.Thread.Lk3Min
public import Kernels.InklingRelDecode.Proof.Thread.SmMax

@[expose] public section

/-!
# The running maximum and sum of a softmax state are numbers that the exit can use

The bridge to the epilogue (`Br.In.NoFault`, through `DComp.exitNext`) takes the running sum
`l` and maximum `m` of the state at the loop's exit. It does not fault where `l` is a number at
least `0` (positive or zero) and `m` reads as an extended real that is not `+inf`. `NnInv` is the
invariant that gives both at every state: the sum starts at `0` and is kept by the update
`l * alpha + row sum` (`alpha` is `1` or `2 ^ alpha_log2`, the row sum is the sum of the
thread's probabilities and the partner's, each `2 ^ x`), the maximum starts at `-inf` and is the
maximum of numbers of the stage (`D.mnE`), whose words are never `+inf` (`eOf`).

One step needs a fact about another lane: the received sum of probabilities at `shfl6` is
non-negative (`NnInv.step`'s premise `hy`). It is the partner's sum of probabilities, which is
non-negative because every probability is (`PfNn`, a one-lane invariant).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lk

noncomputable section
set_option maxRecDepth 100000

/-! ### Numbers of the stage -/

theorem eOf_ne_top (v : Value) : eOf v ≠ ⊤ := by
  cases v <;> simp [eOf, EReal.coe_ne_top]

theorem cmaxW_ne_top (w : Nat → Value) (m : Nat) : cmaxW w m ≠ ⊤ := by
  unfold cmaxW
  refine ne_of_lt ((Finset.sup_lt_iff bot_lt_top).2 fun k _ => ?_)
  exact lt_top_iff_ne_top.2 (eOf_ne_top _)

theorem mnE_ne_top (d : D) (rE : EReal) (h : rE ≠ ⊤) : d.mnE rE ≠ ⊤ := by
  unfold D.mnE D.mE D.ownE
  exact ne_of_lt (max_lt (max_lt (lt_top_iff_ne_top.2 (eOf_ne_top _))
    (lt_top_iff_ne_top.2 (cmaxW_ne_top _ _))) (lt_top_iff_ne_top.2 h))

theorem pow2_nonneg (a : EReal) : 0 ≤ Softmax.pow2 a := by
  unfold Softmax.pow2
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (by norm_num) _

theorem pOfV_nonneg (sl mu : ℝ) (v : Value) : 0 ≤ pOfV sl mu v := by
  unfold pOfV
  cases v <;> first | exact le_rfl | exact Real.rpow_nonneg (by norm_num) _

theorem sumP_nonneg {d : D} (h : ∀ k, 0 ≤ d.pf k) : 0 ≤ d.sumP := by
  unfold D.sumP
  apply List.sum_nonneg
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact h k

theorem valFloat_b32_one' : valFloat .f32 (b32 1065353216) = .ok 1 := by
  have := valFloat_b32 (b := 1065353216) (q := 1) (by decide)
    (by decide +kernel)
  simpa using this

theorem readsAs_infB : ReadsAs infB ⊥ := by
  rw [← erealValue_bot']
  exact readEReal_erealValue bot_ne_top

/-! ### One lane: the probabilities are non-negative -/

/-- **The probabilities of a state are non-negative.** -/
def PfNn (d : D) : Prop := ∀ k, 0 ≤ d.pf k

theorem pfNn_afterSetup {L : Launch} {g : Nat} {d d' : D} (h : PfNn d)
    (hn : Sm.afterSetup L g d = some (some d')) : PfNn d' := by
  unfold Sm.afterSetup at hn
  split at hn
  · cases hn
  · split at hn <;> (simp only [Option.some.injEq] at hn; subst hn; exact h)

theorem pfNn_toBar20 {d d' : D} (h : PfNn d) (hn : toBar20 d = some (some d')) : PfNn d' := by
  unfold toBar20 at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst hn
    exact h
  · cases hn

theorem pfNn_next {L : Launch} {g : Nat} {d d' : D} {e : Event} (h : PfNn d)
    (hn : Sm.next L g d e = some (some d')) : PfNn d' := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; exact h)
    | (simp only [Option.some.injEq] at hn; subst hn; intro k; exact pOfV_nonneg _ _ _)
    | (refine pfNn_afterSetup ?_ hn; exact h)
    | exact pfNn_toBar20 h hn
    | (exact pfNn_toBar20 (d := D.afterSum _ _) h hn)

/-! ### The running maximum and sum -/

/-- **The numbers the exit uses.** -/
structure NnInv (d : D) : Prop where
  m : ∃ x : EReal, x ≠ ⊤ ∧ ReadsAs d.m x
  mn : ∃ x : EReal, x ≠ ⊤ ∧ ReadsAs d.stg.mn x
  l : ∃ x : ℝ, 0 ≤ x ∧ valFloat .f32 d.l = .ok x
  lsh : d.l = b32 0 ∨ ∃ x : ℝ, d.l = .float .f32 x
  al : ∃ x : ℝ, 0 ≤ x ∧ valFloat .f32 d.stg.al = .ok x
  rs : ∃ x : ℝ, 0 ≤ x ∧ valFloat .f32 d.stg.rs = .ok x

theorem NnInv.of_eq {d d' : D} (h : NnInv d) (hm : d'.m = d.m) (hl : d'.l = d.l)
    (ha : d'.stg.al = d.stg.al) (hr : d'.stg.rs = d.stg.rs) (hn : d'.stg.mn = d.stg.mn) :
    NnInv d' :=
  ⟨hm ▸ h.m, hn ▸ h.mn, hl ▸ h.l, hl ▸ h.lsh, ha ▸ h.al, hr ▸ h.rs⟩

theorem nnInv_init (e : Ent) : NnInv (SmEntry.d0 e) where
  m := ⟨⊥, bot_ne_top, readsAs_infB⟩
  mn := ⟨⊥, bot_ne_top, readsAs_infB⟩
  l := ⟨0, le_rfl, valFloat_z0⟩
  lsh := Or.inl rfl
  al := ⟨0, le_rfl, valFloat_z0⟩
  rs := ⟨0, le_rfl, valFloat_z0⟩

theorem alV_nn (d : D) (rE : EReal) : ∃ x : ℝ, 0 ≤ x ∧ valFloat .f32 (d.alV rE) = .ok x := by
  unfold D.alV
  split
  · exact ⟨1, zero_le_one, valFloat_b32_one'⟩
  · exact ⟨_, pow2_nonneg _, valFloat_float _⟩

theorem nnInv_toBar20 {d d' : D} (h : NnInv d) (hn : toBar20 d = some (some d')) : NnInv d' := by
  obtain ⟨x, hx0, hx⟩ := h.l
  obtain ⟨y, hy0, hy⟩ := h.al
  obtain ⟨z, hz0, hz⟩ := h.rs
  have hl : d.lOut = .ok (.float .f32 (x * y + z)) := floatE_fma_fin hx hy hz
  unfold toBar20 at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst hn
    refine ⟨?_, h.mn, ⟨x * y + z, by positivity, ?_⟩, Or.inr ⟨x * y + z, ?_⟩, h.al, h.rs⟩
    · show ∃ x : EReal, x ≠ ⊤ ∧ ReadsAs d.mNew x
      unfold D.mNew
      split
      · exact h.m
      · exact h.mn
    · show valFloat .f32 (okVal (b32 0) d.lOut) = _
      rw [okVal_of_ok hl]
      exact valFloat_float _
    · show okVal (b32 0) d.lOut = _
      rw [okVal_of_ok hl]
  · cases hn

theorem nnInv_afterSetup {L : Launch} {g : Nat} {d d' : D} (h : NnInv d)
    (hn : Sm.afterSetup L g d = some (some d')) : NnInv d' := by
  unfold Sm.afterSetup at hn
  split at hn
  · cases hn
  · split at hn <;>
      (simp only [Option.some.injEq] at hn; subst hn; exact h.of_eq rfl rfl rfl rfl rfl)

/-- **The exchange of the sum of probabilities** keeps the numbers, if the received word is a
non-negative `.f32` number. -/
theorem nnInv_shfl6 {L : Launch} {g : Nat} {d d' : D} {e : Event} (h : NnInv d) (hpf : PfNn d)
    (hs : d.site = .shfl6) (hsw : d.stg.sw = .float .f32 d.sumP)
    (hy : ∀ {md : ShflMode} {a : Value} {b c : Nat} {recv : Value} {ok : Bool},
      e.kind = .shfl md a b c recv ok → ∃ y : ℝ, recv = .float .f32 y ∧ 0 ≤ y)
    (hn : Sm.next L g d e = some (some d')) : NnInv d' := by
  simp only [Sm.next, hs] at hn
  split at hn
  · rename_i md a b c recv ok he
    obtain ⟨y, rfl, hy0⟩ := hy he
    have hv : d.rsOut (.float .f32 y) = .ok (.float .f32 (d.sumP + y)) := by
      unfold D.rsOut
      rw [hsw]
      exact floatE_add_fin (valFloat_float _) (valFloat_float _)
    rw [hv] at hn
    have h' : NnInv (d.afterSum (.float .f32 (d.sumP + y))) :=
      ⟨h.m, h.mn, h.l, h.lsh, h.al,
        ⟨d.sumP + y, add_nonneg (sumP_nonneg hpf) hy0, valFloat_float _⟩⟩
    simp only at hn
    split at hn
    · exact nnInv_toBar20 h' hn
    · simp only [Option.some.injEq] at hn
      subst hn
      exact h'
  · simp at hn

/-- **Every step of the softmax region keeps the numbers**, given that the word a lane received
at the exchange of the sums of probabilities is a non-negative `.f32` number. -/
theorem nnInv_next {L : Launch} {g : Nat} {d d' : D} {e : Event} (h : NnInv d) (hpf : PfNn d)
    (hsw : d.site = .shfl6 → d.stg.sw = .float .f32 d.sumP)
    (hy : ∀ {md : ShflMode} {a : Value} {b c : Nat} {recv : Value} {ok : Bool},
      d.site = .shfl6 → e.kind = .shfl md a b c recv ok → ∃ y : ℝ, recv = .float .f32 y ∧ 0 ≤ y)
    (hn : Sm.next L g d e = some (some d')) (hre' : d'.stg.re = true) : NnInv d' := by
  by_cases hs : d.site = .shfl6
  · exact nnInv_shfl6 h hpf hs (hsw hs) (fun he => hy hs he) hn
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; exact h.of_eq rfl rfl rfl rfl rfl)
    | (refine nnInv_afterSetup ?_ hn; exact h.of_eq rfl rfl rfl rfl rfl)
    | exact nnInv_toBar20 h hn
    | (simp only [Option.some.injEq] at hn; subst hn
       exact ⟨h.m, ⟨_, mnE_ne_top _ _ (eOf_ne_top _),
         ReadsAs.of_erealValue (mnE_ne_top _ _ (eOf_ne_top _))⟩, h.l, h.lsh, alV_nn _ _, h.rs⟩)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterMaxT] at hre')
    | exact absurd (by assumption) hs

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
