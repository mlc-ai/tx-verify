-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk3Exch
public import Kernels.InklingRelDecode.Proof.Thread.Lk5PeerStep
public import Kernels.InklingRelDecode.Proof.Result.SwStore

@[expose] public section

/-!
# The two lanes of a row carry the same running maximum (`Sm.Peer`)

The lane `g` and the lane `x` with `x % 256 = (g % 256) ^ 16` of the same warp hold the two halves
of one tile row. The induction on the iteration that gives them the same shared numbers `Sm.pf`
is `pair_iter` (`Lk5WPair.lean`); here is its start:

* `pred_sm_pro`, `entry_pf`: the region's first state (`setMaxReg`) follows the prologue's last
  state; its entry numbers are a function of the CTA and the Tensor Memory base word, which is 0
  (`Rs.SmBaseZero`), so the first states of the two lanes have the same shared numbers;
* `partner_src`, `partner_symm`: the lane `^ 16` is the source lane of the exchange, and the
  relation is symmetric.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The region's first state -/

/-- The successor of a component's state that is a softmax state: the region's first state after a
prologue state, or a step of the region. -/
theorem dcomp_next_sm_pro {g : Nat} {s0 : DComp.St} {d : Sm.D} {e : Event}
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

/-- **The predecessor of a softmax state**, keeping the prologue state before the first one. -/
theorem pred_sm_pro {g k : Nat} {d : Sm.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    (∃ k0 dp, k = k0 + 1 ∧ St Q L X g k0 = some (some (.d (.pro dp))) ∧
      d = SmEntry.d0 (SmEntry.entOf Q L g dp.dt)) ∨
    ∃ (k0 : Nat) (d0 : Sm.D) (e : Event), k = k0 + 1 ∧ (X.tr g)[k0]? = some e ∧
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
    by_cases hk' : k0 < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k0]? = some e := ⟨_, List.getElem?_eq_getElem hk'⟩
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
            rcases dcomp_next_sm_pro ha with ⟨dp, rfl, hd⟩ | ⟨d0, hd0, hn0⟩
            · exact Or.inl ⟨k0, dp, rfl, hk0, hd⟩
            · subst hd0
              exact Or.inr ⟨k0, d0, e, rfl, he, hk0, hn0⟩
          | w s =>
            rw [next_w] at hn
            obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
            cases h
    · omega

/-- **The first softmax state of a thread**: the entry numbers of the CTA with the base word 0. -/
theorem entry_of (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) {g k : Nat} {d : Sm.D}
    (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .setMaxReg) :
    ∃ dt : ProA.Dat, dt.pro = DStart.inh L g Q 0 ∧ d = SmEntry.d0 (SmEntry.entOf Q L g dt) := by
  rcases pred_sm_pro hk hσ with ⟨k0, dp, -, hσ0, hd⟩ | ⟨k0, d0, e, -, -, -, hn⟩
  · obtain ⟨-, tm, -, hpro⟩ := hf.reach hg hσ0
    have htm : d.e.tm = 0 := hz hg hσ
    have htm' : d.e.tm = tm := by rw [hd]; show dp.dt.pro.tm = tm; rw [hpro]; rfl
    refine ⟨dp.dt, ?_, hd⟩
    rw [hpro, ← htm', htm]
  · exact absurd hs (next_ne_setMaxReg hn)

/-- **The first softmax states of two threads of a CTA have the same shared numbers.** -/
theorem entry_pf (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) {g x k j : Nat}
    {d d' : Sm.D} (hg : g < L.threads) (hx : x < L.threads) (hc : g / L.block = x / L.block)
    (hk : k ≤ (X.tr g).length) (hj : j ≤ (X.tr x).length)
    (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hσ' : St Q L X x j = some (some (.d (.sm d')))) (hs : d.site = .setMaxReg)
    (hs' : d'.site = .setMaxReg) : pf d = pf d' := by
  obtain ⟨dt, hp, rfl⟩ := entry_of hf hz hg hk hσ hs
  obtain ⟨dt', hp', rfl⟩ := entry_of hf hz hx hj hσ' hs'
  have hcta : ∀ c, ProA.cta L g c = ProA.cta L x c := by
    intro c
    unfold ProA.cta
    rw [hc]
  have he : SmEntry.entOf Q L g dt = SmEntry.entOf Q L x dt' := by
    simp only [SmEntry.entOf, hp, hp', DStart.inh, hcta]
  rw [he]

/-! ### Back to the previous synchronizing softmax state -/

/-! ### The exchange of the row maximum is symmetric -/

theorem pfU_congr {d d' : Sm.D} (h : pf d = pf d') : pfU d = pfU d' := by
  unfold pf at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold pfU D.mNew
  rw [h1, h2, h3, h4]

/-- The partner of the partner. -/
theorem partner_src (hb : L.block = 256) {g x : Nat} (hw : SameWarp L g x)
    (hx : x % L.block = (g % L.block) ^^^ 16) : shflSrc L g .bfly 16 31 = x := by
  have h1 := src16_mod hb g
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hlt : (shflSource .bfly (laneOf L g) 16 31).1 < 32 := shflSource_lt _ hl
  have hw2 := (src_sameWarp hb hw.1.1 hlt).1
  have hc1 : shflSrc L g .bfly 16 31 / L.block = g / L.block := hw2.1.2.2.symm
  have hc2 : x / L.block = g / L.block := hw.1.2.2.symm
  have e1 := Nat.div_add_mod (shflSrc L g .bfly 16 31) L.block
  have e2 := Nat.div_add_mod x L.block
  rw [hc1, h1] at e1
  rw [hc2, hx] at e2
  omega

theorem partner_symm {g x : Nat} (hx : x % L.block = (g % L.block) ^^^ 16) :
    g % L.block = (x % L.block) ^^^ 16 := by
  rw [hx, Nat.xor_assoc]
  simp

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
