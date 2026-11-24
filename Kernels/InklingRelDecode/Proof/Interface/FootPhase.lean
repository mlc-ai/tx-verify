-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.FootSrc
public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv

@[expose] public section

/-!
# The barrier-1 events of a default-partition thread

`LedgerInv.phase_inv` counts the barrier-1 events of a thread before its `k`-th event as the phase
of its state plus `3 t` for `t` rounds of the dispatch loop, and it needs `RoleReads` because a
worker's rounds depend on the role bytes. A default-partition thread makes one round and no byte
decides it, so its count is a function of the state alone: `dphase_inv` is the induction of
`phase_inv` for the default partition, which takes no premise on the execution but `Pre`,
`Consistent` and the soundness of the machines.

The consequences used by the shared-word facts: the prologue's role-table store (`st8`) has no
barrier-1 event before it; the softmax region's scratch store has two (the ordinal-0 and
ordinal-1 arrivals are before it); the epilogue's table store (`stTab`) has three.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
include hpre hX hS

/-- **The barrier-1 count of a default-partition thread is its state's phase.** -/
theorem dphase_inv {g : Nat} (hd : g % L.block < 128) :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) →
      ∃ d, s = .d d ∧ b1N X g k = (dPh d).2 := by
  intro k
  induction k with
  | zero =>
    intro s _ hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    have he : (threadCode L g Q).init = .d (.dstart (DStart.D.start L g)) := by
      show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
        else .w (WComp.code L g Q).init) = _
      simp only [hd, ite_true]
    refine ⟨_, he, ?_⟩
    simp [b1N, dPh]
  | succ k ih =>
    intro s' hk hs'
    have hs'' : Frame.stateAt (code L Q) X g (k + 1) = some (some s') := hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs''
    cases hσ : Frame.stateAt (code L Q) X g k with
    | none => rw [hσ] at hs''; simp at hs''
    | some o =>
      cases o with
      | none => rw [hσ] at hs''; simp [Flow.Code.toMachine] at hs''
      | some s =>
        rw [hσ] at hs''
        simp only [Option.bind_some] at hs''
        have hn : (threadCode L g Q).next s e = some (some s') := hs''
        obtain ⟨d0, rfl, h2⟩ := ih s (by omega) hσ
        have hget : X.get (g, k) = some e := he
        have hb := event_b1 hpre hX hS hget hσ
        have hb1 : b1N X g (k + 1) = b1N X g k + bInc (tB1 (.d d0)) := by
          unfold b1N
          rw [countP_take_succ _ he, hb]
          rfl
        obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (DComp.next L g Q d0 e).map
          (Option.map TSt.d) = some (some s') from hn)
        obtain ⟨-, p2⟩ := d_next_ph ha
        refine ⟨a, rfl, ?_⟩
        rw [hb1, h2, p2]
        rfl

/-- **The prologue's role-table store has no barrier-1 event before it.** -/
theorem st8_count {g k : Nat} (hd : g % L.block < 128) (hk : k ≤ (X.tr g).length) {d : ProA.D}
    (hσ : St Q L X g k = some (some (.d (.pro d)))) (hs : d.site = .st8) : b1N X g k = 0 := by
  obtain ⟨d', hd', h⟩ := dphase_inv hpre hX hS hd k _ hk hσ
  cases hd'
  rw [h]
  simp [dPh, hs]

/-- **The softmax region's scratch store has two barrier-1 events before it.** -/
theorem store10_count {g k : Nat} (hd : g % L.block < 128) (hk : k ≤ (X.tr g).length) {d : Sm.D}
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .store10) : b1N X g k = 2 := by
  obtain ⟨d', hd', h⟩ := dphase_inv hpre hX hS hd k _ hk hσ
  cases hd'
  rw [h]
  simp [dPh, hs]

/-- **The epilogue's table store has three barrier-1 events before it.** -/
theorem stTab_count {g k : Nat} (hd : g % L.block < 128) (hk : k ≤ (X.tr g).length) {d : Epi.D}
    (hσ : St Q L X g k = some (some (.d (.epi d)))) (hs : d.site = .stTab) : b1N X g k = 3 := by
  obtain ⟨d', hd', h⟩ := dphase_inv hpre hX hS hd k _ hk hσ
  cases hd'
  rw [h]
  simp [dPh, hs]

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
