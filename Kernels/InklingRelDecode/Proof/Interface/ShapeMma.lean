-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Interface.MmaFacts
public import Kernels.InklingRelDecode.Proof.Result.MmaPremises

@[expose] public section

/-!
# The MMA warp's predecessors

The thread-layer half of `QkChain.prev` and of `OAcc.next` (`Result/MmaPremises.lean`,
`Result/MmaO.lean`): the earlier state and its MMA event, as a statement of abstract states.

* `mma_next_pred`: a successor state of the composed worker machine that is an MMA state at a site
  other than `setMaxReg` is the MMA machine's successor of an MMA state with the same inherited
  registers.
* `qk_pred`, `pv_pred`: if the MMA warp is at QK (PV) step `j + 1` at event `k`, it was at step `j`
  at an earlier event `k'` (the state `{d with site := step j}`, the machine's `qkNext`/`pvNext`
  inverse) and the event at `k'` is an MMA event.

What is left to the protocol layer is the `ReadSource` conjunct of the two fields: that the earlier
MMA is the accumulator read source of every cell the later one writes
(`SOTmemOrder.pv_before_qk_exec`, the S handoffs).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-! ### The successors of the MMA machine -/

/-- A QK step `j + 1` is the successor of QK step `j` and nothing else. -/
theorem mma_next_qk {d d' : Mma.D} {e : Event} (hj : j + 1 < 8)
    (h : Mma.next L g d e = some (some d')) (hs : d'.site = .qk ⟨j + 1, hj⟩) :
    d.site = .qk ⟨j, by omega⟩ ∧ d' = { d with site := .qk ⟨j + 1, hj⟩ } := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all; exact Fin.ext (by assumption))

/-- A PV step `j + 1` is the successor of PV step `j` and nothing else. -/
theorem mma_next_pv {d d' : Mma.D} {e : Event} (hj : j + 1 < 8)
    (h : Mma.next L g d e = some (some d')) (hs : d'.site = .pv ⟨j + 1, hj⟩) :
    d.site = .pv ⟨j, by omega⟩ ∧ d' = { d with site := .pv ⟨j + 1, hj⟩ } := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all; exact Fin.ext (by assumption))

/-! ### The composed worker machine -/

/-- **An MMA successor of the composed worker machine** other than the first one is the MMA
machine's successor of an MMA state with the same inherited registers. -/
theorem wcomp_next_mma {s0 : WComp.WSt} {e : Event} {d : Mma.D} {P : Loader.Pro}
    (h : WComp.next L g s0 e = some (some (.mma d P))) (hs : d.site ≠ .setMaxReg) :
    ∃ d0, s0 = .mma d0 P ∧ Mma.next L g d0 e = some (some d) := by
  cases s0 with
  | worker w =>
    obtain ⟨site, P0⟩ := w
    cases site
    all_goals try (exfalso; simp [WComp.next, Worker.next] at h; done)
    · exfalso
      simp only [WComp.next, WComp.dispatch] at h
      split at h
      · rename_i d' _
        generalize d'.site = st at h
        cases st <;> simp only [WComp.roleStart] at h
        all_goals first
          | (simp at h; done)
          | (split at h <;> simp at h; done)
          | (split at h
             · split at h
               · simp only [Option.some.injEq, WComp.WSt.mma.injEq] at h
                 obtain ⟨rfl, -⟩ := h
                 exact hs rfl
               · simp at h
             · simp at h)
      · simp at h
      · simp at h
  | idle d0 =>
    exfalso
    simp only [WComp.next] at h
    split at h
    · simp at h
    · simp at h
  | loader d0 P0 =>
    exfalso
    simp only [WComp.next] at h
    split at h
    · simp at h
    · simp at h
  | mma d0 P0 =>
    simp only [WComp.next] at h
    split at h
    · simp at h
    · cases hn : Mma.next L g d0 e with
      | none => simp [hn] at h
      | some o =>
        cases o with
        | none => simp [hn] at h
        | some d1 =>
          simp only [hn, Option.map_some, Option.some.injEq, WComp.WSt.mma.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨d0, rfl, hn⟩
  | exit x =>
    exfalso
    simp only [WComp.next] at h
    split at h
    · simp at h
    · cases h

/-! ### The events at the MMA sites -/

/-- **The event at a QK or PV MMA site is an MMA.** The event of thread `g` at an MMA state of a
QK or PV step is a `tcgen05.mma` event (not undefined behaviour, which comes only after the
machine stopped, and not an exit). -/
theorem mma_issue_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k : Nat} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) {d : Mma.D} {P : Loader.Pro}
    (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hs : (∃ j, d.site = .qk j) ∨ ∃ j, d.site = .pv j) :
    ∃ pc dst sp acc mask, e = ⟨pc, .tc (.mma dst sp acc mask)⟩ := by
  have he' : (X.tr g)[k]? = some e := he
  obtain ⟨o, hF⟩ := (Frame.trace hf.sound hX hg).fired_at he' hσ
  obtain ⟨pc, kd⟩ := e
  cases o with
  | none =>
    exfalso
    obtain ⟨t', -, hf'⟩ := hF
    rcases fires_none_ends hf' with ⟨fl, hu⟩ | hx
    · simp only at hu
      subst hu
      rcases hf.ub_stop hg he with h | h <;> rw [hσ] at h <;> cases h
    · simp only at hx
      subst hx
      rcases exit_event_state hX hf.sound hf.tracked he with ⟨d', h, -⟩ | ⟨x, h, -⟩ <;>
        rw [hσ] at h <;> cases h
  | some u =>
    obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
    have hsh := EvW.mma_shape hpre hg (d := d) (P := P) ⟨t', ⟨ha, hi.2⟩, hf'⟩
    unfold EvW.MmShape at hsh
    rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hj] at hsh
      obtain ⟨da, db, dsc, -, -, -, h⟩ := hsh
      exact ⟨pc, _, _, _, _, by rw [(Event.mk.inj h).2]⟩
    · rw [hj] at hsh
      obtain ⟨db, dsc, -, -, h⟩ := hsh
      exact ⟨pc, _, _, _, _, by rw [(Event.mk.inj h).2]⟩

/-! ### Predecessors -/

theorem mma_ne_init (d : Mma.D) (P : Loader.Pro) :
    TSt.w (.mma d P) ≠ (code L Q g).init := by
  show _ ≠ (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
    else TSt.w (WComp.code L g Q).init)
  split <;> simp

/-- **The state before an MMA state.** An MMA state at a site other than `setMaxReg` has a
predecessor: an earlier index at which the thread was at an MMA state `d0` with the same inherited
registers, whose event `e` is in the trace and whose successor is the state. -/
theorem mma_state_pred {g k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hX : Consistent L kernel asms mem0 X)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site ≠ .setMaxReg) :
    ∃ (k0 : Nat) (e : Event) (d0 : Mma.D), k0 < k ∧ g < L.threads ∧ X.get (g, k0) = some e ∧
      St Q L X g k0 = some (some (.w (.mma d0 P))) ∧ Mma.next L g d0 e = some (some d) := by
  obtain ⟨k0, e, s0, hlt, he, hs0, hn⟩ := stateAt_pred hσ (mma_ne_init d P)
  have hge : X.get (g, k0) = some e := he
  refine ⟨k0, e, ?_⟩
  cases s0 with
  | d s =>
    rw [next_d] at hn
    obtain ⟨a, -, h⟩ := map_map_eq_some_some hn
    cases h
  | w s =>
    rw [next_w] at hn
    obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
    cases h
    obtain ⟨d0, rfl, hd0⟩ := wcomp_next_mma ha hs
    exact ⟨d0, hlt, Frame.lt_of_get hX hge, hge, hs0, hd0⟩

/-- **The thread-layer half of `QkChain.prev`.** If the MMA warp is at QK step `j + 1` before
event `k`, it was at QK step `j` (the same state with the site changed) before an earlier event
`k'`, which is an MMA event. -/
theorem qk_pred (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k j : Nat} {d : Mma.D} {P : Loader.Pro} (hj : j + 1 < 8)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .qk ⟨j + 1, hj⟩) :
    ∃ k', k' < k ∧ St Q L X g k' =
        some (some (.w (.mma { d with site := .qk ⟨j, by omega⟩ } P))) ∧
      ∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩ := by
  obtain ⟨k0, e, d0, hlt, hg, he, hs0, hn⟩ := mma_state_pred hX hσ (by rw [hs]; simp)
  obtain ⟨h1, h2⟩ := mma_next_qk hj hn hs
  have hd0 : d0 = { d with site := .qk ⟨j, by omega⟩ } := by
    cases d0
    cases d
    simp only [Mma.D.mk.injEq] at h2 ⊢
    simp_all
  subst hd0
  refine ⟨k0, hlt, hs0, ?_⟩
  obtain ⟨pc, dst, sp, acc, mask, h⟩ := mma_issue_event hpre hX hf hg he hs0
    (.inl ⟨⟨j, by omega⟩, rfl⟩)
  exact ⟨pc, dst, sp, acc, mask, by rw [he, h]⟩

/-- **The thread-layer half of `OAcc.next`.** The same for PV step `j + 1`. -/
theorem pv_pred (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k j : Nat} {d : Mma.D} {P : Loader.Pro} (hj : j + 1 < 8)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site = .pv ⟨j + 1, hj⟩) :
    ∃ k', k' < k ∧ St Q L X g k' =
        some (some (.w (.mma { d with site := .pv ⟨j, by omega⟩ } P))) ∧
      ∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩ := by
  obtain ⟨k0, e, d0, hlt, hg, he, hs0, hn⟩ := mma_state_pred hX hσ (by rw [hs]; simp)
  obtain ⟨h1, h2⟩ := mma_next_pv hj hn hs
  have hd0 : d0 = { d with site := .pv ⟨j, by omega⟩ } := by
    cases d0
    cases d
    simp only [Mma.D.mk.injEq] at h2 ⊢
    simp_all
  subst hd0
  refine ⟨k0, hlt, hs0, ?_⟩
  obtain ⟨pc, dst, sp, acc, mask, h⟩ := mma_issue_event hpre hX hf hg he hs0
    (.inr ⟨⟨j, by omega⟩, rfl⟩)
  exact ⟨pc, dst, sp, acc, mask, by rw [he, h]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
