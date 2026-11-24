-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv

@[expose] public section

/-!
# A lower bound on the barrier-1 count, without the role bytes

`phase_inv` (`LedgerInv.lean`) gives the exact counts of a thread's barrier-1 events from its
state, using the role bytes the dispatch reads (`RoleReads`). A lower bound needs no role byte: a
step of a machine adds to the barrier-1 component of the state's phase (`tPh`) at most what its
event adds to the count (`w_next_ph_le`; a return to the dispatch lowers the phase), so the phase's
barrier-1 component is at most the count at every state (`b1_ph_le`). A loader state and the
dispatch have phase component 1 (`one_le_b1N_loader`, `one_le_b1N_ldRole`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem bad0_next {g : Nat} {P : Loader.Pro} {e : Event} :
    WComp.next L g (.worker ⟨.bad0, P⟩) e = some (some (.worker ⟨.bad1, P⟩)) := rfl

theorem bad1_next {g : Nat} {P : Loader.Pro} {e : Event} :
    WComp.next L g (.worker ⟨.bad1, P⟩) e = some (some (.worker ⟨.loop, P⟩)) := rfl

/-- **A worker step adds to the barrier-1 phase at most its barrier-1 event.** -/
theorem w_next_ph_le {g : Nat} {s s' : WComp.WSt} {e : Event}
    (h : WComp.next L g s e = some (some s')) : (wPh s').2 ≤ (wPh s).2 + bInc (wB1S s) := by
  by_cases hs : wTo s = false
  · have := (w_next h hs).2.1
    omega
  · cases s with
    | worker w =>
      obtain ⟨site, P⟩ := w
      cases site <;> simp only [wTo, reduceCtorEq, or_false, false_or,
        decide_eq_false_iff_not, not_true_eq_false, not_false_eq_true] at hs
      case bad0 =>
        rw [bad0_next] at h
        obtain rfl := Option.some.inj (Option.some.inj h)
        simp [wPh, wB1S, wB1, bInc]
      case bad1 =>
        rw [bad1_next] at h
        obtain rfl := Option.some.inj (Option.some.inj h)
        simp [wPh, wB1S, wB1, bInc]
      all_goals (simp only [WComp.next] at h; cases h)
    | _ => simp [wTo] at hs

/-- **A step adds to the barrier-1 phase at most its barrier-1 event.** -/
theorem t_next_ph_le {g : Nat} {s s' : TSt} {e : Event}
    (h : (threadCode L g Q).next s e = some (some s')) :
    (tPh s').2 ≤ (tPh s).2 + bInc (tB1 s) := by
  cases s with
  | d s0 =>
    obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (DComp.next L g Q s0 e).map
      (Option.map TSt.d) = some (some s') from h)
    have := (d_next_ph ha).2
    show (dPh a).2 ≤ (dPh s0).2 + bInc (dB1 s0)
    omega
  | w s0 =>
    obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (WComp.next L g s0 e).map
      (Option.map TSt.w) = some (some s') from h)
    exact w_next_ph_le ha

/-- **The barrier-1 component of a state's phase is at most the thread's barrier-1 count.** -/
theorem b1_ph_le (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g : Nat} :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) → (tPh s).2 ≤ b1N X g k := by
  intro k
  induction k with
  | zero =>
    intro s _ hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    by_cases hd : g % L.block < 128
    · have he : (threadCode L g Q).init = .d (.dstart (DStart.D.start L g)) := by
        show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
          else .w (WComp.code L g Q).init) = _
        simp only [hd, ite_true]
      rw [he]
      simp [tPh, dPh]
    · have he : (threadCode L g Q).init =
          .w (.worker (Worker.D.start (Worker.startPro Q))) := by
        show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
          else .w (WComp.code L g Q).init) = _
        simp only [hd, ite_false]
      rw [he]
      simp [tPh, wPh, Worker.D.start]
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
        have h1 := ih s (by omega) hσ
        have hget : X.get (g, k) = some e := he
        have hb := event_b1 hpre hX hS hget hσ
        have hb1 : b1N X g (k + 1) = b1N X g k + bInc (tB1 s) := by
          unfold b1N
          rw [countP_take_succ _ he, hb]
          rfl
        have := t_next_ph_le hn
        omega

/-- A state of the dispatch has a barrier-1 event before it. -/
theorem one_le_b1N_ldRole (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {P : Loader.Pro}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.worker ⟨.ldRole, P⟩)))) :
    1 ≤ b1N X g k := by
  have := b1_ph_le hpre hX hS k _ hk hσ
  simpa [tPh, wPh] using this

/-- A loader state has a barrier-1 event before it. -/
theorem one_le_b1N_loader (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {d : Loader.D}
    {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) : 1 ≤ b1N X g k := by
  have := b1_ph_le hpre hX hS k _ hk hσ
  have h1 : 1 ≤ (wPh (.loader d P)).2 := by
    simp only [wPh]
    split <;> simp
  exact le_trans h1 this

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
