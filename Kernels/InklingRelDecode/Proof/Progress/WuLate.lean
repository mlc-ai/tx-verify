-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WuEnd

@[expose] public section

/-!
# The round marker of the dispatch loop: `Worker.late P ↔ 3 ≤ rqN`

`Wt.time` tells the dispatch loop's first round from its later one by the round marker `Worker.late`
that a role's return sets (`Worker.bumpPro`). This file proves that the marker agrees with the
count of register requests at every state where the time reads it (the loop's head, its
`barrier.sync 1` and the load of the role byte), and that the sites of the common start have made
no request and carry no marker.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem late_setTm (P : Loader.Pro) (v : Value) :
    Worker.late (Worker.setTm P v) ↔ Worker.late P := by
  simp [Worker.late, Worker.setTm, Worker.roundReg]

theorem not_late_start (Q : Params) : ¬ Worker.late (Worker.startPro Q) := by
  simp [Worker.late, Worker.startPro, Worker.roundReg, b32]

theorem wn_shfl {L : Launch} {g : Nat} {P0 : Loader.Pro} {e : Event} {d' : Worker.D}
    (h : Worker.next L g ⟨.shfl, P0⟩ e = some (some d')) : d' = ⟨.loop, P0⟩ := by
  simp only [Worker.next] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      exact h.symm
    · simp at h
  · simp at h

theorem wn_ld0 {L : Launch} {g : Nat} {P0 : Loader.Pro} {e : Event} {d' : Worker.D}
    (h : Worker.next L g ⟨.ld0, P0⟩ e = some (some d')) :
    ∃ v, d' = ⟨.bar1, Worker.setTm P0 v⟩ := by
  simp only [Worker.next] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      exact ⟨_, h.symm⟩
    · simp at h
  · simp at h

theorem dispatch_worker {L : Launch} {g : Nat} {P0 : Loader.Pro} {e : Event} {site : Worker.Site}
    {P : Loader.Pro}
    (h : WComp.dispatch L g P0 e = some (some (.worker ⟨site, P⟩))) : site = .bad0 := by
  unfold WComp.dispatch at h
  split at h
  · rename_i d' hd
    unfold WComp.roleStart at h
    cases hs : d'.site <;> simp only [hs] at h <;> (repeat' split at h) <;>
      first
      | (simp at h; done)
      | (simp only [Option.some.injEq, WComp.WSt.worker.injEq, Worker.D.mk.injEq] at h
         exact h.1.symm)
  · simp at h
  · simp at h

/-- The worker's successors that lead to a site the dispatch loop's time reads. -/
theorem late_next {L : Launch} {g : Nat} {s0 a : WComp.WSt} {e : Event}
    (hn : WComp.next L g s0 e = some (some a)) (hto : wTo s0 = false) {site : Worker.Site}
    {P : Loader.Pro} (ha : a = .worker ⟨site, P⟩) :
    (∃ P0, s0 = .worker ⟨.bar0, P0⟩ ∧ site = .ld0 ∧ P = P0) ∨
    (∃ P0 v, s0 = .worker ⟨.ld0, P0⟩ ∧ site = .bar1 ∧ P = Worker.setTm P0 v) ∨
    (∃ P0, s0 = .worker ⟨.bar1, P0⟩ ∧ site = .shfl ∧ P = P0) ∨
    (∃ P0, s0 = .worker ⟨.shfl, P0⟩ ∧ site = .loop ∧ P = P0) ∨
    (∃ P0, s0 = .worker ⟨.loop, P0⟩ ∧ site = .bar2 ∧ P = P0) ∨
    (∃ P0, s0 = .worker ⟨.bar2, P0⟩ ∧ site = .ldRole ∧ P = P0) ∨
    (site = .bad0) ∨
    (site = .loop ∧ wrap s0 = 1 ∧ ∃ P0, P = Worker.bumpPro P0) := by
  subst ha
  cases s0 with
  | worker w =>
    obtain ⟨site0, P0⟩ := w
    cases site0
    · simp only [WComp.next, Worker.next, Option.map_some, Option.some.injEq,
        WComp.WSt.worker.injEq, Worker.D.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact .inl ⟨P0, rfl, rfl, rfl⟩
    · have h1 : Option.map (Option.map WComp.WSt.worker) (Worker.next L g ⟨.ld0, P0⟩ e) =
          some (some (WComp.WSt.worker ⟨site, P⟩)) := hn
      obtain ⟨d', hd', hf⟩ := Ledger.mapInv h1
      obtain ⟨v, rfl⟩ := wn_ld0 hd'
      simp only [WComp.WSt.worker.injEq, Worker.D.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact .inr (.inl ⟨P0, v, rfl, rfl, rfl⟩)
    · simp only [WComp.next, Worker.next, Option.map_some, Option.some.injEq,
        WComp.WSt.worker.injEq, Worker.D.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact .inr (.inr (.inl ⟨P0, rfl, rfl, rfl⟩))
    · have h1 : Option.map (Option.map WComp.WSt.worker) (Worker.next L g ⟨.shfl, P0⟩ e) =
          some (some (WComp.WSt.worker ⟨site, P⟩)) := hn
      obtain ⟨d', hd', hf⟩ := Ledger.mapInv h1
      obtain rfl := wn_shfl hd'
      simp only [WComp.WSt.worker.injEq, Worker.D.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact .inr (.inr (.inr (.inl ⟨P0, rfl, rfl, rfl⟩)))
    · simp only [WComp.next, Worker.next, Option.map_some, Option.some.injEq,
        WComp.WSt.worker.injEq, Worker.D.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact .inr (.inr (.inr (.inr (.inl ⟨P0, rfl, rfl, rfl⟩))))
    · simp only [WComp.next, Worker.next, Option.map_some, Option.some.injEq,
        WComp.WSt.worker.injEq, Worker.D.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨P0, rfl, rfl, rfl⟩)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl (dispatch_worker hn)))))))
    all_goals simp [wTo] at hto
  | idle d =>
    by_cases hs : d.site = .inc
    · obtain ⟨s, P0⟩ := d
      simp only at hs
      subst hs
      have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P0⟩)) =
          some (some (WComp.WSt.worker ⟨site, P⟩)) := hn
      simp only [Option.some.injEq, WComp.WSt.worker.injEq, Worker.D.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, by simp [wrap], P0, rfl⟩))))))
    · rw [Wt.next_idle_eq hs] at hn
      obtain ⟨a, -, h⟩ := Ledger.mapInv hn
      cases h
  | loader d P0 =>
    by_cases hs : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P0⟩)) =
          some (some (WComp.WSt.worker ⟨site, P⟩)) := hn
      simp only [Option.some.injEq, WComp.WSt.worker.injEq, Worker.D.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, by simp [wrap], P0, rfl⟩))))))
    · rw [Wt.next_loader_eq P0 hs] at hn
      obtain ⟨a, -, h⟩ := Ledger.mapInv hn
      cases h
  | mma d P0 =>
    by_cases hs : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hs
      subst hs
      have h1 : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P0⟩)) =
          some (some (WComp.WSt.worker ⟨site, P⟩)) := hn
      simp only [Option.some.injEq, WComp.WSt.worker.injEq, Worker.D.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, by simp [wrap], P0, rfl⟩))))))
    · rw [Wt.next_mma_eq P0 hs] at hn
      obtain ⟨a, -, h⟩ := Ledger.mapInv hn
      cases h
  | exit x =>
    obtain ⟨s, P0⟩ := x
    cases s
    · have h1 : some (some (WComp.WSt.exit ⟨.ret, P0⟩)) =
          some (some (WComp.WSt.worker ⟨site, P⟩)) := hn
      cases h1
    · have h1 : (none : Option (Option WComp.WSt)) = some (some (WComp.WSt.worker ⟨site, P⟩)) :=
        hn
      cases h1

theorem wrap_ph {s : WComp.WSt} (h : wrap s = 1) : (wPh s).1 = 2 ∧ wKind s = 1 := by
  cases s with
  | worker w => simp [wrap] at h
  | idle d =>
    obtain ⟨s, P⟩ := d
    cases s <;> simp [wrap, wPh, wKind] at h ⊢
  | loader d P =>
    obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
    cases s <;> simp [wrap, wPh, wKind] at h ⊢
  | mma d P =>
    obtain ⟨s, i, n, tm, pro⟩ := d
    cases s <;> simp [wrap, wPh, wKind] at h ⊢
  | exit x => simp [wrap] at h

/-- The number of register requests grows by the state's request. -/
theorem rqN_succ (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {e : Event} {s : TSt}
    (he : (X.tr g)[k]? = some e) (hσ : St Q L X g k = some (some s)) :
    rqN X g (k + 1) = rqN X g k + rInc (tReq s) := by
  have hget : X.get (g, k) = some e := he
  obtain ⟨hreq, -⟩ := event_req hX hS hget hσ
  unfold rqN
  rw [countP_take_succ _ he]
  by_cases hr : SetMaxNReg.isRequest e = true
  · have h2 := hreq.mp hr
    simp [hr, h2, rInc_eq]
  · have h2 : ¬ (tReq s).isSome = true := fun h => hr (hreq.mpr h)
    simp [hr, h2, rInc_eq]

/-- The round marker's invariant at a state. -/
def LateAt (X : Execution) (g k : Nat) (s : TSt) : Prop :=
  (∀ P site, (site = .bar0 ∨ site = .ld0 ∨ site = .bar1 ∨ site = .shfl) →
    s = .w (.worker ⟨site, P⟩) → rqN X g k = 0 ∧ ¬ Worker.late P) ∧
  (∀ P site, (site = .loop ∨ site = .bar2 ∨ site = .ldRole) →
    s = .w (.worker ⟨site, P⟩) → (Worker.late P ↔ 3 ≤ rqN X g k))

/-- **`Worker.late P ↔ 3 ≤ rqN`** at the dispatch loop's states, and no request and no marker
at the common start's. -/
theorem late_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g : Nat} :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) → LateAt X g k s := by
  intro k
  induction k with
  | zero =>
    intro s _ hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    have h0 : rqN X g 0 = 0 := by simp [rqN]
    refine ⟨fun P site hsite hs => ?_, fun P site hsite hs => ?_⟩
    · refine ⟨h0, ?_⟩
      by_cases hd : g % L.block < 128
      · have he : (threadCode L g Q).init = .d (.dstart (DStart.D.start L g)) := by
          show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
            else .w (WComp.code L g Q).init) = _
          simp only [hd, ite_true]
        rw [he] at hs
        cases hs
      · have he : (threadCode L g Q).init =
            .w (.worker (Worker.D.start (Worker.startPro Q))) := by
          show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
            else .w (WComp.code L g Q).init) = _
          simp only [hd, ite_false]
        rw [he] at hs
        simp only [TSt.w.injEq, WComp.WSt.worker.injEq, Worker.D.mk.injEq, Worker.D.start] at hs
        obtain ⟨-, rfl⟩ := hs
        exact not_late_start Q
    · by_cases hd : g % L.block < 128
      · have he : (threadCode L g Q).init = .d (.dstart (DStart.D.start L g)) := by
          show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
            else .w (WComp.code L g Q).init) = _
          simp only [hd, ite_true]
        rw [he] at hs
        cases hs
      · have he : (threadCode L g Q).init =
            .w (.worker (Worker.D.start (Worker.startPro Q))) := by
          show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
            else .w (WComp.code L g Q).init) = _
          simp only [hd, ite_false]
        rw [he] at hs
        simp only [TSt.w.injEq, WComp.WSt.worker.injEq, Worker.D.mk.injEq, Worker.D.start] at hs
        obtain ⟨hs1, -⟩ := hs
        subst hs1
        simp at hsite
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
        have hσ' : St Q L X g k = some (some s) := hσ
        have hσ1 : St Q L X g (k + 1) = some (some s') := hs'
        have ih' := ih s (by omega) hσ'
        have hrq := rqN_succ hX hS he hσ'
        obtain ⟨hto, t, h1, h2, h3, h4, h5, h6⟩ := phase_inv hpre hX hS hR k s (by omega) hσ'
        obtain ⟨hto', t', h1', h2', h3', h4', h5', h6'⟩ :=
          phase_inv hpre hX hS hR (k + 1) s' hk hs'
        unfold LateAt
        cases s with
        | d s0 =>
          obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (DComp.next L g Q s0 e).map
            (Option.map TSt.d) = some (some s') from hn)
          exact ⟨fun P site _ h => (by cases h), fun P site _ h => (by cases h)⟩
        | w s0 =>
          obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (WComp.next L g s0 e).map
            (Option.map TSt.w) = some (some s') from hn)
          have hs0 : wTo s0 = false := hto
          have e3 : tReq (TSt.w s0) = wReqS s0 := rfl
          rw [e3] at hrq
          refine ⟨fun P site hsite hs => ?_, fun P site hsite hs => ?_⟩
          · simp only [TSt.w.injEq] at hs
            rcases late_next ha hs0 hs with ⟨P0, rfl, hst, rfl⟩ | ⟨P0, v, rfl, hst, rfl⟩ |
              ⟨P0, rfl, hst, rfl⟩ | ⟨P0, rfl, hst, rfl⟩ | ⟨P0, rfl, hst, rfl⟩ |
              ⟨P0, rfl, hst, rfl⟩ | hst | ⟨hst, -⟩
            · obtain ⟨i1, i2⟩ := ih'.1 _ .bar0 (.inl rfl) rfl
              refine ⟨?_, i2⟩
              rw [hrq, i1]
              simp [wReqS, wReq, rInc]
            · obtain ⟨i1, i2⟩ := ih'.1 _ .ld0 (.inr (.inl rfl)) rfl
              refine ⟨?_, fun hl => i2 ((late_setTm _ _).mp hl)⟩
              rw [hrq, i1]
              simp [wReqS, wReq, rInc]
            · obtain ⟨i1, i2⟩ := ih'.1 _ .bar1 (.inr (.inr (.inl rfl))) rfl
              refine ⟨?_, i2⟩
              rw [hrq, i1]
              simp [wReqS, wReq, rInc]
            · subst hst
              simp at hsite
            · subst hst
              simp at hsite
            · subst hst
              simp at hsite
            · subst hst
              simp at hsite
            · subst hst
              simp at hsite
          · simp only [TSt.w.injEq] at hs
            rcases late_next ha hs0 hs with ⟨P0, rfl, hst, rfl⟩ | ⟨P0, v, rfl, hst, rfl⟩ |
              ⟨P0, rfl, hst, rfl⟩ | ⟨P0, rfl, hst, rfl⟩ | ⟨P0, rfl, hst, rfl⟩ |
              ⟨P0, rfl, hst, rfl⟩ | hst | ⟨hst, hw, P1, hP⟩
            · subst hst
              simp at hsite
            · subst hst
              simp at hsite
            · subst hst
              simp at hsite
            · -- shfl to loop
              obtain ⟨i1, i2⟩ := ih'.1 _ .shfl (.inr (.inr (.inr rfl))) rfl
              rw [hrq, i1]
              simp [wReqS, wReq, rInc]
              exact i2
            · -- loop to bar2
              have hl := ih'.2 _ .loop (.inl rfl) rfl
              rw [hrq]
              simp only [wReqS, wReq, rInc, Option.isSome_some, ite_true] at *
              simp only [tPh, wPh] at h1
              rw [hl]
              omega
            · -- bar2 to ldRole
              have hl := ih'.2 _ .bar2 (.inr (.inl rfl)) rfl
              rw [hrq]
              simp [wReqS, wReq, rInc]
              exact hl
            · subst hst
              simp at hsite
            · -- a role returns to the loop's head
              obtain ⟨hp, hk⟩ := wrap_ph hw
              subst hs
              subst hst
              have hk1 : tKind (TSt.w s0) = 1 := hk
              have ht0 := h4 hk1
              simp only [tPh] at h1
              simp only [tPh, wPh] at h1'
              have hmono : rqN X g k ≤ rqN X g (k + 1) := by omega
              have hl : Worker.late P := by rw [hP]; exact Worker.late_bumpPro _
              constructor
              · intro _
                omega
              · intro _
                exact hl
end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
