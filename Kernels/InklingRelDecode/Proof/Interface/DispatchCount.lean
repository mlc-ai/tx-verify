-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleAll
public import Kernels.InklingRelDecode.Proof.Interface.FootRoleRead
public import Kernels.InklingRelDecode.Proof.Thread.FootRole

@[expose] public section

/-!
# The loads of the role byte along a worker thread

A worker's dispatch loop loads the byte of its role (the event at `Worker.Site.ldRole`) once per
round, and `phase_inv` (`LedgerInv.lean`) says a worker makes at most two rounds: the counts of its
barrier-1 events before a state are the state's phase plus `3 t` with `t ≤ 1`. This file counts the
loads with the same induction.

`ldN X g k` is the number of events of thread `g` before its event `k` that are at the position of
the load. At a state of kind 0 (the common start and the dispatch loop, which is left only by the
load of the role byte) the number is at most `t`; at the other states (a role, the exit) it is at
most `t + 1`: the load that leads into a role is counted, and a role returns to the loop's head only
at its tail, which is one round on (`wrap`). With `t ≤ 1` the loads before a followed state are at
most two, counting the load the state itself is (`ldN_succ_le`).

A thread whose machine stopped has at most one event after the stop, an undefined-behaviour event
(`Machine.Trace.dead`), which may be at the position of the load. So the loads in the whole trace
are at most three (`dispatch_count`): two from followed states and that one.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The number of events of thread `g` before its event `k` at the position of the load of the
role byte. -/
def ldN (X : Execution) (g k : Nat) : Nat :=
  ((X.tr g).take k).countP (fun e => decide (e.pc = Worker.Site.ldRole.pc))

/-- **After the machine stops there is at most one more event**: if the abstract state is lost
after the first `j` events of a run, the run has at most `j + 1` events. -/
theorem trace_length_le {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
    {M : Machine K A L g} {σ : M.St} {es : List Event} (h : M.Trace σ es) :
    ∀ {j : Nat}, M.after σ (es.take j) = none → es.length ≤ j + 1 := by
  induction h with
  | nil σ =>
    intro j hj
    simp at hj
  | step hf hn _ ih =>
    intro j hj
    cases j with
    | zero => simp at hj
    | succ j =>
      simp only [List.take_succ_cons, Machine.after_cons, hn, Option.bind_some] at hj
      have := ih hj
      simp only [List.length_cons]
      omega
  | last hf =>
    intro j hj
    simp
  | dead hf hn hl _ =>
    intro j hj
    cases j with
    | zero => simp at hj
    | succ j =>
      simp only [List.length_cons]
      omega

/-- **The loads of the role byte before a state follow its kind and its round**: the state is a
worker's, and if the barrier-1 events before it are its phase plus `3 t`, the loads before it are
at most `t`, plus one unless the state is in the common start or the dispatch loop. -/
theorem ldN_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g : Nat}
    (hw : 128 ≤ g % L.block) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, St Q L X g k = some (some s) →
      (∃ s0, s = .w s0) ∧ ∀ t, b1N X g k = (tPh s).2 + 3 * t →
        ldN X g k ≤ t + (if tKind s = 0 then 0 else 1) := by
  intro k
  induction k with
  | zero =>
    intro _ s hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    have hd : ¬ g % L.block < 128 := by omega
    have he : (threadCode L g Q).init = .w (.worker (Worker.D.start (Worker.startPro Q))) := by
      show (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
        else .w (WComp.code L g Q).init) = _
      simp only [hd, ite_false]
    exact ⟨⟨_, he⟩, fun t _ => by simp [ldN]⟩
  | succ k ih =>
    intro hk s' hs'
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
        obtain ⟨⟨s0, rfl⟩, ihc⟩ := ih (by omega) s hσ
        have hget : X.get (g, k) = some e := he
        obtain ⟨hto, t0, h1, h2, h3, h4, h5, h6⟩ :=
          phase_inv hpre hX hS hR (g := g) k _ (by omega) hσ
        obtain ⟨hto', t1, h1', h2', h3', h4', h5', h6'⟩ :=
          phase_inv hpre hX hS hR (g := g) (k + 1) s' hk hs'
        have hb := event_b1 hpre hX hS hget hσ
        have hb1 : b1N X g (k + 1) = b1N X g k + bInc (tB1 (TSt.w s0)) := by
          unfold b1N
          rw [countP_take_succ _ he, hb]
          rfl
        have hld : ldN X g (k + 1) = ldN X g k +
            (if e.pc = Worker.Site.ldRole.pc then 1 else 0) := by
          unfold ldN
          rw [countP_take_succ _ he]
          simp
        have hpc := Frame.event_pc hS hX hget hσ
        obtain ⟨a, ha, rfl⟩ := Ledger.mapInv (show (WComp.next L g s0 e).map
          (Option.map TSt.w) = some (some s') from hn)
        have hs0 : wTo s0 = false := hto
        have hta : wTo a = false := hto'
        obtain ⟨p1, p2, k1, k2, k3, k4⟩ := w_next ha hs0
        have e1 : tPh (TSt.w a) = wPh a := rfl
        have e2 : tPh (TSt.w s0) = wPh s0 := rfl
        have e4 : tB1 (TSt.w s0) = wB1S s0 := rfl
        have e5 : tKind (TSt.w s0) = wKind s0 := rfl
        have e6 : tKind (TSt.w a) = wKind a := rfl
        rw [e2] at h2
        rw [e4] at hb1
        rw [e1] at h2'
        have ht1 : t1 = t0 + wrap s0 := by omega
        refine ⟨⟨a, rfl⟩, fun t ht => ?_⟩
        rw [e1] at ht
        have htt : t = t1 := by omega
        subst htt
        have hih := ihc t0 (by rw [e2]; exact h2)
        rw [e5] at hih
        rw [e6, hld]
        by_cases hl : ldRoleSt s0 = true
        · obtain ⟨P, rfl⟩ := ldRoleSt_form hl
          have hpc' : e.pc = Worker.Site.ldRole.pc := hpc
          obtain ⟨a', bs, -, hdisj, -⟩ := dispatch_role ha
          have hk0 : wKind a ≠ 0 := by
            rcases hdisj with ⟨-, h⟩ | ⟨i, -, -, h⟩ | ⟨i, hi, hi4, h⟩
            · omega
            · omega
            · rw [hta] at h
              exact absurd h (by simp)
          have hwr : wrap (.worker ⟨.ldRole, P⟩) = 0 := rfl
          have hk00 : wKind (.worker ⟨.ldRole, P⟩) = 0 := rfl
          rw [hk00] at hih
          simp only [hpc', hk0, ↓reduceIte]
          simp only [↓reduceIte] at hih
          omega
        · have hl' : ldRoleSt s0 = false := by simpa using hl
          have hne : e.pc ≠ Worker.Site.ldRole.pc := by
            intro h
            have h' : TSt.pc (.w s0) = Worker.Site.ldRole.pc := hpc.symm.trans h
            obtain ⟨P, hP⟩ := pc_ldRole_state h'
            have hs0P : s0 = .worker ⟨.ldRole, P⟩ := by simpa using hP
            subst hs0P
            exact hl rfl
          simp only [hne, ↓reduceIte]
          have hle := wKind_le s0
          have hwle := wrap_le s0
          rcases (by omega : wKind s0 = 0 ∨ wKind s0 = 1 ∨ wKind s0 = 2) with hk0 | hk0 | hk0
          · have := k4 hk0 hl'
            simp only [hk0, ↓reduceIte] at hih
            simp only [this, ↓reduceIte]
            omega
          · simp only [hk0, Nat.one_ne_zero, ↓reduceIte] at hih
            by_cases hwr : wrap s0 = 0
            · have := k1 hk0 hwr
              simp only [this, Nat.one_ne_zero, ↓reduceIte]
              omega
            · have h1w : wrap s0 = 1 := by omega
              by_cases ha0 : wKind a = 0
              · simp only [ha0, ↓reduceIte]
                omega
              · simp only [ha0, ↓reduceIte]
                omega
          · simp only [hk0, show (2 : Nat) ≠ 0 by omega, ↓reduceIte] at hih
            have := k3 hk0
            simp only [this, show (2 : Nat) ≠ 0 by omega, ↓reduceIte]
            omega

/-- **The loads of the role byte before a followed state, and the load it is**, are at most two. -/
theorem ldN_succ_le (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g : Nat}
    (hw : 128 ≤ g % L.block) {k : Nat} (hk : k ≤ (X.tr g).length) {s : TSt}
    (hσ : St Q L X g k = some (some s)) :
    ldN X g k + (if TSt.pc s = Worker.Site.ldRole.pc then 1 else 0) ≤ 2 := by
  obtain ⟨⟨s0, rfl⟩, ihc⟩ := ldN_inv hpre hX hS hR hw k hk s hσ
  obtain ⟨-, t, -, h2, -, -, -, h6⟩ := phase_inv hpre hX hS hR (g := g) k _ hk hσ
  have hih := ihc t h2
  by_cases h : TSt.pc (.w s0) = Worker.Site.ldRole.pc
  · obtain ⟨P, hP⟩ := pc_ldRole_state h
    have hs0P : s0 = .worker ⟨.ldRole, P⟩ := by simpa using hP
    subst hs0P
    have hk00 : tKind (TSt.w (.worker ⟨.ldRole, P⟩)) = 0 := rfl
    rw [hk00] at hih
    simp only [h, ↓reduceIte]
    simp only [↓reduceIte] at hih
    omega
  · simp only [h, ↓reduceIte]
    have : (if tKind (TSt.w s0) = 0 then 0 else 1) ≤ 1 := by split <;> omega
    omega

/-- **A worker's trace has at most three events at the position of the load of the role byte**:
at most two from followed states (the first load leads into a role, the second is the exit), and,
if the machine stopped, the one undefined-behaviour event after the stop. -/
theorem dispatch_count (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hR : RoleReads L X) {g : Nat} (hg : g < L.threads) (hw : 128 ≤ g % L.block) :
    ldN X g (X.tr g).length ≤ 3 := by
  cases hlen : St Q L X g (X.tr g).length with
  | none =>
    obtain ⟨i, d, hi, hd, hd'⟩ := Frame.first_stop ht hg hlen
    have hbound : (X.tr g).length ≤ i + 1 + 1 := by
      have htr := Frame.trace hS hX hg
      have h1 : (code L Q g).toMachine.after (some (code L Q g).init) ((X.tr g).take (i + 1)) =
          none := hd'
      exact trace_length_le htr h1
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[i]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hget : X.get (g, i) = some e := he
    have hpc := Frame.event_pc hS hX hget hd
    have h2 := ldN_succ_le hpre hX hS hR hw (k := i) (by omega) hd
    have hld : ldN X g (i + 1) = ldN X g i +
        (if e.pc = Worker.Site.ldRole.pc then 1 else 0) := by
      unfold ldN
      rw [countP_take_succ _ he]
      simp
    have hpc' : e.pc = TSt.pc d := hpc
    have hrest : ldN X g (X.tr g).length ≤ ldN X g (i + 1) + 1 := by
      unfold ldN
      obtain ⟨m, hm⟩ : ∃ m, (X.tr g).length = (i + 1) + m :=
        ⟨_, (Nat.add_sub_of_le (by omega)).symm⟩
      rw [hm, List.take_add, List.countP_append]
      have : (((X.tr g).drop (i + 1)).take m).length ≤ 1 := by
        simp only [List.length_take, List.length_drop]
        omega
      have := List.countP_le_length (p := fun e => decide (e.pc = Worker.Site.ldRole.pc))
        (l := ((X.tr g).drop (i + 1)).take m)
      omega
    rw [hpc'] at hld
    omega
  | some o =>
    cases o with
    | none => exact absurd hlen (ht g _ hg)
    | some s =>
      have := ldN_succ_le hpre hX hS hR hw (k := (X.tr g).length) le_rfl hlen
      omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
