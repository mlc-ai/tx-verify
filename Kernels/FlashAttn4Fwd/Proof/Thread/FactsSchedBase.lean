-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarpColl
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsFire
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMachine
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLags

@[expose] public section

/-! # Collective schedules from the roles' counts and site tables

A collective schedule (`Cross.CollSched`) of the events `p` follows from three facts of the
threads' machine states and one of the schedule:

* the events `p` before a state are a function `C g d` of the state (a conjunct of the role's run
  invariant, `roleJ`);
* the event fired from a state is one of `p` exactly when the state's site is a collective site
  (`isP g d`: the site's kind, `nextKind`, or its barrier);
* a state at a collective site has time `S (key g) (C g d)`, a state at another site an earlier
  time (the site tables against the schedule);
* `S` increases with the ordinal.

The first two hold at every followed state of a thread, the state at the trace's end included,
when no site of a machine has an undefined-behaviour template (`Cross.SitesTmplOk`): the run then
continues after its last event (`state_facts`), and a fired event has its site's kind
(`kind_isWarpColl`, `kind_isTcColl`, `kind_isTmemOp`, `kind_bar`). `Sched.collSched_of` assembles
the schedule. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The kind of a fired event -/

/-- A named-barrier event. -/
def isBar (e : Event) : Bool :=
  match e.kind with
  | .bar .. => true
  | _ => false

/-- The kinds of the warp-collective `tcgen05` events. -/
def tcKind (k : NextKind) : Bool := k == .tmem || k == .tcLoad || k == .tcStore

/-- An event fired from a template of kind `k` is a warp collective, a warp-collective `tcgen05`
event, a paired Tensor Memory operation or a named-barrier event as `k` says. -/
theorem fires_kind {pc : Nat} {k : NextKind} {m : Tmpl} {e : Event} {o : Option TState}
    (hk : KindTmpl k m) (hf : Fires pc m e o) :
    Sched.isWarpColl e = (k == .warp) ∧ isTcColl e = tcKind k ∧
      Tmem.Pair.isTmemOp e = (k == .tmem) ∧ isBar e = (k == .bar) := by
  cases k <;> simp only [KindTmpl] at hk
  all_goals (try casesm* _ ∨ _, ∃ _, _, _ ∧ _)
  all_goals subst_vars
  all_goals simp only [Fires] at hf
  all_goals (try casesm* _ ∨ _, ∃ _, _, _ ∧ _)
  all_goals subst_vars
  all_goals simp [Sched.isWarpColl, isTcColl, Tmem.Pair.isTmemOp, isBar, tcKind]

/-! ### The schedule -/

/-- The role of a thread's state is its warp's. -/
theorem role_cases {g : Nat} {d : ThreadD} (hw : ∀ r, d = .inr r → r.kind.Warp (warpOf L g)) :
    (∃ p, d = .inl p) ∨
      (warpOf L g = 15 ∧ ∃ s, d = .inr (.idle s)) ∨
      (warpOf L g = 14 ∧ ∃ l, d = .inr (.loader l)) ∨
      (warpOf L g = 12 ∧ ∃ m, d = .inr (.mma m)) ∨
      (warpOf L g = 13 ∧ ∃ s, d = .inr (.store s)) ∨
      (warpOf L g < 8 ∧ ∃ s, d = .inr (.softmax s)) ∨
      (8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ ∃ c, d = .inr (.corr c)) := by
  rcases d with p | r
  · exact .inl ⟨p, rfl⟩
  · have h := hw r rfl
    cases r <;> simp only [Role.kind, RoleKind.Warp] at h
    · exact .inr (.inl ⟨h, _, rfl⟩)
    · exact .inr (.inr (.inl ⟨h, _, rfl⟩))
    · exact .inr (.inr (.inr (.inl ⟨h, _, rfl⟩)))
    · exact .inr (.inr (.inr (.inr (.inl ⟨h, _, rfl⟩))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨h, _, rfl⟩)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨h.1, h.2, _, rfl⟩)))))

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X) (hok : SitesTmplOk L)
include hpre hX ht hok

omit ht in
/-- **An event fired from a followed state has its site's kind.** -/
theorem fired_kind {g k : Nat} {d : ThreadD} {e : Event} (hg : g < L.threads)
    (hσ : St L X g k = some (some d)) (he : X.get (g, k) = some e) :
    Sched.isWarpColl e = (nextKind d == .warp) ∧ isTcColl e = tcKind (nextKind d) ∧
      Tmem.Pair.isTmemOp e = (nextKind d == .tmem) ∧ isBar e = (nextKind d == .bar) := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hC hX he hσ
  rcases tmpl_kind hat hc with ⟨f, hub⟩ | hk
  · exact absurd hub (hok g hg d t ins hat hinv hc f)
  · exact fires_kind hk hf

omit ht in
/-- An event of a thread fires from the state before it, which, when followed, is a state of the
run with the machine's invariant. -/
theorem last_step {g : Nat} {d : ThreadD} (hg : g < L.threads)
    (hσ : St L X g (X.tr g).length = some (some d)) (hl : 0 < (X.tr g).length)
    {d0 : ThreadD} (hσ0 : St L X g ((X.tr g).length - 1) = some (some d0)) :
    ∃ t ins u, (code L g).AtD d0 t ∧ (code L g).inv d0 ∧
      kernel.code[(code L g).pc d0]? = some ins ∧
      Fires ((code L g).pc d0) (eventTmpl asms L g t ins.op) (X.tr g)[(X.tr g).length - 1]
        (some u) ∧ (code L g).next d0 (X.tr g)[(X.tr g).length - 1] = some (some d) := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have hk : (X.tr g).length - 1 < (X.tr g).length := by omega
  have hget : X.get (g, (X.tr g).length - 1) = some (X.tr g)[(X.tr g).length - 1] :=
    List.getElem?_eq_getElem hk
  have hsucc := Frame.stateAt_succ (C := code L) (X := X) (g := g) (k := (X.tr g).length - 1)
    hget
  have hσ0' : Frame.stateAt (code L) X g ((X.tr g).length - 1) = some (some d0) := hσ0
  rw [Nat.sub_add_cancel hl, hσ0'] at hsucc
  change St L X g (X.tr g).length = (code L g).next d0 _ at hsucc
  rw [hσ] at hsucc
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hC hX hget hσ0
  cases o with
  | some u => exact ⟨t, ins, u, hat, hinv, hc, hf, hsucc.symm⟩
  | none =>
    exfalso
    rcases fires_none_ends hf with ⟨f, hk'⟩ | hk'
    · exact hok g hg d0 t ins hat hinv hc f (fires_ub hf hk')
    · have hget' : X.get (g, (X.tr g).length - 1) =
          some ⟨(X.tr g)[(X.tr g).length - 1].pc, .exit⟩ := by
        rw [hget, ← hk']
      rw [Lag.next_exit_pc (Lag.exit_pc hpre hX hget' hσ0)] at hsucc
      cases hsucc

/-- **A followed state of a thread**, before an event or at the trace's end, has the roles' run
invariant of the events before it, the machine's invariant and its warp's role. -/
theorem state_facts {g k : Nat} {d : ThreadD} (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hσ : St L X g k = some (some d)) :
    roleJ L g d ((X.tr g).take k) ∧ (code L g).inv d ∧
      ∀ r, d = .inr r → r.kind.Warp (warpOf L g) := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have htr := Frame.trace (C := code L) hC hX hg
  have hwarp : ∀ r, d = .inr r → r.kind.Warp (warpOf L g) := by
    intro r hr
    subst hr
    exact role_warp_run hpre hg htr k r hσ
  rcases Nat.lt_or_ge k (X.tr g).length with hlt | hge
  · have hget : X.get (g, k) = some (X.tr g)[k] := List.getElem?_eq_getElem hlt
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hC hX hget hσ
    exact ⟨RunInv.holds hpre hX hg (roleJ_run hpre hg) hlt hσ, hinv, hwarp⟩
  have hk' : k = (X.tr g).length := by omega
  subst hk'
  refine ⟨?_, ?_, hwarp⟩
  · rw [List.take_length]
    by_cases hl : (X.tr g).length = 0
    · have h0 : X.tr g = [] := List.length_eq_zero_iff.mp hl
      have hi : St L X g (X.tr g).length = some (some (code L g).init) := by
        rw [hl]; exact Frame.stateAt_zero
      rw [hσ] at hi
      cases hi
      rw [h0]
      exact (roleJ_run hpre hg).init
    · obtain ⟨d0, hσ0⟩ := Frame.stateAt_live (C := code L) ht hg hσ (Nat.sub_le _ 1)
      obtain ⟨t, ins, u, hat, hinv, hc, hf, hn⟩ := last_step hpre hX hok hg hσ (by omega) hσ0
      have hJ := RunInv.holds hpre hX hg (roleJ_run hpre hg) (by omega) hσ0
      have h := (roleJ_run hpre hg).step hJ hat hinv hc hf hn
      rwa [← List.take_succ_eq_append_getElem (by omega), Nat.sub_add_cancel (by omega),
        List.take_length] at h
  · obtain ⟨o, hr⟩ := hX.thr g hg
    cases o with
    | some u =>
      obtain ⟨t', -, -, hinv⟩ := Code.end_site (hC g hg) hr
        (by rw [← Frame.stateAt_end]; exact hσ)
      exact hinv
    | none =>
      exfalso
      obtain ⟨e, he, hk⟩ := Run.ended_last hr
      have hl : 0 < (X.tr g).length := by
        cases h : X.tr g with
        | nil => rw [h] at he; cases he
        | cons _ _ => simp
      have hge : (X.tr g)[(X.tr g).length - 1] = e := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at he
        exact Option.some.inj he
      obtain ⟨d0, hσ0⟩ := Frame.stateAt_live (C := code L) ht hg hσ (Nat.sub_le _ 1)
      obtain ⟨t, ins, u, -, -, -, hf, -⟩ := last_step hpre hX hok hg hσ hl hσ0
      rw [hge] at hf
      cases fires_end_none hf hk

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
