-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedule
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsBar2
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base

@[expose] public section

/-! # Producer lag: from a state bound to `Lags`

A producer `y` lags a waiter `g` (`Lags`) when it has not exited and its current time is earlier
than the waiter's state. Both follow from one bound on the producer's states: every state with
the producer's run invariant (`roleJ`), its machine's invariant and fewer than `N` producing
events before it is no later than `B` and is not at the exit (`lags_of`). The exit is fired from
a state at the exit's position, with the producing events before it; the current time is the
time of the state at the trace's end, or one more than that of the state before the last event
when the machine stopped there.

The state at the trace's end has the run invariant and the machine's invariant (`end_state`) when
the execution has no undefined behaviour: the thread's run then continues after its last event
(an exit leaves no state: every role stops at its exit, `next_exit_pc`), so the last event was
fired from a followed state and the run ends at a concrete state of the end state.

Without that premise the bound does not reach the end state: a correction thread whose credit
arrival is undefined behaviour ends its run there, and its machine, which moves past a credit
site on any event, is at the next site (`afterTrip`), later than the softmax poll waiting for
that credit. `Lags` therefore assumes `¬ HasUb X`; `lags_of` proves its conclusion
(`LagsOk`) under it. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Lag

/-- The conclusion of `Lags` in an execution without undefined behaviour. -/
abbrev LagsOk (L : Launch) (X : Execution) (y g : Nat) (d : ThreadD) : Prop :=
  (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧ endTime L X y < stateTime L g d

/-- **Every machine stops at its exit**: a state at the exit's position has no successor. -/
theorem next_exit_pc {g : Nat} {d : ThreadD} {e : Event} (h : (code L g).pc d = Flow.exit_0) :
    (code L g).next d e = none := by
  rcases d with p | r
  · exact absurd h (Prologue.site_ne_exit p.site)
  · cases r with
    | idle s =>
      obtain ⟨site⟩ := s
      cases site
      · exfalso
        change Idle.Site.pc .setMaxReg = Flow.exit_0 at h
        revert h; site_decide
      · rfl
    | loader l =>
      have hs := Loader.site_exit l.site h
      cases l; simp only at hs; subst hs; rfl
    | mma m =>
      have hs := Mma.site_exit m.site h
      cases m; simp only at hs; subst hs; rfl
    | store s =>
      have hs := Facts.store_site_ret s.site (List.mem_singleton.mpr h)
      cases s; simp only at hs; subst hs; rfl
    | softmax s =>
      have hs := Facts.soft_site_ret s.site (List.mem_singleton.mpr h)
      cases s; simp only at hs; subst hs; rfl
    | corr c =>
      have hs := Facts.corr_site_ret c.site (List.mem_singleton.mpr h)
      cases c; simp only at hs; subst hs; rfl

theorem fin6_cases (x : Fin 6) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
  fin_cases x <;> simp

/-- A count of `m` per item plus a position is below another such count, whose position is at
most `m`, when its item is earlier, or the same with an earlier position. -/
theorem mul_add_lt {m a b x y : Nat} (hy : y ≤ m) (h : m * a + x < m * b + y) :
    a < b ∨ a = b ∧ x < y := by
  rcases Nat.lt_trichotomy a b with h1 | rfl | h1
  · exact .inl h1
  · exact .inr ⟨rfl, by omega⟩
  · exfalso
    have : m * (b + 1) ≤ m * a := Nat.mul_le_mul_left _ h1
    rw [Nat.mul_succ] at this
    omega

/-! ### The order of the slot times -/

open Progress in
/-- A time in an earlier item, an earlier slot, or at an offset no later is no later. -/
theorem slotTime_le {n i s o i' s' o' : Nat} (hs : s ≤ n) (ho : o < Time.span)
    (h : i < i' ∨ i = i' ∧ (s < s' ∨ s = s' ∧ o ≤ o')) :
    Time.slotTime n i s o ≤ Time.slotTime n i' s' o' := by
  unfold Time.slotTime Time.gslot
  rcases h with h | ⟨rfl, h⟩
  · have h1 : (i + 1) * (n + 1) ≤ i' * (n + 1) := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at h1
    have h2 : Time.span * (i * (n + 1) + s + 1) ≤ Time.span * (i' * (n + 1) + s') :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at h2
    omega
  · simp only [Time.span] at ho ⊢
    omega

open Progress in
/-- One more than a time in an earlier item, an earlier slot, or at an earlier offset is no
later. -/
theorem slotTime_succ_le {n i s o i' s' o' : Nat} (hs : s ≤ n) (ho : o + 1 < Time.span)
    (h : i < i' ∨ i = i' ∧ (s < s' ∨ s = s' ∧ o + 1 ≤ o')) :
    Time.slotTime n i s o + 1 ≤ Time.slotTime n i' s' o' :=
  slotTime_le (o := o + 1) hs ho h

open Progress in
theorem slotTime_add (n i s o k : Nat) :
    Time.slotTime n i s (o + k) = Time.slotTime n i s o + k := by
  unfold Time.slotTime; omega

open Progress in
/-- One more than a time is earlier than a time in a later item, a later slot, or at least two
offsets later. -/
theorem slotTime_lt {n i s o i' s' o' : Nat} (hs : s ≤ n) (ho : o + 2 < Time.span)
    (h : i < i' ∨ i = i' ∧ (s < s' ∨ s = s' ∧ o + 2 ≤ o')) :
    Time.slotTime n i s o + 1 < Time.slotTime n i' s' o' := by
  have := slotTime_le (o := o + 2) hs ho h
  rw [slotTime_add] at this
  omega

open Progress in
theorem le_slotTime_of {x n i s o : Nat} (h : x ≤ Time.base + o) : x ≤ Time.slotTime n i s o := by
  unfold Time.slotTime; omega

open Progress in
/-- Every fixed time is before every slot. -/
theorem fixed_le_slotTime {x n i s o : Nat} (h : x ≤ Time.base) : x ≤ Time.slotTime n i s o := by
  unfold Time.slotTime; omega

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

omit ht in
/-- An exit event fires from a state at the exit's position. -/
theorem exit_pc {g k pc : Nat} {d : ThreadD} (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (hσ : St L X g k = some (some d)) : (code L g).pc d = Flow.exit_0 := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ :=
    Frame.fired_site (C := code L) (fun _ hg => sound hpre hg) hX he hσ
  have hret : retOp ins.op = true := retOp_of_fires hf rfl
  exact List.mem_singleton.mp (OpPcsFast.mem kernel_ret_pcs hc hret)

/-- **The state at the trace's end** of a thread of an execution without undefined behaviour has
the roles' run invariant and the machine's invariant. -/
theorem end_state (hub : ¬ HasUb X) {g : Nat} {d : ThreadD} (hg : g < L.threads)
    (hσ : St L X g (X.tr g).length = some (some d)) :
    roleJ L g d (X.tr g) ∧ (code L g).inv d := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  -- the last event, if any, continues the run
  have hlast : ∀ (hl : 0 < (X.tr g).length), ∃ d0 t ins u,
      St L X g ((X.tr g).length - 1) = some (some d0) ∧ (code L g).AtD d0 t ∧
      (code L g).inv d0 ∧ kernel.code[(code L g).pc d0]? = some ins ∧
      Fires ((code L g).pc d0) (eventTmpl asms L g t ins.op) (X.tr g)[(X.tr g).length - 1]
        (some u) ∧ (code L g).next d0 (X.tr g)[(X.tr g).length - 1] = some (some d) := by
    intro hl
    have hk : (X.tr g).length - 1 < (X.tr g).length := by omega
    have hget : X.get (g, (X.tr g).length - 1) = some (X.tr g)[(X.tr g).length - 1] :=
      List.getElem?_eq_getElem hk
    obtain ⟨d0, hσ0⟩ := Frame.stateAt_live (C := code L) ht hg hσ (Nat.sub_le _ 1)
    have hsucc := Frame.stateAt_succ (C := code L) (X := X) (g := g) (k := (X.tr g).length - 1)
      hget
    rw [Nat.sub_add_cancel hl, hσ0] at hsucc
    change St L X g (X.tr g).length = (code L g).next d0 _ at hsucc
    rw [hσ] at hsucc
    obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hC hX hget hσ0
    cases o with
    | some u => exact ⟨d0, t, ins, u, hσ0, hat, hinv, hc, hf, hsucc.symm⟩
    | none =>
      exfalso
      rcases fires_none_ends hf with ⟨f, hk'⟩ | hk'
      · apply hub
        refine ⟨(g, (X.tr g).length - 1), (X.tr g)[(X.tr g).length - 1].pc, f, ?_⟩
        rw [hget, ← hk']
      · have hget' : X.get (g, (X.tr g).length - 1) =
            some ⟨(X.tr g)[(X.tr g).length - 1].pc, .exit⟩ := by rw [hget, ← hk']
        rw [next_exit_pc (exit_pc hpre hX hget' hσ0)] at hsucc
        cases hsucc
  refine ⟨?_, ?_⟩
  · by_cases hl : (X.tr g).length = 0
    · have h0 : X.tr g = [] := List.length_eq_zero_iff.mp hl
      have hi : St L X g (X.tr g).length = some (some (code L g).init) := by
        rw [hl]; exact Frame.stateAt_zero
      rw [hσ] at hi
      cases hi
      rw [h0]
      exact (roleJ_run hpre hg).init
    · obtain ⟨d0, t, ins, u, hσ0, hat, hinv, hc, hf, hn⟩ := hlast (by omega)
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
      have hget : X.get (g, (X.tr g).length - 1) = some e := by
        rw [← hge]; exact List.getElem?_eq_getElem (Nat.sub_lt hl Nat.one_pos)
      obtain ⟨d0, t, ins, u, hσ0, -, -, -, -, hn⟩ := hlast hl
      rw [hge] at hn
      obtain ⟨pc, k⟩ := e
      rcases hk with ⟨f, hk⟩ | hk <;> simp only at hk <;> subst hk
      · exact hub ⟨_, pc, f, hget⟩
      · rw [next_exit_pc (exit_pc hpre hX hget hσ0)] at hn
        cases hn

/-- **Lag from a bound on the producer's states.** A producer `y` of an execution without
undefined behaviour with fewer than `N` events `p` lags `g` at `dg` when every state of `y`'s
machine (with the roles' run invariant, the machine's invariant and its warp's role) with fewer
than `N` events `p` before it is no later than `B`, below `stateTime L g dg - 1`, and not at the
exit's position. -/
theorem lags_of (hub : ¬ HasUb X) {y g : Nat} {dg : ThreadD} (hy : y < L.threads)
    (p : Event → Bool) (N B : Nat)
    (hb : ∀ d es, (∃ k, es = (X.tr y).take k) → roleJ L y d es → (code L y).inv d →
      (∀ r, d = .inr r → r.kind.Warp (warpOf L y)) → es.countP p < N →
        stateTime L y d ≤ B ∧ (code L y).pc d ≠ Flow.exit_0)
    (hlt : (X.tr y).countP p < N) (hB : B + 1 < stateTime L g dg) :
    LagsOk L X y g dg := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have htr := Frame.trace (C := code L) hC hX hy
  have hwarp : ∀ k d, St L X y k = some (some d) →
      ∀ r, d = .inr r → r.kind.Warp (warpOf L y) := by
    intro k d hσ r hr
    subst hr
    exact role_warp_run hpre hy htr k r hσ
  have hpre_le : ∀ k, ((X.tr y).take k).countP p ≤ (X.tr y).countP p :=
    fun k => (List.take_sublist _ _).countP_le
  -- a state before an event
  have hbefore : ∀ k d, k < (X.tr y).length → St L X y k = some (some d) →
      stateTime L y d ≤ B ∧ (code L y).pc d ≠ Flow.exit_0 := by
    intro k d hk hσ
    have hget : X.get (y, k) = some (X.tr y)[k] := List.getElem?_eq_getElem hk
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hC hX hget hσ
    exact hb d _ ⟨k, rfl⟩ (RunInv.holds hpre hX hy (roleJ_run hpre hy) hk hσ) hinv (hwarp k d hσ)
      (lt_of_le_of_lt (hpre_le k) hlt)
  refine ⟨fun k pc he => ?_, ?_⟩
  · obtain ⟨d, hσ⟩ := Frame.event_state hC hX ht he (fun _ _ h => by cases h)
    have hk : k < (X.tr y).length := (List.getElem?_eq_some_iff.mp he).1
    exact (hbefore k d hk hσ).2 (exit_pc hpre hX he hσ)
  · unfold Sched.threadTime; dsimp only [timed]
    split
    · rename_i d hσ
      obtain ⟨hJ, hinv⟩ := end_state hpre hX ht hub hy hσ
      have := (hb d _ ⟨_, List.take_length.symm⟩ hJ hinv (hwarp _ d hσ) hlt).1
      omega
    · omega
    · rename_i hσ
      split
      · rename_i d0 hσ0
        have hl : 0 < (X.tr y).length := by
          by_contra h0
          have h1 : Frame.stateAt (code L) X y (X.tr y).length = some (some (code L y).init) := by
            rw [show (X.tr y).length = 0 by omega]; exact Frame.stateAt_zero
          rw [h1] at hσ
          cases hσ
        have := (hbefore _ d0 (by omega) hσ0).1
        omega
      · omega

/-! ### Per producer role -/

omit hpre hX ht in
open Progress in
/-- A prologue state is before every bound at or above the slots' start, and not at the
exit. -/
theorem prologue_bound {y B : Nat} (p : Prologue.D) (hB : Time.base ≤ B) :
    stateTime L y (.inl p) ≤ B ∧ (code L y).pc (.inl p) ≠ Flow.exit_0 := by
  refine ⟨le_trans ?_ hB, Prologue.site_ne_exit p.site⟩
  show Time.prologue p.site ≤ Time.base
  cases p.site with
  | elect e =>
    have := (Prologue.groupStart e).isLt
    have := e.isLt
    simp only [Time.prologue, Time.base]
    split_ifs <;> omega
  | init j =>
    have := (Prologue.groupOf j).isLt
    have := j.isLt
    simp only [Time.prologue, Time.base]
    split_ifs <;> omega
  | _ => simp [Time.prologue, Time.base, Time.clArriveT, Time.clWaitT]

open Progress in
/-- **Lag of a correction thread**, from a bound on its states. -/
theorem lags_corr (hub : ¬ HasUb X) {y g : Nat} {dg : ThreadD} (hy : y < L.threads)
    (hw : 8 ≤ warpOf L y ∧ warpOf L y < 12) (p : Event → Bool) (N B : Nat) (hB0 : Time.base ≤ B)
    (hb : ∀ c es, (∃ k, es = (X.tr y).take k) →
      Correction.Counts L y c es → Correction.Inv L y c → es.countP p < N →
      Time.correction (Work.n L) (Work.T L y) c ≤ B ∧ c.site ≠ .exit)
    (hlt : (X.tr y).countP p < N) (hB : B + 1 < stateTime L g dg) :
    LagsOk L X y g dg := by
  refine lags_of hpre hX ht hub hy p N B (fun d es hk0 hJ hinv hk hc => ?_) hlt hB
  rcases d with q | r
  · exact prologue_bound q hB0
  · have hk' := hk r rfl
    cases r with
    | corr c =>
      obtain ⟨h1, h2⟩ := hb c es hk0 hJ hinv hc
      exact ⟨h1, fun h => h2 (Facts.corr_site_ret c.site (List.mem_singleton.mpr h))⟩
    | _ => simp only [Role.kind, RoleKind.Warp] at hk'; omega

open Progress in
/-- **Lag of a store thread**, from a bound on its states. -/
theorem lags_store (hub : ¬ HasUb X) {y g : Nat} {dg : ThreadD} (hy : y < L.threads)
    (hw : warpOf L y = 13) (p : Event → Bool) (N B : Nat) (hB0 : Time.base ≤ B)
    (hb : ∀ c es, (∃ k, es = (X.tr y).take k) →
      Store.Counts L y c es → (c.site = .setMaxReg ∨ Store.Inv L y c) →
      es.countP p < N → Time.store (Work.n L) (Work.T L y) c ≤ B ∧ c.site ≠ .exit)
    (hlt : (X.tr y).countP p < N) (hB : B + 1 < stateTime L g dg) :
    LagsOk L X y g dg := by
  refine lags_of hpre hX ht hub hy p N B (fun d es hk0 hJ hinv hk hc => ?_) hlt hB
  rcases d with q | r
  · exact prologue_bound q hB0
  · have hk' := hk r rfl
    cases r with
    | store c =>
      obtain ⟨h1, h2⟩ := hb c es hk0 hJ hinv hc
      exact ⟨h1, fun h => h2 (Facts.store_site_ret c.site (List.mem_singleton.mpr h))⟩
    | _ => simp only [Role.kind, RoleKind.Warp] at hk'; omega

open Progress in
/-- **Lag of a softmax thread**, from a bound on its states. -/
theorem lags_soft (hub : ¬ HasUb X) {y g : Nat} {dg : ThreadD} (hy : y < L.threads)
    (hw : warpOf L y < 8) (p : Event → Bool) (N B : Nat) (hB0 : Time.base ≤ B)
    (hb : ∀ c es, (∃ k, es = (X.tr y).take k) →
      Softmax.Counts L y c es → Softmax.Inv L y c → es.countP p < N →
      Time.softmax (Work.n L) (Work.T L y) (Softmax.stOf L y) c ≤ B ∧ c.site ≠ .exit)
    (hlt : (X.tr y).countP p < N) (hB : B + 1 < stateTime L g dg) :
    LagsOk L X y g dg := by
  refine lags_of hpre hX ht hub hy p N B (fun d es hk0 hJ hinv hk hc => ?_) hlt hB
  rcases d with q | r
  · exact prologue_bound q hB0
  · have hk' := hk r rfl
    cases r with
    | softmax c =>
      obtain ⟨h1, h2⟩ := hb c es hk0 hJ hinv hc
      exact ⟨h1, fun h => h2 (Facts.soft_site_ret c.site (List.mem_singleton.mpr h))⟩
    | _ => simp only [Role.kind, RoleKind.Warp] at hk'; omega

open Progress in
/-- **Lag of an MMA thread**, from a bound on its states. -/
theorem lags_mma (hub : ¬ HasUb X) {y g : Nat} {dg : ThreadD} (hy : y < L.threads)
    (hw : warpOf L y = 12) (p : Event → Bool) (N B : Nat) (hB0 : Time.base ≤ B)
    (hb : ∀ c es, (∃ k, es = (X.tr y).take k) →
      Mma.Counts L y c es → Mma.Inv L y c → es.countP p < N →
      Time.mma (Work.n L) (Work.T L y) c ≤ B ∧ c.site ≠ .exit)
    (hlt : (X.tr y).countP p < N) (hB : B + 1 < stateTime L g dg) :
    LagsOk L X y g dg := by
  refine lags_of hpre hX ht hub hy p N B (fun d es hk0 hJ hinv hk hc => ?_) hlt hB
  rcases d with q | r
  · exact prologue_bound q hB0
  · have hk' := hk r rfl
    cases r with
    | mma c =>
      obtain ⟨h1, h2⟩ := hb c es hk0 hJ hinv.1 hc
      exact ⟨h1, fun h => h2 (Mma.site_exit c.site h)⟩
    | _ => simp only [Role.kind, RoleKind.Warp] at hk'; omega

open Progress in
/-- **Lag of a loader thread**, from a bound on its states. -/
theorem lags_loader (hub : ¬ HasUb X) {y g : Nat} {dg : ThreadD} (hy : y < L.threads)
    (hw : warpOf L y = 14) (p : Event → Bool) (N B : Nat) (hB0 : Time.base ≤ B)
    (hb : ∀ c es, (∃ k, es = (X.tr y).take k) →
      Loader.Counts L y c es → Loader.Inv L y c → es.countP p < N →
      Time.loader (Work.n L) (Work.T L y) c ≤ B ∧ c.site ≠ .exit)
    (hlt : (X.tr y).countP p < N) (hB : B + 1 < stateTime L g dg) :
    LagsOk L X y g dg := by
  refine lags_of hpre hX ht hub hy p N B (fun d es hk0 hJ hinv hk hc => ?_) hlt hB
  rcases d with q | r
  · exact prologue_bound q hB0
  · have hk' := hk r rfl
    cases r with
    | loader c =>
      obtain ⟨h1, h2⟩ := hb c es hk0 hJ hinv hc
      exact ⟨h1, fun h => h2 (Loader.site_exit c.site h)⟩
    | _ => simp only [Role.kind, RoleKind.Warp] at hk'; omega

end Lag
end
end PTX.Kernels.FlashAttn4Fwd.Proof
