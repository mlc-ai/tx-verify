-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RdMmaRun
public import Kernels.InklingRelDecode.Proof.Protocol.RingLoaderExec
public import Kernels.InklingRelDecode.Proof.Interface.Lk2Bar0
public import Kernels.InklingRelDecode.Proof.Interface.RrArrive

@[expose] public section

/-!
# The loader warp's run, from the thread's states

The loader's counts (`Ring.loader_arrive_exec`, `loader_copy_exec`, `loader_poll_exec`) are
stated on an anchored run: an event `k₀` at which the thread is at the loader's `bar0`, the states
from `k₀` to the event inside the loop (`hin`), and no ring event before `k₀` (`hfresh`). Here the
anchor is derived from the thread's states `St Q L X g k`, as `Rd.mma_anchor` does for the MMA
warp:

* `loader_state_pred_adj`: the state before a loader state other than the role's first is a loader
  state with the same inherited registers, at the previous event;
* `loader_back`: a loader state at an event has an entry state (`setMaxDec`) at an earlier or the
  same event, every state between being the role's;
* `loader_entry_unique`: a thread has one entry state of the loader role (the register-request
  count `rqN`, `phase_inv`, from the role byte protocol `RoleReads`);
* `loader_bar0_back`, `loader_anchor`: a loader state in the loop has the state `bar0` of its run
  at an earlier event, and the window between is in the loop;
* `loader_fresh`: no event of the thread before that `bar0` is an arrival, a copy or a poll of a
  ring barrier.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Predecessors -/

/-- **A loader successor of the composed worker machine** other than the role's first state is the
loader machine's successor of a loader state with the same inherited registers. -/
theorem wcomp_next_loader {s0 : WComp.WSt} {e : Event} {d : Loader.D} {P : Loader.Pro}
    (h : WComp.next L g s0 e = some (some (.loader d P))) (hs : d.site ≠ .setMaxDec) :
    ∃ d0, s0 = .loader d0 P ∧ Loader.next L g d0 e = some (some d) := by
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
          | (simp only [Option.some.injEq, WComp.WSt.loader.injEq] at h
             obtain ⟨rfl, -⟩ := h
             exact hs rfl)
          | (split at h <;> simp at h; done)
          | ((repeat' split at h) <;> simp at h)
      · simp at h
      · simp at h
  | idle d0 =>
    exfalso
    simp only [WComp.next] at h
    split at h
    · simp at h
    · simp at h
  | mma d0 P0 =>
    exfalso
    simp only [WComp.next] at h
    split at h
    · simp at h
    · simp at h
  | loader d0 P0 =>
    simp only [WComp.next] at h
    split at h
    · simp at h
    · cases hn : Loader.next L g d0 e with
      | none => simp [hn] at h
      | some o =>
        cases o with
        | none => simp [hn] at h
        | some d1 =>
          simp only [hn, Option.map_some, Option.some.injEq, WComp.WSt.loader.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨d0, rfl, hn⟩
  | exit x =>
    exfalso
    simp only [WComp.next] at h
    split at h
    · simp at h
    · cases h

theorem loader_ne_init (d : Loader.D) (P : Loader.Pro) :
    TSt.w (.loader d P) ≠ (code L Q g).init := by
  show _ ≠ (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
    else TSt.w (WComp.code L g Q).init)
  split <;> simp

/-- **The state before a loader state, with adjacency.** -/
theorem loader_state_pred_adj (hX : Consistent L kernel asms mem0 X) {k : Nat} {d : Loader.D}
    {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hs : d.site ≠ .setMaxDec) :
    ∃ (k0 : Nat) (e : Event) (d0 : Loader.D), k0 + 1 = k ∧ g < L.threads ∧
      X.get (g, k0) = some e ∧ St Q L X g k0 = some (some (.w (.loader d0 P))) ∧
      Loader.next L g d0 e = some (some d) := by
  have hk1 : k ≠ 0 := by
    rintro rfl
    have h0 := hσ
    rw [St, Frame.stateAt_zero] at h0
    exact loader_ne_init d P (Option.some.inj (Option.some.inj h0)).symm
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k0]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hs' := hσ
  rw [St, Frame.stateAt_succ he] at hs'
  cases hk0 : St Q L X g k0 with
  | none => simp [St] at hk0 hs'; simp [hk0] at hs'
  | some σ =>
    cases σ with
    | none =>
      have : Frame.stateAt (code L Q) X g k0 = some none := hk0
      rw [this] at hs'
      simp [Code.toMachine] at hs'
    | some s0 =>
      have : Frame.stateAt (code L Q) X g k0 = some (some s0) := hk0
      rw [this] at hs'
      have hn : (threadCode L g Q).next s0 e = some (some (.w (.loader d P))) := hs'
      cases s0 with
      | d s =>
        rw [next_d] at hn
        obtain ⟨a, -, h⟩ := map_map_eq_some_some hn
        cases h
      | w s =>
        rw [next_w] at hn
        obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
        cases h
        obtain ⟨d0, rfl, hd0⟩ := wcomp_next_loader ha hs
        have hge : X.get (g, k0) = some e := he
        exact ⟨k0, e, d0, rfl, Frame.lt_of_get hX hge, hge, hk0, hd0⟩

/-- **The loader's invariant at a state with an event**, with the facts of the composed state. -/
theorem loader_inv_at (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {k : Nat} {d : Loader.D} {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) :
    Loader.Inv L g d ∧ 4 ≤ WComp.warpOf L g ∧ g % L.block < 256 := by
  obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
  have h : Loader.Inv L g d ∧ Loader.ProEq L g P d ∧ Worker.Rest L g P ∧
      4 ≤ WComp.warpOf L g ∧ g % L.block < 256 := hinv.2
  exact ⟨h.1, h.2.2.2⟩

/-- A step of the loader machine is not a step into `setMaxDec`, and not out of `setMaxInc`. -/
theorem next_ne_setMaxDec {d0 d : Loader.D} {e : Event}
    (hn : Loader.next L g d0 e = some (some d)) :
    d.site ≠ .setMaxDec ∧ d0.site ≠ .setMaxInc := by
  constructor
  · unfold Loader.next Loader.afterIter Loader.readI Loader.readN at hn
    repeat' split at hn
    all_goals first
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
      | (simp only [Option.some.injEq] at hn; subst hn; (try split) <;> simp_all)
  · intro h
    simp [Loader.next, h] at hn

/-- **The role byte protocol makes the entry of the loader role unique.** -/
theorem loader_entry_unique (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {k1 k2 : Nat} {d1 d2 : Loader.D}
    {P1 P2 : Loader.Pro} (hk1 : k1 < (X.tr g).length) (hk2 : k2 < (X.tr g).length)
    (h1 : St Q L X g k1 = some (some (.w (.loader d1 P1)))) (s1 : d1.site = .setMaxDec)
    (h2 : St Q L X g k2 = some (some (.w (.loader d2 P2)))) (s2 : d2.site = .setMaxDec) :
    k1 = k2 := by
  have key : ∀ {k1 k2 : Nat} {d1 d2 : Loader.D} {P1 P2 : Loader.Pro},
      k1 < (X.tr g).length → k2 < (X.tr g).length → k1 < k2 →
      St Q L X g k1 = some (some (.w (.loader d1 P1))) → d1.site = .setMaxDec →
      St Q L X g k2 = some (some (.w (.loader d2 P2))) → d2.site = .setMaxDec → False := by
    intro k1 k2 d1 d2 P1 P2 hk1 hk2 hlt h1 s1 h2 s2
    obtain ⟨-, t1, hr1, -, -, hkk1, -, -⟩ := phase_inv hpre hX hf.sound hR k1 _ (by omega) h1
    obtain ⟨-, t2, hr2, -, -, hkk2, -, -⟩ := phase_inv hpre hX hf.sound hR k2 _ (by omega) h2
    have t1z : t1 = 0 := hkk1 (by simp [tKind, wKind])
    have t2z : t2 = 0 := hkk2 (by simp [tKind, wKind])
    subst t1z t2z
    have p1 : (tPh (.w (.loader d1 P1))).1 = 1 := by simp [tPh, wPh, s1]
    have p2 : (tPh (.w (.loader d2 P2))).1 = 1 := by simp [tPh, wPh, s2]
    rw [p1] at hr1
    rw [p2] at hr2
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k1) = some e := ⟨_, List.getElem?_eq_getElem hk1⟩
    obtain ⟨hreq, -⟩ := event_req hX hf.sound he h1
    have hq : (tReq (.w (.loader d1 P1))).isSome = true := by
      simp [tReq, wReqS, loaderReq, s1]
    have hrq := hreq.mpr hq
    have he' : (X.tr g)[k1]? = some e := he
    have h3 : rqN X g (k1 + 1) = rqN X g k1 + 1 := by
      unfold rqN
      rw [List.take_add_one, he', Option.toList_some, List.countP_append]
      simp [hrq]
    have h4 : rqN X g (k1 + 1) ≤ rqN X g k2 := by
      unfold rqN
      exact (List.take_sublist_take_left (by omega)).countP_le
    omega
  rcases lt_trichotomy k1 k2 with h | h | h
  · exact (key hk1 hk2 h h1 s1 h2 s2).elim
  · exact h
  · exact (key hk2 hk1 h h2 s2 h1 s1).elim

/-! ### The loop's anchor -/

/-- The sites of the role before its loop: the register request and the vector load. -/
def PreSite (s : Loader.Site) : Prop := s = .setMaxDec ∨ s = .ld0 ∨ s = .ld1

/-- The steps of the role before its loop are a chain: `setMaxDec`, `ld0`, `ld1`, `bar0`. -/
theorem next_pre {d0 d : Loader.D} {e : Event} (hn : Loader.next L g d0 e = some (some d)) :
    (d.site = .ld0 → d0.site = .setMaxDec) ∧ (d.site = .ld1 → d0.site = .ld0) ∧
      (d.site = .bar0 → d0.site = .ld1 ∧ d.i = d0.i) ∧
      (d0.site = .setMaxDec → d.site = .ld0) ∧ (d0.site = .ld0 → d.site = .ld1) ∧
      (d0.site = .ld1 → d.site = .bar0) := by
  unfold Loader.next Loader.afterIter Loader.readI Loader.readN at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; (try split) <;> simp_all)

/-- **Backward from a loader state in the loop to the loop's anchor `bar0`.** Every state from the
anchor to the state is in the loop and not at the role's last site. -/
theorem loader_bar0_back (hX : Consistent L kernel asms mem0 X) (hrg : LdRng Q L X) :
    ∀ (k : Nat) {d : Loader.D} {P : Loader.Pro}, k < (X.tr g).length →
      St Q L X g k = some (some (.w (.loader d P))) → ¬ PreSite d.site →
      ∃ (k0 : Nat) (d0 : Loader.D), k0 ≤ k ∧ St Q L X g k0 = some (some (.w (.loader d0 P))) ∧
        d0.site = .bar0 ∧
        ∀ j, k0 ≤ j → j < k → ∃ dj, St Q L X g j = some (some (.w (.loader dj P))) ∧
          Ring.Ld.InLoop dj ∧ dj.site ≠ .setMaxInc := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d P hk hσ hp
    by_cases hs : d.site = .bar0
    · exact ⟨k, d, le_refl _, hσ, hs, fun j h1 h2 => by omega⟩
    · have hs0 : d.site ≠ .setMaxDec := fun h => hp (.inl h)
      obtain ⟨k0, e, d0, hadj, hg0, he, hσ0, hn⟩ := loader_state_pred_adj hX hk hσ hs0
      obtain ⟨-, -, -, h4, h5, h6⟩ := next_pre hn
      have hp0 : ¬ PreSite d0.site := by
        rintro (h | h | h)
        · exact hp (.inr (.inl (h4 h)))
        · exact hp (.inr (.inr (h5 h)))
        · exact hs (h6 h)
      obtain ⟨k1, d1, hk1, hσ1, hs1, hch⟩ := ih k0 (by omega) (by omega) hσ0 hp0
      refine ⟨k1, d1, by omega, hσ1, hs1, fun j hj1 hj2 => ?_⟩
      by_cases hjk : j = k0
      · subst hjk
        have hg : g < L.threads := Frame.lt_of_get hX (List.getElem?_eq_getElem hk)
        refine ⟨d0, hσ0, ⟨fun h => hp0 (.inl h), fun h => hp0 (.inr (.inl h)),
          fun h => hp0 (.inr (.inr h)), hrg hg hσ0⟩, (next_ne_setMaxDec hn).2⟩
      · exact hch j hj1 (by omega)

/-- **The anchor of a loader thread is unique**: two states at `bar0` are at one event. -/
theorem loader_bar0_unique (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {k1 k2 : Nat} {d1 d2 : Loader.D}
    {P1 P2 : Loader.Pro} (hk1 : k1 < (X.tr g).length) (hk2 : k2 < (X.tr g).length)
    (h1 : St Q L X g k1 = some (some (.w (.loader d1 P1)))) (s1 : d1.site = .bar0)
    (h2 : St Q L X g k2 = some (some (.w (.loader d2 P2)))) (s2 : d2.site = .bar0) :
    k1 = k2 := by
  have entry : ∀ {k : Nat} {d : Loader.D} {P : Loader.Pro}, k < (X.tr g).length →
      St Q L X g k = some (some (.w (.loader d P))) → d.site = .bar0 →
      ∃ k0 d0, k0 + 3 = k ∧ St Q L X g k0 = some (some (.w (.loader d0 P))) ∧
        d0.site = .setMaxDec := by
    intro k d P hk hσ hs
    obtain ⟨ka, _, da, ha, -, -, hσa, hna⟩ :=
      loader_state_pred_adj hX hk hσ (by rw [hs]; nofun)
    have hsa := ((next_pre hna).2.2.1 hs).1
    obtain ⟨kb, _, db, hb, -, -, hσb, hnb⟩ :=
      loader_state_pred_adj hX (by omega) hσa (by rw [hsa]; nofun)
    have hsb := (next_pre hnb).2.1 hsa
    obtain ⟨kc, _, dc, hc, -, -, hσc, hnc⟩ :=
      loader_state_pred_adj hX (by omega) hσb (by rw [hsb]; nofun)
    exact ⟨kc, dc, by omega, hσc, (next_pre hnc).1 hsb⟩
  obtain ⟨a1, e1, ha1, hσ1, hs1⟩ := entry hk1 h1 s1
  obtain ⟨a2, e2, ha2, hσ2, hs2⟩ := entry hk2 h2 s2
  have := loader_entry_unique hpre hX hf hR (by omega) (by omega) hσ1 hs1 hσ2 hs2
  omega

/-- A worker thread has no default-partition state with an event. -/
theorem not_d_of_w (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {k j : Nat} {s : WComp.WSt} {s' : DComp.St} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w s))) (hj : j < (X.tr g).length)
    (hσ' : St Q L X g j = some (some (.d s'))) : False := by
  obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨e', he'⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
  obtain ⟨t', ins', o', -, hinv', -, -⟩ := Frame.fired_site hf.sound hX he' hσ'
  have h1 : ¬ IsDefault L g := hinv.1
  have h2 : IsDefault L g := hinv'.1
  exact h1 h2

/-- **No ring event of a loader thread before its anchor.** An event of the thread before its
loop's `bar0` is no arrival, no tensor copy and no poll. -/
theorem loader_fresh_ev (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {k0 : Nat} {d0 : Loader.D}
    {P0 : Loader.Pro} (hk0 : k0 < (X.tr g).length)
    (h0 : St Q L X g k0 = some (some (.w (.loader d0 P0)))) (hs0 : d0.site = .bar0)
    {j : Nat} {e : Event} (hj : j < k0) (he : X.get (g, j) = some e) :
    (∀ l tx c rel sc, e.kind ≠ .arrive l tx c rel sc) ∧
      (∀ a sp, e.kind ≠ .tensorIssue a sp) ∧ (∀ l p ok acq sc, e.kind ≠ .wait l p ok acq sc) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hjl : j < (X.tr g).length := by omega
  -- a loader state at `j` in the loop has its anchor at or before `j`
  have late : ∀ {d : Loader.D} {P : Loader.Pro},
      St Q L X g j = some (some (.w (.loader d P))) → ¬ PreSite d.site → False := by
    intro d P hσ hp
    obtain ⟨k1, d1, hk1, hσ1, hs1, -⟩ := loader_bar0_back hX hf.ldRng j hjl hσ hp
    have := loader_bar0_unique hpre hX hf hR (by omega) hk0 hσ1 hs1 h0 hs0
    omega
  refine ⟨fun l tx c rel sc hk => ?_, fun a sp hk => ?_, fun l p ok acq sc hk => ?_⟩
  · rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he
      ⟨l, tx, c, rel, sc, hk⟩ with
      ⟨d, hσ, -⟩ | ⟨d, hσ, -⟩ | ⟨d, P, hσ, hs, -⟩
    · exact not_d_of_w hX hf hk0 h0 hjl hσ
    · exact not_d_of_w hX hf hk0 h0 hjl hσ
    · exact late hσ (by rw [hs]; rintro (h | h | h) <;> cases h)
  · rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, sp, hk⟩ with
      ⟨d, hσ, -⟩ | ⟨d, P, hσ, hsh⟩
    · exact not_d_of_w hX hf hk0 h0 hjl hσ
    · refine late hσ ?_
      rintro (h | h | h) <;> (unfold EvW.LdShape at hsh; rw [h] at hsh)
      · obtain ⟨inst, rfl⟩ := hsh; cases hk
      · obtain ⟨ac, bs, rfl, -⟩ := hsh; cases hk
      · obtain ⟨ac, bs, rfl, -⟩ := hsh; cases hk
  · rcases wait_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨l, p, ok, acq, sc, hk⟩ with
      ⟨d, hσ, -⟩ | ⟨d, P, hσ, hs, -⟩ | ⟨d, P, hσ, -, -⟩ | ⟨d, hσ, -⟩
    · exact not_d_of_w hX hf hk0 h0 hjl hσ
    · exact late hσ (by rw [hs]; rintro (h | h | h) <;> cases h)
    · have h6 := roleWarp_inv hf.roleWarp k0 _ hk0.le h0
      have h7 := roleWarp_inv hf.roleWarp j _ hjl.le hσ
      simp only [RoleWarp, roleWarp] at h6 h7
      omega
    · exact not_d_of_w hX hf hk0 h0 hjl hσ

/-- A count over the first `k₀` events is zero when no event before `k₀` is counted. -/
theorem countP_take_zero {p : Event → Bool} {k0 : Nat}
    (h : ∀ j e, j < k0 → X.get (g, j) = some e → p e = false) :
    ((X.tr g).take k0).countP p = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  rw [List.length_take] at hj
  rw [List.getElem_take]
  have hjl : j < (X.tr g).length := by omega
  have := h j _ (by omega) (show (X.tr g)[j]? = _ from List.getElem?_eq_getElem hjl)
  simp [this]

/-- **The anchored run of a loader state in the loop.** The anchor `k₀` (the state `bar0`, whose
counter is the CTA's `num_pre`), the run of the worker machine from it to the state (`hin`), and no
arrival, copy or poll on any barrier before the anchor. -/
theorem loader_anchor (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X) {k : Nat}
    {d : Loader.D} {P : Loader.Pro} (hk : k < (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) (hd : ¬ PreSite d.site) :
    4 ≤ WComp.warpOf L g ∧ ∃ (k0 : Nat) (d0 : Loader.D), k0 ≤ k ∧
      wAt Q L X g k0 = some (some (.loader d0 P)) ∧ wAt Q L X g k = some (some (.loader d P)) ∧
      d0.site = .bar0 ∧ d0.i = ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) ∧
      (∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.loader d' P)) ∧
        Ring.Ld.InLoop d' ∧ d'.site ≠ .setMaxInc) ∧
      (∀ m, arrivals m ((X.tr g).take k0) = 0) ∧ (∀ m, okPolls m ((X.tr g).take k0) = 0) ∧
      ∀ m, ((X.tr g).take k0).countP (issuesTo m) = 0 := by
  have hw := (loader_inv_at hX hf hk hσ).2.1
  obtain ⟨k0, d0, hk0, h0, hs0, hch⟩ := loader_bar0_back hX hf.ldRng k hk hσ hd
  have hi0 : d0.i = ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) :=
    Lk.ipre_inv hpre hX hf hp k0 _ h0 (.inr hs0)
  have hfr := fun {j e} (hj : j < k0) (he : X.get (g, j) = some e) =>
    loader_fresh_ev hpre hX hf hR (by omega) h0 hs0 hj he
  refine ⟨hw, k0, d0, hk0, Rd.wAt_of_st k0 (by omega) h0, Rd.wAt_of_st k (by omega) hσ, hs0, hi0,
    fun j hj1 hj2 => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · obtain ⟨dj, hdj, hI, hne⟩ := hch j hj1 hj2
    exact ⟨dj, Rd.wAt_of_st j (by omega) hdj, hI, hne⟩
  · exact countP_take_zero fun j e hj he => arrivesOn_notArrive (hfr hj he).1
  · exact countP_take_zero fun j e hj he => okPoll_notWait (hfr hj he).2.2
  · exact countP_take_zero fun j e hj he => issuesTo_notTensor (hfr hj he).2.1

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
