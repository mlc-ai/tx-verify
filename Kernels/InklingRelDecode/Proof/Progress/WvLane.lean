-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WvLate
public import Kernels.InklingRelDecode.Proof.Progress.WvP0Lag

@[expose] public section

/-!
# A lane of the MMA warp against a default-partition poller

The facts about a lane `y` of a CTA's MMA warp that the lag of the committing lane uses:

* `b1_peer`: while a thread `g` of the CTA has not exited and has made at most two barrier-1
  events, `y` has made at most two before each of its events (a third with a later event of `y`
  would be a passed generation that `g` is a member of, `Bar.bar1_member`).
* `noLate`: so `y` is not at a later-round or exit state (`late_back`: such a state follows a
  role's last state, which has made three barrier-1 events, `phase_inv`), and has not exited.
* `fin_iter_le`: `Interface.fin_iter` at an index up to the trace's end.
* `fin0`: a state at `finBar` or `finElect` of iteration 0 has `n = 0` or `n > 2147483646`.
* `elect_of`: a state that is not `PreE` (before the role's first election) follows an election
  event of the thread.
* `mmaT_loop_le`: an MMA loop state is timed at most 28 after its slot's MMA band starts.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Barrier 1 -/

/-- **A peer of a thread with at most two barrier-1 events has at most two before each of its
events.** -/
theorem b1_peer (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) {g y k : Nat}
    (hc : g / L.block = y / L.block) (hk : k < (X.tr y).length)
    (hnx : ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) (hgb : b1N X g (X.tr g).length ≤ 2) :
    b1N X y k ≤ 2 := by
  by_contra h
  obtain ⟨j, e, hj, hge, hp, hc2⟩ :=
    Flow.exists_nthEv (X := X) (p := Execution.isBarId 1) (g := y) (k := k) (n := 2)
      (by unfold b1N at h; omega)
  obtain ⟨pc, cnt, m, rfl⟩ := NamedBar.isBarId_form hp
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  obtain ⟨rfl, rfl⟩ := bar_one_static hX hb hge
  have hyb : X.IsBarrier (y, j) 1 none pc := hge
  obtain ⟨i, pc', hi, hiord⟩ := Bar.bar1_member hpre hX hyb (show j + 1 < (X.tr y).length by omega)
    (g := g) hc (fun ⟨jx, pcx, hjx⟩ => absurd hjx (hnx jx pcx))
  have hi' : (X.tr g)[i]? = some ⟨pc', .bar 1 none .sync⟩ := hi
  have hil : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hi').1
  have h3 : b1N X g (i + 1) = 3 := by
    unfold b1N
    rw [countP_take_succ _ hi']
    have : ((X.tr g).take i).countP (Execution.isBarId 1) = 2 := hiord.trans hc2
    simp [Execution.isBarId, this]
  have h4 : b1N X g (i + 1) ≤ b1N X g (X.tr g).length := by
    unfold b1N
    exact (List.take_sublist_take_left (by omega)).countP_le
  omega

/-- A role's last state has made three barrier-1 events. -/
theorem wrap_b1 {s : WComp.WSt} (h : wrap s = 1) : (wPh s).2 = 3 ∧ wKind s = 1 := by
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

/-- **A peer of a thread with at most two barrier-1 events is not at a later-round or exit
state.** -/
theorem noLate (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hR : RoleReads L X) {g y k : Nat}
    (hc : g / L.block = y / L.block) (hk : k ≤ (X.tr y).length)
    (hnx : ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) (hgb : b1N X g (X.tr g).length ≤ 2)
    {s : TSt} (hσ : St Q L X y k = some (some s)) : ¬ LateSt s := by
  intro hl
  obtain ⟨j, σ, hj, hσj, hw⟩ := late_back hpre hX hS hR k s hk hσ hl
  obtain ⟨-, t, -, hb1, -, hk1, -, -⟩ := phase_inv hpre hX hS hR j _ (by omega) hσj
  obtain ⟨h3, hkind⟩ := wrap_b1 hw
  have ht : t = 0 := hk1 hkind
  have : b1N X y j = 3 := by
    rw [hb1, ht]
    exact h3
  have := b1_peer hpre hX hc (show j < (X.tr y).length by omega) hnx hgb
  omega

/-- **A worker peer of such a thread has not exited.** -/
theorem noExit_peer (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) {g y : Nat}
    (hc : g / L.block = y / L.block) (hyw : ¬ y % L.block < 128)
    (hnx : ∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) (hgb : b1N X g (X.tr g).length ≤ 2) :
    ∀ j pc, X.get (y, j) ≠ some ⟨pc, .exit⟩ := by
  intro j pc hj
  have hj' : j ≤ (X.tr y).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr y)[j]? = _ from hj)).1.le
  rcases exit_event_state hX hf.sound hf.tracked hj with ⟨de, hσ', -⟩ | ⟨x, hσ', -⟩
  · exact hyw ((cls_inv j _ hj' hσ').mp trivial)
  · exact noLate hpre hX hf.sound hR hc hj' hnx hgb hσ' trivial

/-! ### The loop's end -/

/-- **`Interface.fin_iter` at an index up to the trace's end.** -/
theorem fin_iter_le (hX : Consistent L kernel asms mem0 X) {y : Nat}
    (hlead : ElectLead L y (X.tr y)) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k ≤ (X.tr y).length) (hσ : St Q L X y k = some (some (.w (.mma d P))))
    (hfs : FinSite d.site) (h1 : 1 ≤ d.n) (h2 : d.n ≤ 2147483646) : d.i = d.n + 1 := by
  rcases Nat.lt_or_ge k (X.tr y).length with hlt | hge
  · exact fin_iter hX hlead k hlt hσ hfs h1 h2
  have hsite : d.site ≠ .setMaxReg := by
    intro hs
    unfold FinSite at hfs
    rw [hs] at hfs
    rcases hfs with h | h | h | h | h <;> cases h
  obtain ⟨k0, e, d0, rfl, -, he, hs0, hn⟩ := Proof.Wv.mma_pred_le hX hk hσ hsite
  have hmem : e ∈ X.tr y := List.mem_of_getElem? (show (X.tr y)[k0]? = some e from he)
  have hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L y :=
    fun mask inst ld h => hlead e hmem mask inst ld h
  obtain ⟨-, hnn, hc⟩ := next_fin hn hl hfs h1 h2
  rcases hc with ⟨hf0, hi0⟩ | ⟨-, -, hi3⟩
  · have := fin_iter hX hlead k0 (by omega) hs0 hf0 (by omega) (by omega)
    omega
  · omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The step into `finBar` or `finElect` of iteration 0. -/
theorem next_fin0 {g : Nat} {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hs : d.site = .finBar ∨ d.site = .finElect) (hi : d.i = 0) :
    (d0.site = .finBar ∧ d0.i = 0 ∧ d0.n = d.n) ∨
      (d0.site = .bar0 ∧ (d.n = 0 ∨ 2147483646 < d.n)) := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp at hs; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp at hi; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)

/-- **A state at `finBar` or `finElect` of iteration 0** has a loop bound of 0 or above
`2147483646`. -/
theorem fin0 (hX : Consistent L kernel asms mem0 X) {y : Nat} :
    ∀ (k : Nat) {d : Mma.D} {P : Loader.Pro}, k ≤ (X.tr y).length →
      St Q L X y k = some (some (.w (.mma d P))) → (d.site = .finBar ∨ d.site = .finElect) →
      d.i = 0 → d.n = 0 ∨ 2147483646 < d.n := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d P hk hσ hs hi
    have hsite : d.site ≠ .setMaxReg := by
      rcases hs with h | h <;> rw [h] <;> nofun
    obtain ⟨k0, e, d0, rfl, -, -, hs0, hn⟩ := Proof.Wv.mma_pred_le hX hk hσ hsite
    rcases next_fin0 hn hs hi with ⟨h1, h2, h3⟩ | ⟨-, h⟩
    · rw [← h3]
      exact ih k0 (by omega) (by omega) hs0 (.inl h1) h2
    · exact h

/-! ### Before the first election -/

/-- The MMA role's states before its first election: before the loop, the first iteration up to
its election, and the end of a loop that does not run. -/
def PreE (d : Mma.D) : Prop :=
  Mma.PreSite d.site ∨ (d.i = 0 ∧ (d.site = .qkBar ∨ d.site = .kvWait ∨ d.site = .qkShfl ∨
    d.site = .qkBar2 ∨ d.site = .qkElect ∨ d.site = .finBar ∨ d.site = .finElect))

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- A step out of `PreE` is an election. -/
theorem next_preE {g : Nat} {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hI : Mma.Inv d0) (hk : d.site.isSkip = false) (h0 : PreE d0) (h : ¬ PreE d) :
    ∃ mask inst ld, e.kind = .elect mask inst ld := by
  have hpre := hI.pre
  unfold PreE at h0 h
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | exact ⟨_, _, _, by assumption⟩
    | (simp only [Option.some.injEq] at hn; subst hn
       simp_all [Mma.PreSite, Mma.Site.isSkip]; done)

/-- **A state that is not before the first election follows an election of the thread.** -/
theorem elect_of (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X) {y : Nat}
    (hbc : Mma.BcastRun (X.tr y)) :
    ∀ (k : Nat) {d : Mma.D} {P : Loader.Pro}, k ≤ (X.tr y).length →
      St Q L X y k = some (some (.w (.mma d P))) → ¬ PreE d →
      ∃ j e mask inst ld, j < k ∧ X.get (y, j) = some e ∧ e.kind = .elect mask inst ld := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d P hk hσ hne
    have hsite : d.site ≠ .setMaxReg := by
      intro h
      exact hne (.inl (by rw [h]; trivial))
    obtain ⟨k0, e, d0, rfl, -, he, hs0, hn⟩ := Proof.Wv.mma_pred_le hX hk hσ hsite
    by_cases h0 : PreE d0
    · obtain ⟨mask, inst, ld, hk'⟩ := next_preE hn (mma_inv_at hX hf (by omega) hs0)
        (not_skip hX hbc hσ) h0 hne
      exact ⟨k0, e, mask, inst, ld, by omega, he, hk'⟩
    · obtain ⟨j, e', mask, inst, ld, hj, he', hk'⟩ := ih k0 (by omega) (by omega) hs0 h0
      exact ⟨j, e', mask, inst, ld, by omega, he', hk'⟩

/-! ### Times -/

/-- An MMA loop state is timed at most 28 after its slot's MMA band starts. -/
theorem mmaT_loop_le (d : Mma.D) (h : Mma.QkSite d.site ∨ Mma.PvSite d.site) :
    mmaT d ≤ slot d.i + bandM + 28 := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp only [Mma.QkSite, Mma.PvSite, or_self, or_false, false_or] at h <;>
    simp only [mmaT, Bound.Mma.pos] <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wv
