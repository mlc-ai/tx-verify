-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.IpMmaNext
public import Kernels.InklingRelDecode.Proof.Interface.IpInitTrace
public import Kernels.InklingRelDecode.Proof.Interface.MmaFacts
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts
public import Lemmas.Flow.ElectLead

@[expose] public section

/-!
# The MMA warp's elections along a thread

* `step_pred_w`: the state before event `k + 1` of a worker thread and the state before event `k`
  are joined by the composed worker machine's step;
* `mma_shape_at`: an event fired before the last one from the MMA role has the role's site shape;
* `mma_lead`: a thread at a PV (QK) MMA or commit site led the PV (QK) election before: an earlier
  election event with the full mask returned the thread's own lane;
* `fin_commit`: a thread that led an election and is at a state of the role before its last commit
  does that commit before it leaves the role, if its trace ends outside the role.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.IpMma

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The predecessor of a worker-kind state.** -/
theorem step_pred_w {g k : Nat} {w' : WComp.WSt} (hk : k < (X.tr g).length)
    (h : St Q L X g (k + 1) = some (some (.w w'))) :
    ∃ w e, St Q L X g k = some (some (.w w)) ∧ (X.tr g)[k]? = some e ∧
      WComp.next L g w e = some (some w') := by
  obtain ⟨s, e, hσ, he, hn⟩ := step_pred hk h
  cases s with
  | d d =>
    obtain ⟨a, ha, hh⟩ := Ledger.mapInv (show (DComp.next L g Q d e).map
      (Option.map TSt.d) = some (some (.w w')) from hn)
    cases hh
  | w w =>
    obtain ⟨a, ha, hh⟩ := Ledger.mapInv (show (WComp.next L g w e).map
      (Option.map TSt.w) = some (some (.w w')) from hn)
    cases hh
    exact ⟨w, e, hσ, he, ha⟩

/-- **The state of an event fired before the last** is defined at every earlier index. -/
theorem St_def_le {g j : Nat} {s : TSt} (hj : j ≤ (X.tr g).length)
    (h : St Q L X g j = some (some s)) :
    ∀ i, i ≤ j → ∃ s0, St Q L X g i = some (some s0) := by
  induction j generalizing s with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    subst this
    exact ⟨s, h⟩
  | succ j ih =>
    intro i hi
    by_cases hij : i = j + 1
    · subst hij
      exact ⟨s, h⟩
    · obtain ⟨s0, e, hσ, -, -⟩ := step_pred (by omega) h
      exact ih (by omega) hσ i (by omega)

/-- **An event fired before the last one from the MMA role has the site's shape.** -/
theorem mma_shape_at (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k : Nat} {e : Event}
    {d : Mma.D} {P : Loader.Pro} (hg : g < L.threads) (he : (X.tr g)[k]? = some e)
    (hk : k + 1 < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    EvW.MmShape L g d e := by
  obtain ⟨u, hF⟩ := fired_step hX hS hg he hk hσ
  obtain ⟨t', ⟨ha, hi⟩, hf'⟩ := hF
  exact EvW.mma_shape hpre hg (d := d) (P := P) ⟨t', ⟨ha, hi.2⟩, hf'⟩

/-- **A thread at a site of one half of the MMA role led that half's election**: an earlier event
of the thread is an election with the full member mask that returned the thread's own lane. -/
theorem mma_lead (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g : Nat} (hg : g < L.threads)
    {isX : Mma.Site → Bool} {el : Mma.Site} (hel : el = .qkElect ∨ el = .pvElect)
    (hx0 : isX .setMaxReg = false)
    (hn : ∀ {d d' : Mma.D} {e : Event}, Mma.next L g d e = some (some d') →
      isX d'.site = true →
        (d.site = el ∧ ∃ mk inst ld, e.kind = .elect mk inst ld ∧ laneOf L g = ld) ∨
          isX d.site = true) :
    ∀ m d P, m < (X.tr g).length → St Q L X g m = some (some (.w (.mma d P))) →
      isX d.site = true →
        ∃ m0 < m, ∃ pc inst ld, X.get (g, m0) = some ⟨pc, .elect 4294967295 inst ld⟩ ∧
          laneOf L g = ld := by
  intro m
  induction m with
  | zero =>
    intro d P _ hs _
    have hs : Frame.stateAt (code L Q) X g 0 = some (some (.w (.mma d P))) := hs
    rw [Frame.stateAt_zero] at hs
    have h' : (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
        else .w (WComp.code L g Q).init) = .w (.mma d P) := Option.some.inj (Option.some.inj hs)
    split_ifs at h'
    cases h'
  | succ m ih =>
    intro d P hk hs hx
    obtain ⟨w, e, hσ, he, hnx⟩ := step_pred_w (by omega) hs
    rcases wnext_mma hnx with ⟨d0, rfl, hne, hd⟩ | hset
    · rcases hn hd hx with ⟨hsite, mk, inst, ld, hkind, hl⟩ | hx0'
      · have hsh := mma_shape_at hpre hX hS hg he (by omega) hσ
        unfold EvW.MmShape at hsh
        rw [hsite] at hsh
        rcases hel with rfl | rfl
        all_goals
          simp only at hsh
          obtain ⟨inst', ld', hev⟩ := hsh
          rw [hev] at hkind
          simp only [Kind.elect.injEq] at hkind
          obtain ⟨-, -, rfl⟩ := hkind
          exact ⟨m, by omega, _, inst', ld', by
            show (X.tr g)[m]? = _
            rw [he, hev], hl⟩
      · obtain ⟨m0, hm0, r⟩ := ih d0 P (by omega) hσ hx0'
        exact ⟨m0, by omega, r⟩
    · rw [hset] at hx
      simp [hx0] at hx

/-- **Before its last commit, a thread that led an election commits.** The thread's trace ends
outside the MMA role (`St kx` is not an MMA state), `hlead` is an election of the thread with the
full mask returning its own lane. -/
theorem fin_commit (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g kx : Nat} (hg : g < L.threads)
    (hkx : kx < (X.tr g).length) {s : TSt} (hex : St Q L X g kx = some (some s))
    (hns : ∀ d P, s ≠ .w (.mma d P))
    (hlead : ∃ m0 pc inst ld, X.get (g, m0) = some ⟨pc, .elect 4294967295 inst ld⟩ ∧
      laneOf L g = ld) :
    ∀ n m d P, kx - m = n → m < kx → St Q L X g m = some (some (.w (.mma d P))) →
      Alive d.site → ∃ k', m ≤ k' ∧ k' < kx ∧ ∃ d' P' pc sp, k' < (X.tr g).length ∧
        St Q L X g k' = some (some (.w (.mma d' P'))) ∧ d'.site = .finCommit ∧
        X.get (g, k') = some ⟨pc, .tc (.commit sp)⟩ := by
  obtain ⟨m0, pc0, inst0, ld0, hel0, hl0⟩ := hlead
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m d P hn hm hs ha
    obtain ⟨s', hs'⟩ := St_def_le hkx.le hex (m + 1) (by omega)
    obtain ⟨w0, e, hσ0, he, hnx⟩ := step_pred (by omega) hs'
    rw [hs] at hσ0
    cases hσ0
    obtain ⟨w', hw', hnx'⟩ : ∃ w', s' = .w w' ∧
        WComp.next L g (.mma d P) e = some (some w') := by
      cases s' with
      | d x =>
        obtain ⟨a, -, hh⟩ := Ledger.mapInv (show (WComp.next L g (.mma d P) e).map
          (Option.map TSt.w) = some (some (.d x)) from hnx)
        cases hh
      | w w' =>
        obtain ⟨a, ha', hh⟩ := Ledger.mapInv (show (WComp.next L g (.mma d P) e).map
          (Option.map TSt.w) = some (some (.w w')) from hnx)
        cases hh
        exact ⟨_, rfl, ha'⟩
    obtain ⟨d', rfl, hnd⟩ := wnext_mma_fwd hnx' ha.2
    subst hw'
    have hsh := mma_shape_at hpre hX hS hg he (by omega) hs
    by_cases hfc : d.site = .finCommit
    · unfold EvW.MmShape at hsh
      rw [hfc] at hsh
      simp only at hsh
      exact ⟨m, le_rfl, hm, d, P, _, _, by omega, hs, hfc, by
        show (X.tr g)[m]? = _
        rw [he, hsh]⟩
    · obtain ⟨hfe, hal⟩ := next_fin hnd ha hfc
      have hnext : Alive d'.site := by
        by_cases hfe' : d.site = .finElect
        · have hsh' := hsh
          unfold EvW.MmShape at hsh'
          rw [hfe'] at hsh'
          simp only at hsh'
          obtain ⟨inst, ld, hev⟩ := hsh'
          have hel : X.get (g, m) = some ⟨Mma.Site.finElect.pc, .elect 4294967295 inst ld⟩ := by
            show (X.tr g)[m]? = _
            rw [he, hev]
          have hsw : SameWarp L g g := sameWarp_self hg
          have hld := hX.elect.2.2 (e := (g, m0)) (f := (g, m)) _ _ _ _ _ _ _ hel0 hel hsw
          have := hfe hfe' 4294967295 inst ld (by rw [hev]) (by rw [← hld]; exact hl0)
          rw [this]
          exact ⟨by decide, by decide⟩
        · exact hal hfe'
      have hm1 : m + 1 < kx := by
        rcases Nat.lt_or_ge (m + 1) kx with h | h
        · exact h
        · have : m + 1 = kx := by omega
          subst this
          rw [hs'] at hex
          cases hex
          exact (hns d' P rfl).elim
      exact (fun ⟨k', h1, h2, r⟩ => ⟨k', by omega, h2, r⟩) (ih (kx - (m + 1)) (by omega)
        (m + 1) d' P rfl hm1 hs' hnext)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
