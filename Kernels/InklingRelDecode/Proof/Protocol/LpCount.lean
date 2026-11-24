-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpRun
public import Kernels.InklingRelDecode.Proof.Protocol.RingCommitLe
public import Kernels.InklingRelDecode.Proof.Interface.RdPvBack

@[expose] public section

/-!
# The ring's counts from the thread's states

The budget clauses and the parities of `Ring.Kv.Hyp`, at an event of a thread, with the anchored
runs derived from the thread's states (`Lp.loader_anchor`, `Rd.mma_anchor`) instead of taken as
premises:

* `arrive_budget`: the loader's arrival on `kv_ready s` has more successful polls of `kv_empty s`
  before it than earlier arrivals (`FullSource.arrive.hb`);
* `copy_budget`: the copies of a loader thread that led its elections are at most eight per
  successful poll of `kv_empty s` (`FullSource.copy.hb`, `Hyp.issue`);
* `notify_budget`: the MMA lane's commit to `kv_empty s` has more successful polls of `kv_ready s`
  before it than earlier commits (`EmptySource.notify.hb`);
* `full_parity`, `empty_parity`: the parity of a successful poll of `kv_ready s` (an MMA-warp
  lane's) and of `kv_empty s` (a loader lane's) is that of the thread's earlier successful polls.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt)
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The loader's event at a state -/

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- The event at a loader state is `LdShape` of the state. -/
theorem loader_ev_shape {k : Nat} {e : Event} {d : Loader.D} {P : Loader.Pro}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.w (.loader d P)))) :
    EvW.LdShape Q L g d e := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨t, hgd, hfire⟩ := hF
  have hr := hf.reach hg hσ
  exact EvW.loader_shape hpre hr.2 (hf.ldRng hg hσ) (g := g) (d := d) (P := P) (u := u)
    ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩

/-- A loader state whose event is an arrival, a copy or a poll is in the loop. -/
theorem loader_ev_notPre {k : Nat} {e : Event} {d : Loader.D} {P : Loader.Pro}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.w (.loader d P))))
    (hk : (∃ l tx c rel sc, e.kind = .arrive l tx c rel sc) ∨ (∃ a sp, e.kind = .tensorIssue a sp) ∨
      ∃ l p ok acq sc, e.kind = .wait l p ok acq sc) : ¬ PreSite d.site := by
  have hsh := loader_ev_shape hpre hX hf he hσ
  rintro (h | h | h) <;> (unfold EvW.LdShape at hsh; rw [h] at hsh)
  · obtain ⟨inst, rfl⟩ := hsh
    rcases hk with ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> cases h
  · obtain ⟨ac, bs, rfl, -⟩ := hsh
    rcases hk with ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> cases h
  · obtain ⟨ac, bs, rfl, -⟩ := hsh
    rcases hk with ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> cases h

omit hpre hX hf in
theorem numPre_le (Q : Params) (r s : Nat) : ProA.numPre Q r s ≤ 3 := by
  unfold ProA.numPre
  exact Nat.min_le_right _ _

/-! ### The loader's budgets -/

/-- **The loader's arrival on `kv_ready s` follows more successful polls of `kv_empty s` than its
earlier arrivals.** -/
theorem arrive_budget (hR : RoleReads L X) (hp : NumPreRead Q L X) {k : Nat} {d : Loader.D}
    {P : Loader.Pro} (hσ : St Q L X g k = some (some (.w (.loader d P)))) {s pc tx cnt : Nat}
    {rel : Bool} {sc : MbarScope} (hs : s < 3)
    (he : X.get (g, k) = some ⟨pc, .arrive (kvReady L (g / L.block) s) tx cnt rel sc⟩) :
    arrivals (kvReady L (g / L.block) s) ((X.tr g).take k) + 1 ≤
      okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  have hnp := loader_ev_notPre hpre hX hf he hσ (.inl ⟨_, _, _, _, _, rfl⟩)
  obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hi0, hin, hA, hP, -⟩ :=
    loader_anchor hpre hX hf hR hp hk hσ hnp
  have := Ring.loader_arrive_exec hpre hw hg hX hk0 h0 hd (hf.ldRng hg hσ) hin hs0
    (by rw [hi0]; exact numPre_le _ _ _) hs (hA _) (hP _) he
  omega

/-- **The copies of a loader thread that led its elections are at most eight per successful poll
of `kv_empty s`.** -/
theorem copy_budget (hR : RoleReads L X) (hp : NumPreRead Q L X) (hlead : ElectLead L g (X.tr g))
    {k : Nat} {d : Loader.D} {P : Loader.Pro} (hσ : St Q L X g k = some (some (.w (.loader d P))))
    {s pc a : Nat} {sp : TensorCopy.Spec} (hs : s < 3)
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) (hsp : sp.mbar = kvReady L (g / L.block) s) :
    ((X.tr g).take k).countP (issuesTo (kvReady L (g / L.block) s)) + 1 ≤
      8 * okPolls (kvEmpty L (g / L.block) s) ((X.tr g).take k) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  have hnp := loader_ev_notPre hpre hX hf he hσ (.inr (.inl ⟨_, _, rfl⟩))
  obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hi0, hin, -, hP, hC⟩ :=
    loader_anchor hpre hX hf hR hp hk hσ hnp
  obtain ⟨hcp, -, -, -, hmod, -, hcnt⟩ := Ring.loader_copy_exec hpre hw hg hX hk0 h0 hd
    (hf.ldRng hg hσ) hin hs0
    (by rw [hi0]; exact numPre_le _ _ _) hs (hlead.take k) (hC _) (hP _) he hsp
  have hlt := Ring.Ld.cpIn_lt hcp
  omega

/-! ### The MMA warp's anchor, with its polls -/

/-- **No poll of an MMA-warp thread before the entry of its role.** -/
theorem mma_fresh_polls (hR : RoleReads L X) {k0 : Nat} {d0 : Mma.D} {P : Loader.Pro}
    (hk0 : k0 < (X.tr g).length) (h0 : St Q L X g k0 = some (some (.w (.mma d0 P))))
    (hs0 : d0.site = .setMaxReg) (m : Loc) :
    okPolls m ((X.tr g).take k0) = 0 := by
  refine countP_take_zero fun j e hj he => okPoll_notWait fun l p ok acq sc hk => ?_
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hjl : j < (X.tr g).length := by omega
  rcases wait_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨l, p, ok, acq, sc, hk⟩ with
    ⟨d, hσ, -⟩ | ⟨d, P', hσ, -, -⟩ | ⟨d, P', hσ, -, -⟩ | ⟨d, hσ, -⟩
  · exact not_d_of_w hX hf hk0 h0 hjl hσ
  · have h6 := roleWarp_inv hf.roleWarp k0 _ hk0.le h0
    have h7 := roleWarp_inv hf.roleWarp j _ hjl.le hσ
    simp only [RoleWarp, roleWarp] at h6 h7
    omega
  · obtain ⟨k1, d1, hk1, hσ1, hs1, -⟩ := Rd.mma_back hX hf j hjl hσ
    have := Rd.mma_entry_unique hpre hX hf hR (by omega) hk0 hσ1 hs1 h0 hs0
    omega
  · exact not_d_of_w hX hf hk0 h0 hjl hσ

omit hpre hX hf in
/-- The step into `pvCommit1` is from PV step 7. -/
theorem next_into_pvCommit1 {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d))
    (hs : d.site = .pvCommit1) : d0.site = .pv 7 := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all
       exact Fin.ext (by omega))

/-- **A thread that commits to `kv_empty s` led its elections**: the commit is at `pvCommit1`,
after PV step 7, which only the elected lane reaches. -/
theorem commit_lead {k pc s : Nat} {sp : TcCommit.Spec} (hs : s < 3)
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) (hsp : sp.mbar = kvEmpty L (g / L.block) s) :
    ∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      d.site = .pvCommit1 ∧ ElectLead L g (X.tr g) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, -⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (Or.inr ⟨sp, rfl⟩)
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨t, hgd, hfire⟩ := hF
  have hF' : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) _ (some u) :=
    ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩
  have hcm := Ring.mm_commitsTo hpre hg hF' hs
  rw [commitsTo_of_kind (sp := sp) rfl] at hcm
  simp only [hsp, decide_true] at hcm
  have hsite : d.site = .pvCommit1 := by
    have := hcm.symm
    simp only [decide_eq_true_eq] at this
    exact this.1
  obtain ⟨k0, e0, d0, hadj, -, -, hσ0, hn⟩ :=
    mma_state_pred_adj hX hk hσ (by rw [hsite]; nofun)
  have h7 := next_into_pvCommit1 hn hsite
  exact ⟨d, P, hσ, hsite, lead_of_pv hX 7 (j := 7) rfl (by omega) hσ0 h7⟩

/-! ### Who polls the ring barriers -/

/-- **A poll of `kv_ready s` of CTA `c` is an MMA-warp state at `kvWait`**, of the CTA, at an
iteration of the slot. -/
theorem poll_kvReady {k pc p c s : Nat} {ok acq : Bool} {sc : MbarScope} (hs : s < 3)
    (he : X.get (g, k) = some ⟨pc, .wait (kvReady L c s) p ok acq sc⟩) :
    ∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      d.site = .kvWait ∧ g / L.block = c ∧ d.i % 3 = s ∧ p = d.i / 3 % 2 ∧ acq = true ∧
      sc = .cta := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  rcases wait_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨_, _, _, _, _, rfl⟩ with
    ⟨d, hσ, ⟨-, ok', hev⟩ | hw⟩ | ⟨d, P, hσ, hw, hsh⟩ | ⟨d, P, hσ, hw, hsh⟩ | ⟨d, hσ, -, ok', hev⟩
  · simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    obtain ⟨-, hl, -⟩ := hev
    simp only [kvReady, EvW.barLoc, EvW.kvReadyOff, EvD.Bar.loc, EvD.sReadyOf, EvD.Bar.off,
      Loc.mk.injEq] at hl
    omega
  · have := Interface.odoneWait hpre hX hf hσ hw he
    simp only [kvReady, EvW.barLoc, EvW.kvReadyOff, EvD.Bar.loc, EvD.Bar.off,
      Loc.mk.injEq] at this
    omega
  · unfold EvW.LdShape at hsh
    rw [hw] at hsh
    obtain ⟨ok', hev⟩ := hsh
    simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    obtain ⟨-, hl, -⟩ := hev
    simp only [kvReady, kvEmpty, EvW.barLoc, EvW.kvReadyOff, EvW.kvEmptyOff, Loc.mk.injEq] at hl
    omega
  · unfold EvW.MmShape at hsh
    rcases hw with hw | hw <;> rw [hw] at hsh <;> obtain ⟨ok', hev⟩ := hsh <;>
      simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    · obtain ⟨-, hl, hp, -, hacq, hsc⟩ := hev
      simp only [kvReady, EvW.barLoc, EvW.kvReadyOff, Loc.mk.injEq] at hl
      exact ⟨d, P, hσ, hw, by omega, by omega, hp, hacq, hsc⟩
    · obtain ⟨-, hl, -⟩ := hev
      simp only [kvReady, EvW.pReady, EvW.barLoc, EvW.kvReadyOff, EvW.pReadyOff,
        Loc.mk.injEq] at hl
      omega
  · simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    obtain ⟨-, hl, -⟩ := hev
    simp only [kvReady, EvW.barLoc, EvW.kvReadyOff, EvD.Bar.loc, EvD.Bar.off, Loc.mk.injEq] at hl
    omega

/-- **A poll of `kv_empty s` of CTA `c` is a loader state at `wait`**, of the CTA, at an
iteration of the slot. -/
theorem poll_kvEmpty {k pc p c s : Nat} {ok acq : Bool} {sc : MbarScope} (hs : s < 3)
    (he : X.get (g, k) = some ⟨pc, .wait (kvEmpty L c s) p ok acq sc⟩) :
    ∃ (d : Loader.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.loader d P))) ∧
      d.site = .wait ∧ g / L.block = c ∧ d.i % 3 = s ∧ acq = true ∧ sc = .cta := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  rcases wait_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨_, _, _, _, _, rfl⟩ with
    ⟨d, hσ, ⟨-, ok', hev⟩ | hw⟩ | ⟨d, P, hσ, hw, hsh⟩ | ⟨d, P, hσ, hw, hsh⟩ | ⟨d, hσ, -, ok', hev⟩
  · simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    obtain ⟨-, hl, -⟩ := hev
    simp only [kvEmpty, EvW.barLoc, EvW.kvEmptyOff, EvD.Bar.loc, EvD.sReadyOf, EvD.Bar.off,
      Loc.mk.injEq] at hl
    omega
  · have := Interface.odoneWait hpre hX hf hσ hw he
    simp only [kvEmpty, EvW.barLoc, EvW.kvEmptyOff, EvD.Bar.loc, EvD.Bar.off,
      Loc.mk.injEq] at this
    omega
  · unfold EvW.LdShape at hsh
    rw [hw] at hsh
    obtain ⟨ok', hev⟩ := hsh
    simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    obtain ⟨-, hl, -, -, hacq, hsc⟩ := hev
    simp only [kvEmpty, EvW.barLoc, EvW.kvEmptyOff, Loc.mk.injEq] at hl
    exact ⟨d, P, hσ, hw, by omega, by omega, hacq, hsc⟩
  · unfold EvW.MmShape at hsh
    rcases hw with hw | hw <;> rw [hw] at hsh <;> obtain ⟨ok', hev⟩ := hsh <;>
      simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    · obtain ⟨-, hl, -⟩ := hev
      simp only [kvReady, kvEmpty, EvW.barLoc, EvW.kvReadyOff, EvW.kvEmptyOff,
        Loc.mk.injEq] at hl
      omega
    · obtain ⟨-, hl, -⟩ := hev
      simp only [kvEmpty, EvW.pReady, EvW.barLoc, EvW.kvEmptyOff, EvW.pReadyOff,
        Loc.mk.injEq] at hl
      omega
  · simp only [Event.mk.injEq, Kind.wait.injEq] at hev
    obtain ⟨-, hl, -⟩ := hev
    simp only [kvEmpty, EvW.barLoc, EvW.kvEmptyOff, EvD.Bar.loc, EvD.Bar.off, Loc.mk.injEq] at hl
    omega

/-! ### The MMA warp's anchor and counts -/

/-- **The anchored run of an MMA-warp state, with no poll and no commit before the anchor.** -/
theorem mma_anchor_full (hR : RoleReads L X) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    4 ≤ WComp.warpOf L g ∧ ∃ (k0 : Nat) (d0 : Mma.D), k0 ≤ k ∧
      wAt Q L X g k0 = some (some (.mma d0 P)) ∧ wAt Q L X g k = some (some (.mma d P)) ∧
      d0.site = .setMaxReg ∧
      (∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧ Mma.Inv d' ∧
        d'.site ≠ .setMaxRegInc) ∧
      (∀ m, ((X.tr g).take k0).countP (commitsTo m) = 0) ∧
      ∀ m, okPolls m ((X.tr g).take k0) = 0 := by
  have hg : g < L.threads := by
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    exact Frame.lt_of_get hX he
  obtain ⟨hw, -⟩ := Rd.mma_anchor hpre hX hf hR hg hk hσ
  obtain ⟨k0, d0, hk0, h0, hs0, hch⟩ := Rd.mma_back hX hf k hk hσ
  refine ⟨hw, k0, d0, hk0, Rd.wAt_of_st k0 (by omega) h0, Rd.wAt_of_st k (by omega) hσ, hs0,
    fun j hj1 hj2 => ?_, Rd.mma_fresh hpre hX hf hR hg (by omega) h0 hs0,
    mma_fresh_polls hpre hX hf hR (by omega) h0 hs0⟩
  obtain ⟨dj, hdj, hI, hne⟩ := hch j hj1 hj2
  exact ⟨dj, Rd.wAt_of_st j (by omega) hdj, hI, hne⟩

/-- **The MMA lane's commit to `kv_empty s` follows more successful polls of `kv_ready s` than
its earlier commits to `kv_empty s`.** -/
theorem notify_budget (hR : RoleReads L X) {k pc s : Nat} {sp : TcCommit.Spec} (hs : s < 3)
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) (hsp : sp.mbar = kvEmpty L (g / L.block) s) :
    ((X.tr g).take k).countP (commitsTo (kvEmpty L (g / L.block) s)) + 1 ≤
      okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, -, -⟩ := commit_lead hpre hX hf hs he hsp
  obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hin, hC, hP⟩ := mma_anchor_full hpre hX hf hR hk hσ
  have hp0 : Ring.Mm.polled d0 = 0 := by simp [Ring.Mm.polled, hs0]
  have hdn0 : Ring.Mm.done d0 = 0 := by simp [Ring.Mm.done, hs0]
  exact Ring.mma_commit_gate_le hpre hw hg hX hk0 h0 hd hin hp0 hdn0 hs (hP _) (hC _) he hsp

/-- **The parity of a successful poll of `kv_ready s`** is that of the thread's earlier successful
polls of it. -/
theorem full_parity (hR : RoleReads L X) {k pc p c s : Nat} {acq : Bool} {sc : MbarScope}
    (hs : s < 3) (he : X.get (g, k) = some ⟨pc, .wait (kvReady L c s) p true acq sc⟩) :
    p % 2 = (okPolls (kvReady L c s) ((X.tr g).take k) + 0) % 2 := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, -, hc, -⟩ := poll_kvReady hpre hX hf hs he
  subst hc
  obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hin, -, hP⟩ := mma_anchor_full hpre hX hf hR hk hσ
  have hp0 : Ring.Mm.polled d0 = 0 := by simp [Ring.Mm.polled, hs0]
  obtain ⟨-, -, -, -, h⟩ := Ring.mma_poll_exec hpre hw hg hX hk0 h0 hd hin hp0 hs (hP _) he
  omega

/-- **The parity of a successful poll of `kv_empty s`** is that of the thread's earlier successful
polls of it, plus one for a slot the prologue does not preload. -/
theorem empty_parity (hR : RoleReads L X) (hp : NumPreRead Q L X) {k pc p c s : Nat} {acq : Bool}
    {sc : MbarScope} (hs : s < 3)
    (he : X.get (g, k) = some ⟨pc, .wait (kvEmpty L c s) p true acq sc⟩) :
    p % 2 = (okPolls (kvEmpty L c s) ((X.tr g).take k) +
      (if s < ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) then 0 else 1)) % 2 := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, hw, hc, -⟩ := poll_kvEmpty hpre hX hf hs he
  subst hc
  have hnp : ¬ PreSite d.site := by rw [hw]; rintro (h | h | h) <;> cases h
  obtain ⟨hw4, k0, d0, hk0, h0, hd, hs0, hi0, hin, -, hP, -⟩ :=
    loader_anchor hpre hX hf hR hp hk hσ hnp
  have hpo : Ring.Ld.polled d0 = d0.i := by simp [Ring.Ld.polled, Ring.Ld.afterWait, hs0]
  obtain ⟨-, -, -, -, h⟩ := Ring.loader_poll_exec hpre hw4 hg hX hk0 h0 hd (hf.ldRng hg hσ) hin
    (by rw [hpo, hi0]; exact numPre_le _ _ _) (hP _) he
  rw [hpo, hi0] at h
  exact h

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
