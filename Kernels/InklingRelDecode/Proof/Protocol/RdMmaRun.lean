-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaExec
public import Kernels.InklingRelDecode.Proof.Interface.RdQkBack
public import Kernels.InklingRelDecode.Proof.Interface.LedgerInv
public import Kernels.InklingRelDecode.Proof.Interface.RsElect

@[expose] public section

/-!
# The MMA warp's anchored run, from the thread's states

`SOMmaExec` reads the MMA lane's counts on an anchored run: an event `k₀` at which the lane is at
the site `setMaxReg` of the MMA role, the states from `k₀` to the event inside the role
(`hin`), and no earlier commit (`hfresh`). Here the anchor is derived from the thread's states
`St Q L X g k`:

* `wAt_of_st`: the state of a worker thread is the worker machine's state (`Ring.wAt`);
* `mma_back`: an MMA-warp state at an event has an entry state (`setMaxReg`) at an earlier or the
  same event, every state from the entry to it is the role's with the same `Loader.Pro` (one
  contiguous run), has the invariant and is not the role's last site;
* `mma_entry_unique`: a thread has one entry state of the MMA role (the register-request count
  `rqN` of the ledger: a role state is in the first round of the dispatch loop, `phase_inv`),
  from the role byte protocol `RoleReads` (the first load returns a role, a later one the exit);
* `mma_fresh`: so no event before the entry is a commit;
* `qk_commit_block`, `o_commit_block`: the commit of the lane to `s_ready b` (to `o_done`) at
  event `k` is at the site `qkCommit` (`pvCommit2`) of an iteration whose number the earlier
  commits fix, as `SOMmaExec.mma_qkcommit_exec` states for an anchored run.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rd
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.SO
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt)
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The state of a worker thread is the worker machine's.** -/
theorem wAt_of_st : ∀ (k : Nat), k ≤ (X.tr g).length → ∀ {s : WComp.WSt},
    St Q L X g k = some (some (.w s)) → wAt Q L X g k = some (some s) := by
  intro k
  induction k with
  | zero =>
    intro _ s h
    have h0 := h
    rw [St, Frame.stateAt_zero] at h0
    have h1 := Option.some.inj (Option.some.inj h0)
    change (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
      else TSt.w (WComp.code L g Q).init) = TSt.w s at h1
    split at h1
    · cases h1
    · have := TSt.w.inj h1
      subst this
      rfl
  | succ k ih =>
    intro hk s h
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs' := h
    rw [St, Frame.stateAt_succ he] at hs'
    cases hk0 : St Q L X g k with
    | none => simp [St] at hk0 hs'; simp [hk0] at hs'
    | some σ0 =>
      cases σ0 with
      | none =>
        have : Frame.stateAt (code L Q) X g k = some none := hk0
        rw [this] at hs'
        simp [Code.toMachine] at hs'
      | some s0 =>
        have : Frame.stateAt (code L Q) X g k = some (some s0) := hk0
        rw [this] at hs'
        have hn : (threadCode L g Q).next s0 e = some (some (.w s)) := hs'
        cases s0 with
        | d s1 =>
          rw [next_d] at hn
          obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
          cases h
        | w s1 =>
          rw [next_w] at hn
          obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
          cases h
          have h1 := ih (by omega) hk0
          have e1 : wAt Q L X g (k + 1) = (wAt Q L X g k).bind fun σ =>
              (WComp.code L g Q).toMachine.next σ e :=
            Frame.stateAt_succ (C := fun g => WComp.code L g Q) he
          rw [e1, h1]
          simpa [Code.toMachine] using ha

/-- A step of the MMA machine is not a step into the site `setMaxReg`, and not out of
`setMaxRegInc`. -/
theorem next_ne_setMaxReg {d0 d : Mma.D} {e : Event} (hn : Mma.next L g d0 e = some (some d)) :
    d.site ≠ .setMaxReg ∧ d0.site ≠ .setMaxRegInc := by
  constructor
  · unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at hn
    repeat' split at hn
    all_goals first
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
      | (simp only [Option.some.injEq] at hn; subst hn; simp_all)
  · intro h
    simp [Mma.next, h] at hn

/-- **Backward from an MMA-warp state to the entry of the role.** The state at an event has an
entry state (the site `setMaxReg`) at an event before or at it, and every state between is the
role's, with the same `Loader.Pro`, has the invariant and is not at the role's last site. -/
theorem mma_back (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X) :
    ∀ (k : Nat) {d : Mma.D} {P : Loader.Pro}, k < (X.tr g).length →
      St Q L X g k = some (some (.w (.mma d P))) →
      ∃ (k0 : Nat) (d0 : Mma.D), k0 ≤ k ∧ St Q L X g k0 = some (some (.w (.mma d0 P))) ∧
        d0.site = .setMaxReg ∧
        ∀ j, k0 ≤ j → j < k → ∃ dj, St Q L X g j = some (some (.w (.mma dj P))) ∧
          Mma.Inv dj ∧ dj.site ≠ .setMaxRegInc := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d P hk hσ
    by_cases hs : d.site = .setMaxReg
    · exact ⟨k, d, le_refl _, hσ, hs, fun j h1 h2 => by omega⟩
    · obtain ⟨k0, e, d0, hadj, hg0, he, hs0, hn⟩ := mma_state_pred_adj hX hk hσ hs
      obtain ⟨k1, d1, hk1, hσ1, hs1, hch⟩ := ih k0 (by omega) (by omega) hs0
      refine ⟨k1, d1, by omega, hσ1, hs1, fun j hj1 hj2 => ?_⟩
      by_cases hjk : j = k0
      · subst hjk
        exact ⟨d0, hs0, mma_inv_at hX hf (by omega) hs0, (next_ne_setMaxReg hn).2⟩
      · exact hch j hj1 (by omega)

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- The role byte protocol makes the entry of the MMA role unique. -/
theorem mma_entry_unique (hR : RoleReads L X) {k1 k2 : Nat} {d1 d2 : Mma.D} {P1 P2 : Loader.Pro}
    (hk1 : k1 < (X.tr g).length) (hk2 : k2 < (X.tr g).length)
    (h1 : St Q L X g k1 = some (some (.w (.mma d1 P1)))) (s1 : d1.site = .setMaxReg)
    (h2 : St Q L X g k2 = some (some (.w (.mma d2 P2)))) (s2 : d2.site = .setMaxReg) :
    k1 = k2 := by
  have key : ∀ {k1 k2 : Nat} {d1 d2 : Mma.D} {P1 P2 : Loader.Pro},
      k1 < (X.tr g).length → k2 < (X.tr g).length → k1 < k2 →
      St Q L X g k1 = some (some (.w (.mma d1 P1))) → d1.site = .setMaxReg →
      St Q L X g k2 = some (some (.w (.mma d2 P2))) → d2.site = .setMaxReg → False := by
    intro k1 k2 d1 d2 P1 P2 hk1 hk2 hlt h1 s1 h2 s2
    obtain ⟨-, t1, hr1, -, -, hkk1, -, -⟩ := phase_inv hpre hX hf.sound hR k1 _ (by omega) h1
    obtain ⟨-, t2, hr2, -, -, hkk2, -, -⟩ := phase_inv hpre hX hf.sound hR k2 _ (by omega) h2
    have t1z : t1 = 0 := hkk1 (by simp [tKind, wKind])
    have t2z : t2 = 0 := hkk2 (by simp [tKind, wKind])
    subst t1z t2z
    have p1 : (tPh (.w (.mma d1 P1))).1 = 1 := by simp [tPh, wPh, s1]
    have p2 : (tPh (.w (.mma d2 P2))).1 = 1 := by simp [tPh, wPh, s2]
    rw [p1] at hr1
    rw [p2] at hr2
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k1) = some e := ⟨_, List.getElem?_eq_getElem hk1⟩
    obtain ⟨hreq, -⟩ := event_req hX hf.sound he h1
    have hq : (tReq (.w (.mma d1 P1))).isSome = true := by simp [tReq, wReqS, mmaReq, s1]
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

/-- **No commit before the entry of the MMA role**: an MMA-warp state at an event whose entry
state is at `k₀` has no commit among the thread's first `k₀` events. -/
theorem mma_fresh (hR : RoleReads L X) (hg : g < L.threads) {k0 : Nat} {d0 : Mma.D} {P : Loader.Pro}
    (hk0 : k0 < (X.tr g).length) (h0 : St Q L X g k0 = some (some (.w (.mma d0 P))))
    (hs0 : d0.site = .setMaxReg) (m : Loc) : ((X.tr g).take k0).countP (commitsTo m) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  rw [List.length_take] at hj
  have hjk : j < k0 := by omega
  have hjl : j < (X.tr g).length := by omega
  rw [List.getElem_take]
  intro hc
  have hget : X.get (g, j) = some (X.tr g)[j] := by
    show (X.tr g)[j]? = _
    exact List.getElem?_eq_getElem hjl
  have hcm : ∃ sp, (X.tr g)[j].kind = .tc (.commit sp) := by
    unfold commitsTo at hc
    split at hc
    · rename_i sp hk
      exact ⟨sp, hk⟩
    · cases hc
  obtain ⟨d, P', hσ, -⟩ := mma_event_state hpre hX hf.sound hf.tracked hg hget (Or.inr hcm)
  obtain ⟨k1, d1, hk1, hσ1, hs1, -⟩ := mma_back hX hf j hjl hσ
  have := mma_entry_unique hpre hX hf hR (by omega) hk0 hσ1 hs1 h0 hs0
  omega


/-! ### The commits of the lane -/

/-- **The anchored run of an MMA-warp state at an event.** The entry `k₀` (the site `setMaxReg`),
the run of the worker machine from it to the state (`hin`), and the counts of `SOMmaExec`: no
commit to any barrier before the entry. -/
theorem mma_anchor (hR : RoleReads L X) (hg : g < L.threads) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    4 ≤ WComp.warpOf L g ∧ ∃ (k0 : Nat) (d0 : Mma.D), k0 ≤ k ∧
      wAt Q L X g k0 = some (some (.mma d0 P)) ∧ wAt Q L X g k = some (some (.mma d P)) ∧
      d0.site = .setMaxReg ∧
      (∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧ Mma.Inv d' ∧
        d'.site ≠ .setMaxRegInc) ∧
      ∀ m, ((X.tr g).take k0).countP (commitsTo m) = 0 := by
  obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
  have hw : ¬ IsDefault L g := hinv.1
  have hwarp : 4 ≤ WComp.warpOf L g := by
    show 4 ≤ Worker.warpOf L g
    unfold Worker.warpOf
    unfold IsDefault at hw
    omega
  obtain ⟨k0, d0, hk0, h0, hs0, hch⟩ := mma_back hX hf k hk hσ
  refine ⟨hwarp, k0, d0, hk0, wAt_of_st k0 (by omega) h0, wAt_of_st k (by omega) hσ, hs0,
    fun j hj1 hj2 => ?_, mma_fresh hpre hX hf hR hg (by omega) h0 hs0⟩
  obtain ⟨dj, hdj, hI, hne⟩ := hch j hj1 hj2
  exact ⟨dj, wAt_of_st j (by omega) hdj, hI, hne⟩

/-- **The QK commit to `s_ready b` of the lane.** The commit at event `k` is at the site `qkCommit`
of an iteration `i` with `i % 2 = b`, which is block `i` of the buffer: the `n`-th commit to the
barrier is for block `2 n + b`. -/
theorem qk_commit_block (hR : RoleReads L X) (hlead : ElectLead L g (X.tr g))
    (hB : Mma.MmaBcast L X) (hg : g < L.threads) {k pc b : Nat} {sp : TcCommit.Spec} (hb : b < 2)
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) (hsp : sp.mbar = sReady L (g / L.block) b) :
    ∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      d.site = .qkCommit ∧ d.i % 2 = b ∧
      d.i = blockB b (((X.tr g).take k).countP (commitsTo (sReady L (g / L.block) b))) := by
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, -⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (Or.inr ⟨sp, rfl⟩)
  obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hin, hfresh⟩ := mma_anchor hpre hX hf hR hg hk hσ
  have h0p : Mm.qkDone d0 = 0 := by simp [Mm.qkDone, hs0]
  obtain ⟨hs, hi2, hi⟩ := mma_qkcommit_exec hpre hw hg hX hk0 h0 hd hin h0p hb
    (fun e' he' => hlead e' (List.mem_of_mem_take he'))
    ((bcast_of_mma hf.roleWarp hB hg hk.le hσ).take k) (hfresh _) he hsp
  exact ⟨d, P, hσ, hs, hi2, hi⟩

/-- **The `o_done` commit of the lane.** The commit at event `k` is at the site `pvCommit2` of an
iteration `i`, and `i - 1` is the number of the thread's earlier commits to the barrier. -/
theorem o_commit_block (hR : RoleReads L X) (hlead : ElectLead L g (X.tr g)) (hB : Mma.MmaBcast L X)
    (hg : g < L.threads) {k pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩) (hsp : sp.mbar = oDone L (g / L.block)) :
    ∃ (d : Mma.D) (P : Loader.Pro), St Q L X g k = some (some (.w (.mma d P))) ∧
      d.site = .pvCommit2 ∧
      d.i - 1 = ((X.tr g).take k).countP (commitsTo (oDone L (g / L.block))) := by
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, -⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he (Or.inr ⟨sp, rfl⟩)
  obtain ⟨hw, k0, d0, hk0, h0, hd, hs0, hin, hfresh⟩ := mma_anchor hpre hX hf hR hg hk hσ
  have h0p : Mm.oDoneC d0 = 0 := by simp [Mm.oDoneC, hs0]
  obtain ⟨hs, hi⟩ := mma_ocommit_exec hpre hw hg hX hk0 h0 hd hin h0p
    (fun e' he' => hlead e' (List.mem_of_mem_take he'))
    ((bcast_of_mma hf.roleWarp hB hg hk.le hσ).take k) (hfresh _) he hsp
  exact ⟨d, P, hσ, hs, hi⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Rd
