-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsData
public import Kernels.InklingRelDecode.Proof.Interface.RdElect
public import Kernels.InklingRelDecode.Proof.Interface.RdPvBack

@[expose] public section

/-!
# The MMA lane's counts at its states, and the coordinates of its MMAs

`Rd.mma_anchor` gives an MMA-warp state at an event its anchored run from the entry of the role
(`setMaxReg`) with no commit before the entry. Here:

* `mma_fresh_polls`: no successful poll of `p_ready` before the entry either (a poll of `p_ready`
  is the MMA role's, `poll_class`, and the entry is unique);
* `mma_cnt`: at an MMA-warp state `d` the thread's successful polls of `p_ready b` number
  `below2 b (SO.Mm.pPolled d)`; if every election of the thread so far returned its lane, its
  commits to `s_ready b` number `below2 b (SO.Mm.qkDone d)` and those to `o_done` `SO.Mm.oDoneC d`
  (the counts of `SOMmaRun` on the anchored run);
* `qkAt_of`, `pvAt_of`: the event at a state at a QK (PV) step is a QK (PV) MMA of its block with
  the counts of `Sr.QkAt` (`Sr.PvAt`) for the CTA's committing lane and base column 0.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Hs
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal kvReady kvEmpty)
open PTX.Kernels.InklingRelDecode.Proof.SO (IsMma below2)
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- Two barrier locations are equal exactly when their CTAs and offsets are. -/
theorem barLoc_eq {c c' o o' : Nat} :
    EvW.barLoc L c o = EvW.barLoc L c' o' ↔ c = c' ∧ o = o' := by
  unfold EvW.barLoc
  simp only [Loc.mk.injEq, true_and]
  omega

/-- A successful poll on `m` is a `wait` on `m` that succeeded. -/
theorem okPoll_true {m : Loc} {e : Event} (h : okPoll m e = true) :
    ∃ p acq sc, e = ⟨e.pc, .wait m p true acq sc⟩ := by
  obtain ⟨pc, k⟩ := e
  cases k with
  | wait l p ok acq sc =>
    cases ok
    · simp [okPoll, sourceWaitSuccess] at h
    · simp only [okPoll, sourceWaitSuccess, decide_eq_true_eq] at h
      subst h
      exact ⟨p, acq, sc, rfl⟩
  | _ => simp [okPoll, sourceWaitSuccess] at h

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **No successful poll of `p_ready` before the entry of the MMA role.** -/
theorem mma_fresh_polls (hR : RoleReads L X) {k0 : Nat} {d0 : Mma.D} {P : Loader.Pro}
    (hk0 : k0 < (X.tr g).length) (h0 : St Q L X g k0 = some (some (.w (.mma d0 P))))
    (hs0 : d0.site = .setMaxReg) {b : Nat} (hb : b < 2) :
    okPolls (pReady L (g / L.block) b) ((X.tr g).take k0) = 0 := by
  unfold okPolls
  rw [List.countP_eq_zero]
  intro e he hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  rw [List.length_take] at hj
  have hjk : j < k0 := by omega
  have hjl : j < (X.tr g).length := by omega
  rw [List.getElem_take] at hc
  have hget : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hjl
  obtain ⟨p, acq, sc, hev⟩ := okPoll_true hc
  rw [hev] at hget
  rcases (poll_class hpre hX hf hget).2.2 with
    ⟨d, -, -, hm, -⟩ | ⟨d, -, -, hm, -⟩ | ⟨d, P', -, -, hm⟩ | ⟨d, P', -, -, hm⟩ |
    ⟨d, P', hσ, -, -, -⟩ | ⟨d, -, -, hm, -⟩
  rotate_left 4
  · obtain ⟨k1, d1, hk1, hσ1, hs1, -⟩ := Rd.mma_back hX hf j hjl hσ
    have := Rd.mma_entry_unique hpre hX hf hR (by omega) hk0 hσ1 hs1 h0 hs0
    omega
  all_goals
    (simp only [EvW.sReady, EvW.pReady, EvW.oDone, EvW.oFinal, EvW.kvReady, EvW.kvEmpty,
      barLoc_eq, EvW.sReadyOff, EvW.pReadyOff, EvW.oDoneOff, EvW.oFinalOff, EvW.kvReadyOff,
      EvW.kvEmptyOff, true_and] at hm
     omega)

/-- **The MMA lane's counts at a state.** -/
theorem mma_cnt (hR : RoleReads L X) (hg : g < L.threads) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    (∀ b < 2, okPolls (pReady L (g / L.block) b) ((X.tr g).take k) = below2 b (SO.Mm.pPolled d)) ∧
      (ElectLead L g ((X.tr g).take k) → Mma.BcastRun ((X.tr g).take k) →
        (∀ b < 2, ((X.tr g).take k).countP (commitsTo (sReady L (g / L.block) b)) =
          below2 b (SO.Mm.qkDone d)) ∧
        ((X.tr g).take k).countP (commitsTo (oDone L (g / L.block))) = SO.Mm.oDoneC d) := by
  have hw : 4 ≤ WComp.warpOf L g := (Rd.mma_anchor hpre hX hf hR hg hk hσ).1
  obtain ⟨k0, d0, hk0, h0, hs0, hch⟩ := Rd.mma_back hX hf k hk hσ
  have h0w : wAt Q L X g k0 = some (some (.mma d0 P)) := Rd.wAt_of_st k0 (by omega) h0
  have hdw : wAt Q L X g k = some (some (.mma d P)) := Rd.wAt_of_st k (by omega) hσ
  have hin : ∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧
      Mma.Inv d' ∧ d'.site ≠ .setMaxRegInc := by
    intro j hj1 hj2
    obtain ⟨dj, hdj, hI, hne⟩ := hch j hj1 hj2
    exact ⟨dj, Rd.wAt_of_st j (by omega) hdj, hI, hne⟩
  obtain ⟨hT, hend, hin'⟩ := SO.mma_exec_run hpre hw hg hX hk0 h0w hdw hin
  refine ⟨fun b hb => ?_, fun hlead hbc => ⟨fun b hb => ?_, ?_⟩⟩
  · have h := SO.mma_pPolls hpre hg hT hin' hend hb
    have hz : SO.Mm.pPolled d0 = 0 := by simp [SO.Mm.pPolled, hs0]
    rw [hz, SO.below2_zero, Nat.add_zero] at h
    unfold okPolls at h ⊢
    rw [Ring.countP_take_split _ _ hk0, h]
    have := mma_fresh_polls hpre hX hf hR (by omega) h0 hs0 hb
    unfold okPolls at this
    rw [this, Nat.zero_add]
  · have h := SO.mma_sCommits hpre hg hT (SO.mma_exec_lead hg hX hk0 hk hlead hbc) hin' hend hb
    have hz : SO.Mm.qkDone d0 = 0 := by simp [SO.Mm.qkDone, hs0]
    rw [hz, SO.below2_zero, Nat.add_zero] at h
    rw [Ring.countP_take_split _ _ hk0, h,
      Rd.mma_fresh hpre hX hf hR hg (by omega) h0 hs0, Nat.zero_add]
  · have h := SO.mma_oCommits hpre hg hT (SO.mma_exec_lead hg hX hk0 hk hlead hbc) hin' hend
    have hz : SO.Mm.oDoneC d0 = 0 := by simp [SO.Mm.oDoneC, hs0]
    rw [hz, Nat.add_zero] at h
    rw [Ring.countP_take_split _ _ hk0, h,
      Rd.mma_fresh hpre hX hf hR hg (by omega) h0 hs0, Nat.zero_add]

omit hpre hX hf in
/-- An election property of the whole trace holds for a prefix. -/
theorem electLead_take {es : List Event} (h : ElectLead L g es) (k : Nat) :
    ElectLead L g (es.take k) :=
  fun e he => h e (List.mem_of_mem_take he)

/-- The event at an MMA state at a QK or PV step: an MMA with the state's shape, by the
committing lane of its CTA. -/
theorem mma_at_state (hg : g < L.threads) {k : Nat} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hs : (∃ j, d.site = .qk j) ∨ ∃ j, d.site = .pv j) :
    ∃ e, X.get (g, k) = some e ∧ EvW.MmShape L g d e ∧ g = cmOf L X (g / L.block) := by
  obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨pc, dst, sp, acc, mask, rfl⟩ := mma_issue_event hpre hX hf hg he hσ hs
  obtain ⟨d', P', hσ', hsh⟩ :=
    mma_event_state hpre hX hf.sound hf.tracked hg he (.inl ⟨_, _, _, _, rfl⟩)
  rw [hσ] at hσ'
  simp only [Option.some.injEq, TSt.w.injEq, WComp.WSt.mma.injEq] at hσ'
  obtain ⟨rfl, rfl⟩ := hσ'
  exact ⟨_, he, hsh, mma_cm hpre hX hf (x := (g, k)) ⟨dst, sp, acc, mask, pc, he⟩ rfl⟩

/-- **The event at a QK step is a QK MMA of its iteration's block, with `Sr.QkAt`'s counts.** -/
theorem qkAt_of (hR : RoleReads L X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X)
    (hB : Mma.MmaBcast L X) (hg : g < L.threads) {k : Nat} {j : Fin 8} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hs : d.site = .qk j) :
    Sr.QkAt L X (g / L.block) (cmOf L X (g / L.block)) (tmOf (g / L.block)) (g, k) d.i := by
  obtain ⟨e, he, hsh, hcm⟩ := mma_at_state hpre hX hf hg hk hσ (.inl ⟨j, hs⟩)
  have htm : d.tm = 0 := mma_tm hpre hX hf hb hn (m := (g, k)) ⟨P, hσ⟩
  have hlead := electLead_take (lead_of_qk hX j.val rfl hk hσ hs) k
  obtain ⟨hP, hC⟩ := mma_cnt hpre hX hf hR hg hk hσ
  obtain ⟨hS, hO⟩ := hC hlead ((bcast_of_mma hf.roleWarp hB hg hk.le hσ).take k)
  have hb2 : d.i % 2 < 2 := Nat.mod_lt _ (by omega)
  refine ⟨hcm, ⟨j, d.site.pc, e, he, ?_⟩, ?_, ?_, ?_⟩
  · have h := hsh
    unfold EvW.MmShape at h
    simp only [hs] at h
    rw [htm] at h
    rw [hs]
    unfold tmOf
    exact h
  · show List.countP _ ((X.tr (cmOf L X (g / L.block))).take k) ≤ _
    rw [← hcm, hS _ hb2]
    simp only [SO.Mm.qkDone, hs, SO.below2]
    omega
  · show _ ≤ okPolls _ ((X.tr (cmOf L X (g / L.block))).take k)
    rw [← hcm, hP _ hb2]
    simp only [SO.Mm.pPolled, hs, SO.below2]
    omega
  · show _ ≤ List.countP _ ((X.tr (cmOf L X (g / L.block))).take k)
    rw [← hcm, hO]
    simp [SO.Mm.oDoneC, hs]

/-- **The event at a PV step is a PV MMA of the previous block, with `Sr.PvAt`'s counts.** -/
theorem pvAt_of (hR : RoleReads L X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X)
    (hB : Mma.MmaBcast L X) (hg : g < L.threads) {k : Nat} {j : Fin 8} {d : Mma.D} {P : Loader.Pro}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hs : d.site = .pv j) :
    1 ≤ d.i ∧
      Sr.PvAt L X (g / L.block) (cmOf L X (g / L.block)) (tmOf (g / L.block)) (g, k) (d.i - 1) := by
  obtain ⟨e, he, hsh, hcm⟩ := mma_at_state hpre hX hf hg hk hσ (.inr ⟨j, hs⟩)
  have htm : d.tm = 0 := mma_tm hpre hX hf hb hn (m := (g, k)) ⟨P, hσ⟩
  have hI := mma_inv_at hX hf hk hσ
  have h1 : 1 ≤ d.i := (hI.pv (by rw [hs]; trivial)).1
  have hlead := electLead_take (lead_of_pv hX j.val rfl hk hσ hs) k
  obtain ⟨hP, hC⟩ := mma_cnt hpre hX hf hR hg hk hσ
  obtain ⟨hS, hO⟩ := hC hlead ((bcast_of_mma hf.roleWarp hB hg hk.le hσ).take k)
  have hb2 : (d.i - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  refine ⟨h1, hcm, ⟨j, d.site.pc, e, j.isLt, he, ?_⟩, ?_, ?_, ?_⟩
  · have h := hsh
    unfold EvW.MmShape at h
    simp only [hs] at h
    rw [htm] at h
    rw [hs]
    have hi : d.i - 1 + 1 = d.i := by omega
    unfold tmOf
    rw [hi]
    exact h
  · show List.countP _ ((X.tr (cmOf L X (g / L.block))).take k) ≤ _
    rw [← hcm, hS _ hb2]
    simp only [SO.Mm.qkDone, hs, SO.below2]
    have := Nat.min_le_left (d.i + 1) d.n
    omega
  · intro b hb
    show _ ≤ okPolls _ ((X.tr (cmOf L X (g / L.block))).take k)
    rw [← hcm, hP _ hb]
    simp only [SO.Mm.pPolled, hs, SO.below2]
    omega
  · show List.countP _ ((X.tr (cmOf L X (g / L.block))).take k) ≤ _
    rw [← hcm, hO]
    simp [SO.Mm.oDoneC, hs]

end
end PTX.Kernels.InklingRelDecode.Proof.Hs
