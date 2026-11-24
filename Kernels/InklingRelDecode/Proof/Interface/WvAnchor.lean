-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpCount
public import Kernels.InklingRelDecode.Proof.Protocol.HsMma

@[expose] public section

/-!
# The MMA lane's counts at the end of its trace

`Lp.mma_anchor_full` and `Hs.mma_cnt` read the MMA lane's counts at a state before an event
(`k < length`). The progress layer needs them at the state after the last event, `k = length`.
Every MMA state but the entry `setMaxReg` follows an MMA state at the previous event
(`mma_pred_le`), which has an event, so its anchored run extends by one step (`mma_anchor_le`):

* `mma_polls_le`: the successful polls of `p_ready b` and of `kv_ready s` before the state are
  `below2 b (pPolled d)` and `below s (polled d)`;
* `mma_commits_le`: if every election of the thread so far returned its lane, the commits to
  `s_ready b`, `o_done` and `o_final` are `below2 b (qkDone d)`, `oDoneC d` and `finDone d`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (sReady pReady oDone oFinal kvReady kvEmpty)
open PTX.Kernels.InklingRelDecode.Proof.Ring (wAt)
open PTX.Kernels.InklingRelDecode.Proof.SO (below2)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The state before an MMA state at an index up to the trace's length.** Like
`Interface.mma_state_pred_adj`, for `k ≤ length`. -/
theorem mma_pred_le (hX : Consistent L kernel asms mem0 X) {k : Nat} {d : Mma.D}
    {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site ≠ .setMaxReg) :
    ∃ (k0 : Nat) (e : Event) (d0 : Mma.D), k0 + 1 = k ∧ g < L.threads ∧
      X.get (g, k0) = some e ∧ St Q L X g k0 = some (some (.w (.mma d0 P))) ∧
      Mma.next L g d0 e = some (some d) := by
  have hk1 : k ≠ 0 := by
    rintro rfl
    have h0 := hσ
    rw [St, Frame.stateAt_zero] at h0
    exact mma_ne_init d P (Option.some.inj (Option.some.inj h0)).symm
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
      have hn : (threadCode L g Q).next s0 e = some (some (.w (.mma d P))) := hs'
      cases s0 with
      | d s =>
        rw [next_d] at hn
        obtain ⟨a, -, h⟩ := map_map_eq_some_some hn
        cases h
      | w s =>
        rw [next_w] at hn
        obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
        cases h
        obtain ⟨d0, rfl, hd0⟩ := wcomp_next_mma ha hs
        have hge : X.get (g, k0) = some e := he
        exact ⟨k0, e, d0, rfl, Frame.lt_of_get hX hge, hge, hk0, hd0⟩

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hR : RoleReads L X) {k : Nat} {d : Mma.D} {P : Loader.Pro} (hk : k ≤ (X.tr g).length)
include hpre hX hf hR hk

/-- **The anchored run of an MMA state at an index up to the trace's length**, with no poll and
no commit before the anchor. `Lp.mma_anchor_full` for `k ≤ length` and a state that is not the
entry. -/
theorem mma_anchor_le (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site ≠ .setMaxReg) :
    g < L.threads ∧ 4 ≤ WComp.warpOf L g ∧ ∃ (k0 : Nat) (d0 : Mma.D), k0 ≤ k ∧ k0 < k ∧
      wAt Q L X g k0 = some (some (.mma d0 P)) ∧ wAt Q L X g k = some (some (.mma d P)) ∧
      d0.site = .setMaxReg ∧
      (∀ j, k0 ≤ j → j < k → ∃ d', wAt Q L X g j = some (some (.mma d' P)) ∧ Mma.Inv d' ∧
        d'.site ≠ .setMaxRegInc) ∧
      (∀ m, ((X.tr g).take k0).countP (commitsTo m) = 0) ∧
      ∀ m, okPolls m ((X.tr g).take k0) = 0 := by
  obtain ⟨k1, e, d1, rfl, hg, he, hσ1, hn⟩ := mma_pred_le hX hk hσ hs
  have hk1 : k1 < (X.tr g).length := by omega
  obtain ⟨hw, k0, d0, hk0, h0, hd1, hs0, hin, hC, hP⟩ := Lp.mma_anchor_full hpre hX hf hR hk1 hσ1
  refine ⟨hg, hw, k0, d0, by omega, by omega, h0, Rd.wAt_of_st _ hk hσ, hs0, ?_, hC, hP⟩
  intro j hj1 hj2
  by_cases hj : j = k1
  · subst hj
    exact ⟨d1, hd1, mma_inv_at hX hf hk1 hσ1, (Rd.next_ne_setMaxReg hn).2⟩
  · exact hin j hj1 (by omega)

/-- **The MMA lane's successful polls at a state up to the trace's end.** -/
theorem mma_polls_le (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site ≠ .setMaxReg) :
    (∀ b < 2, okPolls (pReady L (g / L.block) b) ((X.tr g).take k) =
      below2 b (SO.Mm.pPolled d)) ∧
    ∀ s < 3, okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) =
      Ring.below s (Ring.Mm.polled d) := by
  obtain ⟨hg, hw, k0, d0, hk0, -, h0, hd, hs0, hin, -, hP⟩ :=
    mma_anchor_le hpre hX hf hR hk hσ hs
  obtain ⟨hT, hend, hin'⟩ := SO.mma_exec_run hpre hw hg hX hk0 h0 hd hin
  refine ⟨fun b hb => ?_, fun s hs3 => ?_⟩
  · have h := SO.mma_pPolls hpre hg hT hin' hend hb
    have hz : SO.Mm.pPolled d0 = 0 := by simp [SO.Mm.pPolled, hs0]
    rw [hz, SO.below2_zero, Nat.add_zero] at h
    unfold okPolls at h ⊢
    rw [Ring.countP_take_split _ _ hk0, h]
    have := hP (pReady L (g / L.block) b)
    unfold okPolls at this
    rw [this, Nat.zero_add]
  · have h := Ring.mma_polls hpre hg hT hin' hend hs3
    have hz : Ring.Mm.polled d0 = 0 := by simp [Ring.Mm.polled, hs0]
    rw [hz] at h
    have hb0 : Ring.below s 0 = 0 := by unfold Ring.below; omega
    rw [hb0, Nat.add_zero] at h
    unfold okPolls at h ⊢
    rw [Ring.countP_take_split _ _ hk0, h]
    have := hP (kvReady L (g / L.block) s)
    unfold okPolls at this
    rw [this, Nat.zero_add]

/-- **The MMA lane's commits at a state up to the trace's end**, when every election of the
thread returned its lane and no event of the thread ends it. -/
theorem mma_commits_le (hσ : St Q L X g k = some (some (.w (.mma d P)))) (hs : d.site ≠ .setMaxReg)
    (hlead : ElectLead L g (X.tr g)) (hbc : Mma.BcastRun (X.tr g)) (hne : ∀ e ∈ X.tr g, ¬ Ends e) :
    (∀ b < 2, ((X.tr g).take k).countP (commitsTo (sReady L (g / L.block) b)) =
      below2 b (SO.Mm.qkDone d)) ∧
    ((X.tr g).take k).countP (commitsTo (oDone L (g / L.block))) = SO.Mm.oDoneC d ∧
    ((X.tr g).take k).countP (commitsTo (oFinal L (g / L.block))) = SO.Mm.finDone d := by
  obtain ⟨hg, hw, k0, d0, hk0, -, h0, hd, hs0, hin, hC, -⟩ :=
    mma_anchor_le hpre hX hf hR hk hσ hs
  obtain ⟨hT, hend, hin'⟩ := SO.mma_exec_run hpre hw hg hX hk0 h0 hd hin
  have hE : ∀ e ∈ ((X.tr g).drop k0).take (k - k0), Ring.MmRun L g e := by
    intro e he
    have hmem : e ∈ X.tr g := List.mem_of_mem_drop (List.mem_of_mem_take he)
    exact ⟨⟨hne e hmem, hlead e hmem⟩, hbc e hmem⟩
  refine ⟨fun b hb => ?_, ?_, ?_⟩
  · have h := SO.mma_sCommits hpre hg hT hE hin' hend hb
    have hz : SO.Mm.qkDone d0 = 0 := by simp [SO.Mm.qkDone, hs0]
    rw [hz, SO.below2_zero, Nat.add_zero] at h
    rw [Ring.countP_take_split _ _ hk0, h, hC, Nat.zero_add]
  · have h := SO.mma_oCommits hpre hg hT hE hin' hend
    have hz : SO.Mm.oDoneC d0 = 0 := by simp [SO.Mm.oDoneC, hs0]
    rw [hz, Nat.add_zero] at h
    rw [Ring.countP_take_split _ _ hk0, h, hC, Nat.zero_add]
  · have h := SO.mma_fCommits hpre hg hT hE hin' hend
    have hz : SO.Mm.finDone d0 = 0 := by simp [SO.Mm.finDone, hs0]
    rw [hz, Nat.add_zero] at h
    rw [Ring.countP_take_split _ _ hk0, h, hC, Nat.zero_add]

end
end PTX.Kernels.InklingRelDecode.Proof.Wv
