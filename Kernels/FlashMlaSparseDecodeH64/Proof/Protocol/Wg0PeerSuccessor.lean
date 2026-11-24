-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerReadback
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerContinuation
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

@[expose] public section

/-! # Actual continuation through the WG0 peer exchange -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerSuccessor

open PTX PTX.Flow PTX.Proof Wg0 MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat}
variable {d : D} {e : Event} {group : Fin 8}

/-- The actual score-result handoff establishes real words on the lane that stored each group. -/
def PeerScoresReal (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g i (d : D) (group : Fin 8),
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) →
    d.site = .exchStore group → RealScores d.peerScores

/-- The lane's own QK half remains real while its peer exchange is in progress. -/
def OwnScoresReal (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g i (d : D) (group : Fin 8),
    Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)) →
    d.site = .peerRead group → RealScores d.ownScores

private theorem read_event (he : X.get (g, i) = some e) {a : Acc} {bytes : List (Option Byte)}
    (hk : e.kind = .rd a bytes) : X.Reads (g, i) a bytes := by
  cases e
  exact ⟨_, he.trans (congrArg some (congrArg (Event.mk _) hk))⟩

/-- Either the event ends the concrete lane or it advances the same score block.
Both pending and completed values are available to the next peer element. -/
theorem actual_next {cut : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hreal : PeerScoresReal P L X) (hown : RealScores d.ownScores)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) (hp : PeerPrefix d group)
    (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t) :
    Machine.next P L g (.wg0 d) e = none ∨
      ∃ d', Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
        d'.block = d.block ∧
        ((∃ nextGroup : Fin 8, d'.site = .peerRead nextGroup ∧ PeerPrefix d' nextGroup ∧
            2 * nextGroup.val + d'.sub = 2 * group.val + d.sub + 1) ∨
          (d'.site = .rowMax ∧ 2 * group.val + d.sub + 1 = 16 ∧
            ∀ j < 16, MaskedPair (d'.scoreSums j))) := by
  obtain ⟨o, hf⟩ := (Frame.trace hs hX (Frame.lt_of_get hX he)).fired_at he hd
  cases o with
  | none => exact .inl (composed_ending_next hf)
  | some u =>
    obtain ⟨a, bytes, hk, ha, hz, hsub⟩ := composed_peer_geometry hpre hsite hf
    obtain ⟨j, q, _, hq, hqs, _, _, hread, _⟩ :=
      Wg0PeerReadback.actual_readback_value hpre hX hs (read_event he hk) hd hsite
        hCut hLen hPrior
    have hv := peerReadValue_real (hreal _ j q group hq hqs) group hsub
    by_cases h0 : d.sub = 0
    · have hnext := composed_peerFirst_ready (P := P) hsite h0 hk ha hz hread
      exact .inr ⟨_, hnext, rfl, .inl ⟨group, hsite, peerPrefix_first hp hv, by simp [h0]⟩⟩
    · obtain ⟨d', hn, hb, hSub', hresult⟩ := composed_peerSecond_next hpre hsite (by omega)
        hk ha hz hread hown hp hv
      refine .inr ⟨d', hn, hb, ?_⟩
      rcases hresult with ⟨j', hj', hgroup, hp'⟩ | ⟨hrow, hlast, hm⟩
      · exact .inl ⟨j', hj', hp', by omega⟩
      · exact .inr ⟨hrow, by omega, hm⟩

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
include hpre hX hs

/-- The peer successor in a globally tracked execution. -/
theorem next (ht : Frame.Tracked (Machine.code P L) X) (hreal : PeerScoresReal P L X)
    (hown : RealScores d.ownScores) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) (hp : PeerPrefix d group) :
    Machine.next P L g (.wg0 d) e = none ∨
      ∃ d', Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
        d'.block = d.block ∧
        ((∃ nextGroup : Fin 8, d'.site = .peerRead nextGroup ∧ PeerPrefix d' nextGroup ∧
            2 * nextGroup.val + d'.sub = 2 * group.val + d.sub + 1) ∨
          (d'.site = .rowMax ∧ 2 * group.val + d.sub + 1 = 16 ∧
            ∀ j < 16, MaskedPair (d'.scoreSums j))) :=
  actual_next hpre hX hs hreal hown he hd hsite hp le_rfl (PTX.len_of_get he)
    (fun t _ => tracked_not_dismisses hX ht t)

omit hpre hX hs in
/-- Every reached peer state gets its pending value and completed pairs from the actual earlier
reads of that exchange. The pair barrier starts a new set of completed sums. -/
theorem actual_prefix_at {cut : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hpeer : PeerScoresReal P L X) (hown : OwnScoresReal P L X)
    (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ Dismisses P L X t)
    (hCut : i ≤ cut)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) : PeerPrefix d group := by
  induction i generalizing d group with
  | zero =>
    rw [Frame.stateAt_zero] at hd
    cases hd
  | succ k ih =>
    have hk : k < (X.tr g).length := by omega
    obtain ⟨ev, hev⟩ : ∃ ev, X.get (g, k) = some ev := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨σ, hσ⟩ := FollowedPrefix.state_at hd (Nat.le_succ k)
    rw [Frame.stateAt_succ hev, hσ, Option.bind_some] at hd
    change Machine.next P L g σ ev = some (some (.wg0 d)) at hd
    obtain ⟨q, rfl, hprev⟩ := composed_peer_predecessor hd hsite
    rcases hprev with ⟨hbar, rfl, hsub⟩ | ⟨j, hj⟩
    · obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hev hσ
      have hq : Inv P L g q := hInv
      have hz := hq.subLt
      rw [hbar] at hz
      change q.sub < 1 at hz
      exact ⟨fun h => by omega, fun j hj => by omega⟩
    · have hEarlier : k ≤ cut := by omega
      have hp := ih hEarlier hσ hj
      rcases actual_next hpre hX hs hpeer (hown g k q j hσ hj) hev hσ hj hp
        hEarlier hLen hPrior with
        hdead | ⟨r, hr, _, hafter⟩
      · rw [hdead] at hd
        cases hd
      · rw [hr] at hd
        have heq := Machine.ThreadD.wg0.inj (Option.some.inj (Option.some.inj hd))
        subst r
        rcases hafter with ⟨nextGroup, hn, hp', _⟩ | ⟨hrow, _, _⟩
        · have heq := Site.peerRead.inj (hsite.symm.trans hn)
          subst nextGroup
          exact hp'
        · rw [hrow] at hsite
          cases hsite

/-- The peer prefix at a tracked state, including the end of a prefix. -/
theorem prefix_at (ht : Frame.Tracked (Machine.code P L) X) (hpeer : PeerScoresReal P L X)
    (hown : OwnScoresReal P L X) (hlen : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) : PeerPrefix d group := by
  induction i generalizing d group with
  | zero =>
    rw [Frame.stateAt_zero] at hd
    cases hd
  | succ k ih =>
    have hk : k < (X.tr g).length := by omega
    obtain ⟨ev, hev⟩ : ∃ ev, X.get (g, k) = some ev := ⟨_, List.getElem?_eq_getElem hk⟩
    have hg := Frame.lt_of_get hX hev
    obtain ⟨σ, hσ⟩ := Frame.stateAt_live ht hg hd (Nat.le_succ k)
    rw [Frame.stateAt_succ hev, hσ, Option.bind_some] at hd
    change Machine.next P L g σ ev = some (some (.wg0 d)) at hd
    obtain ⟨q, rfl, hprev⟩ := composed_peer_predecessor hd hsite
    rcases hprev with ⟨hbar, rfl, hsub⟩ | ⟨j, hj⟩
    · obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hev hσ
      have hq : Inv P L g q := hInv
      have hz := hq.subLt
      rw [hbar] at hz
      change q.sub < 1 at hz
      exact ⟨fun h => by omega, fun j hj => by omega⟩
    · have hp := ih (Nat.le_of_lt hk) hσ hj
      rcases next hpre hX hs ht hpeer (hown g k q j hσ hj) hev hσ hj hp with
        hdead | ⟨r, hr, _, hafter⟩
      · rw [hdead] at hd
        cases hd
      · rw [hr] at hd
        have heq := Machine.ThreadD.wg0.inj (Option.some.inj (Option.some.inj hd))
        subst r
        rcases hafter with ⟨nextGroup, hn, hp', _⟩ | ⟨hrow, _, _⟩
        · have heq := Site.peerRead.inj (hsite.symm.trans hn)
          subst nextGroup
          exact hp'
        · rw [hrow] at hsite
          cases hsite

/-- The actual peer reads preserve tracking using the predecessors of the current event. -/
theorem actual_never_dismiss (hpeer : PeerScoresReal P L X) (hown : OwnScoresReal P L X)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group)
    (hPrior : ∀ t, baseCausality L X t (g, i) → ¬ Dismisses P L X t) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  have hLen := PTX.len_of_get he
  have hp := actual_prefix_at hpre hX hs hpeer hown hLen hPrior le_rfl hd hsite
  rcases actual_next hpre hX hs hpeer (hown g i d group hd hsite) he hd hsite hp
    le_rfl hLen hPrior with hdead | ⟨_, hn, _⟩
  · simp [hdead]
  · simp [hn]

/-- Neither of the two peer reads discards a followed role once the QK score loads are identified.
The last second element also produces all sixteen pairs consumed by the row-max write. -/
theorem never_dismiss (ht : Frame.Tracked (Machine.code P L) X) (hpeer : PeerScoresReal P L X)
    (hown : OwnScoresReal P L X) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) :
    Machine.next P L g (.wg0 d) e ≠ some none := by
  have hp := prefix_at hpre hX hs ht hpeer hown (Nat.le_of_lt (PTX.len_of_get he)) hd hsite
  rcases next hpre hX hs ht hpeer (hown g i d group hd hsite) he hd hsite hp with
    hdead | ⟨_, hn, _⟩
  · rw [hdead]
    intro h
    cases h
  · rw [hn]
    intro h
    cases h

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerSuccessor
