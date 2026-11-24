-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerContinuation
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0MaxTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0StateFields

@[expose] public section

/-! # Each packed score pair comes from the actual two peer reads of its group -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ScoreSumsHistory

open PTX PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def First (q d : D) (group : Fin 8) (word : Value) : Prop :=
  q.sub = 0 ∧ d.site = .peerRead group ∧ d.sub = 1 ∧
    d.peerPending = [word] ∧ d.scoreSums = q.scoreSums

private def Second (q d : D) (group : Fin 8) (word : Value) : Prop :=
  q.sub ≠ 0 ∧ d.sub = 0 ∧
    (if h : group.val + 1 < 8 then d.site = .peerRead ⟨group.val + 1, h⟩
      else d.site = .rowMax) ∧
    ∃ first left right, q.peerPending = [first] ∧
      peerAddE (ownScorePair q (2 * group.val)) first = .ok left ∧
      peerAddE (ownScorePair q (2 * group.val + 1)) word = .ok right ∧
      d.scoreSums = Function.update (Function.update q.scoreSums (2 * group.val) left)
        (2 * group.val + 1) right

private theorem peer_step {g : Nat} {q d : D} {group : Fin 8} {e : Event}
    (hs : q.site = .peerRead group)
    (hn : Machine.next P L g (.wg0 q) e = some (some (.wg0 d))) :
    q.block = d.block ∧ q.ownScores = d.ownScores ∧ q.maskWord = d.maskWord ∧
      ∃ access bytes word, e.kind = .rd access bytes ∧ rebuild 3 bytes = .ok word ∧
        (First q d group word ∨ Second q d group word) := by
  simp only [Machine.next] at hn
  split at hn
  · rename_i d' hnext
    cases hn
    simp only [Wg0.next, nextSite, hs] at hnext
    split at hnext
    · rename_i a bytes hKind
      split at hnext
      · split at hnext
        · rename_i word hRebuild
          split at hnext
          · rename_i hSub
            cases hnext
            exact ⟨rfl, rfl, rfl, a, bytes, word, hKind, hRebuild,
              .inl ⟨hSub, rfl, rfl, rfl, rfl⟩⟩
          · rename_i hSub
            split at hnext
            · rename_i first hPending
              split at hnext
              · rename_i left right hLeft hRight
                split at hnext
                · rename_i hMore
                  cases hnext
                  exact ⟨rfl, rfl, rfl, a, bytes, word, hKind, hRebuild,
                    .inr ⟨hSub, rfl, by rw [dite_eq_left hMore], first, left, right, hPending,
                      hLeft, hRight, rfl⟩⟩
                · rename_i hLast
                  split at hnext
                  · cases hnext
                    exact ⟨rfl, rfl, rfl, a, bytes, word, hKind, hRebuild,
                      .inr ⟨hSub, rfl, by rw [dite_eq_right hLast], first, left, right, hPending,
                        hLeft, hRight, rfl⟩⟩
                  · cases hnext
              · cases hnext
            · cases hnext
        · cases hnext
      · cases hnext
    · cases hnext
  · split_ifs at hn <;> cases hn
  · cases hn

private theorem before_peer {g i : Nat} {d : D} {group : Fin 8}
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) :
    ∃ j e q, j + 1 = i ∧ X.get (g, j) = some e ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) ∧
      Machine.next P L g (.wg0 q) e = some (some (.wg0 d)) ∧
      ((q.site = .pairBar ∧ group = 0 ∧ d.sub = q.sub) ∨ ∃ j, q.site = .peerRead j) := by
  cases i with
  | zero => rw [Frame.stateAt_zero] at hd; cases hd
  | succ j =>
    have hlen : j < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hlen⟩
    obtain ⟨s, hs⟩ := FollowedPrefix.state_at hd (Nat.le_succ j)
    have hn := Frame.stateAt_succ (C := Machine.code P L) he
    rw [hd, hs] at hn
    obtain ⟨q, rfl, hprev⟩ := composed_peer_predecessor hn.symm hsite
    exact ⟨j, e, q, rfl, he, hs, hn.symm, hprev⟩

private theorem before_second {g i : Nat} {q : D} {group : Fin 8}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hi : i ≤ (X.tr g).length)
    (hq : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 q)))
    (hsite : q.site = .peerRead group) (hSub : q.sub ≠ 0) :
    ∃ j r a bs word, j + 1 = i ∧ X.Reads (g, j) a bs ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 r)) ∧
      r.site = .peerRead group ∧ r.sub = 0 ∧ r.block = q.block ∧
      rebuild 3 bs = .ok word ∧ q.peerPending = [word] := by
  obtain ⟨j, e, r, hj, he, hr, hn, hprev⟩ := before_peer hi hq hsite
  rcases hprev with ⟨hb, _, hqr⟩ | ⟨prev, hPrev⟩
  · obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hr
    have hInv' : Wg0.Inv P L g r := hInv
    have hsub := hInv'.subLt
    rw [hb] at hsub
    change r.sub < 1 at hsub
    exact (hSub (by omega)).elim
  · obtain ⟨hblock, _, _, a, bs, word, hkind, hword, hstep | hstep⟩ := peer_step hPrev hn
    · obtain ⟨hrSub, hqsite, _, hp, _⟩ := hstep
      have heq : prev = group := Site.peerRead.inj (hqsite.symm.trans hsite)
      have hRead : X.Reads (g, j) a bs := ⟨e.pc, he.trans (by cases e; cases hkind; rfl)⟩
      exact ⟨j, r, a, bs, word, hj, hRead, hr, hPrev.trans (congrArg Site.peerRead heq),
        hrSub, hblock, hword, hp⟩
    · exact (hSub hstep.2.1).elim

/-- A packed pair retains the exact read operand and local addition of its own peer element. -/
def PairFromPeerReads (P : Params) (L : Launch) (X : Execution) (g stop block : Nat)
    (k : Fin 16) (result : Value) : Prop :=
  ∃ j q r a0 a1 bs0 bs1 first second, j + 1 < stop ∧
    Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 r)) ∧
    Frame.stateAt (Machine.code P L) X g (j + 1) = some (some (.wg0 q)) ∧
    r.site = .peerRead ⟨k.val / 2, by omega⟩ ∧ q.site = .peerRead ⟨k.val / 2, by omega⟩ ∧
    r.sub = 0 ∧ q.sub = 1 ∧ r.block = block ∧ q.block = block ∧
    X.Reads (g, j) a0 bs0 ∧ X.Reads (g, j + 1) a1 bs1 ∧
    rebuild 3 bs0 = .ok first ∧ rebuild 3 bs1 = .ok second ∧
    peerAddE (ownScorePair q k.val) (if k.val % 2 = 0 then first else second) = .ok result

private theorem PairFromPeerReads.mono {g stop next block : Nat} {k : Fin 16} {value : Value}
    (h : PairFromPeerReads P L X g stop block k value) (hle : stop ≤ next) :
    PairFromPeerReads P L X g next block k value := by
  obtain ⟨j, q, r, a0, a1, bs0, bs1, word0, word1, hj, h⟩ := h
  exact ⟨j, q, r, a0, a1, bs0, bs1, word0, word1, Nat.lt_of_lt_of_le hj hle, h⟩

private theorem second_pair_history {g j : Nat} {q d : D} {group : Fin 8} {k : Fin 16}
    {a : Acc} {bs : List (Option Byte)} {word : Value}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hread : X.Reads (g, j) a bs) (hword : rebuild 3 bs = .ok word)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)))
    (hsite : q.site = .peerRead group) (hb : q.block = d.block)
    (hstep : Second q d group word) (hk : k.val / 2 = group.val) :
    PairFromPeerReads P L X g (j + 1) d.block k (d.scoreSums k.val) := by
  obtain ⟨hNonzero, _, _, first, left, right, hp, hl, hr, hSums⟩ := hstep
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hread.choose_spec hq
  have hInv' : Inv P L g q := hInv
  have hBound := hInv'.subLt
  rw [hsite] at hBound
  change q.sub < 2 at hBound
  have hSub : q.sub = 1 := by omega
  obtain ⟨t, prev, a0, bs0, w, htj, hFirst, hPrev, hPrevSite,
    hPrevSub, hPrevBlock, hRebuild, hPending⟩ :=
    before_second hX hs (PTX.len_of_get hread.choose_spec).le hq hsite hNonzero
  have hFirstWord : w = first := List.cons.inj (hPending.symm.trans hp) |>.1
  subst w
  have hGroup : group = ⟨k.val / 2, by omega⟩ := Fin.ext hk.symm
  refine ⟨t, q, prev, a0, a, bs0, bs, first, word, by omega, hPrev, ?_,
    hPrevSite.trans (congrArg Site.peerRead hGroup), hsite.trans (congrArg Site.peerRead hGroup),
    hPrevSub, hSub, hPrevBlock.trans hb, hb, hFirst, ?_, hRebuild, hword, ?_⟩
  · rwa [htj]
  · rwa [htj]
  rw [hSums]
  by_cases heven : k.val % 2 = 0
  · have hk0 : k.val = 2 * group.val := by omega
    rw [ite_eq_left heven, hk0,
      Function.update_of_ne (by omega : 2 * group.val ≠ 2 * group.val + 1), Function.update_self]
    exact hl
  · have hk1 : k.val = 2 * group.val + 1 := by omega
    rw [ite_eq_right heven, hk1, Function.update_self]
    exact hr

private theorem earlier_pair_before_peer
    {g i : Nat} {d : D} {group : Fin 8} {k : Fin 16}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .peerRead group) (hk : k.val / 2 < group.val) :
    PairFromPeerReads P L X g i d.block k (d.scoreSums k.val) := by
  obtain ⟨j, e, q, hj, he, hq, hn, hPrev⟩ := before_peer hi hd hsite
  have hlen : j ≤ (X.tr g).length := (PTX.len_of_get he).le
  rcases hPrev with ⟨_, hzero, _⟩ | ⟨prev, hPrev⟩
  · have : group.val = 0 := congrArg Fin.val hzero
    omega
  obtain ⟨hb, _, _, a, bs, word, hKind, hWord, hStep | hStep⟩ := peer_step hPrev hn
  · obtain ⟨_, hdSite, _, _, hSums⟩ := hStep
    have hEq : prev = group := Site.peerRead.inj (hdSite.symm.trans hsite)
    rw [← hEq] at hk
    have hPast := earlier_pair_before_peer hX hs hlen hq hPrev hk
    rw [hSums, ← hb]
    exact hPast.mono (by omega)
  · have hCopy := hStep
    obtain ⟨_, _, hNext, _, left, right, _, _, _, hSums⟩ := hStep
    split at hNext
    · have hEq : group.val = prev.val + 1 :=
        congrArg Fin.val (Site.peerRead.inj (hsite.symm.trans hNext))
      by_cases h : k.val / 2 = prev.val
      · rw [← hj]
        exact second_pair_history hX hs
          ⟨e.pc, he.trans (by cases e; cases hKind; rfl)⟩ hWord hq hPrev hb hCopy h
      · have hk' : k.val / 2 < prev.val := by omega
        have hPast := earlier_pair_before_peer hX hs hlen hq hPrev hk'
        rw [hSums, Function.update_of_ne (by omega : k.val ≠ 2 * prev.val + 1),
          Function.update_of_ne (by omega : k.val ≠ 2 * prev.val), ← hb]
        exact hPast.mono (by omega)
    · rw [hsite] at hNext
      cases hNext
termination_by i
decreasing_by all_goals omega

variable {g i : Nat} {d : D} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hg : g < L.threads)
    (hi : i ≤ (X.tr g).length) (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
include hX hs hg hi hd

/-- The local maximum state carries all sixteen pairs produced by its completed peer exchange. -/
theorem pairs_at_rowMax (hsite : d.site = .rowMax) (k : Fin 16) :
    PairFromPeerReads P L X g i d.block k (d.scoreSums k.val) := by
  obtain ⟨j, e, q, hj, he, hq, hPrev⟩ := Wg0MaxTrace.peer_before_rowMax hX hs hg hi hd hsite
  rw [← hj, Frame.stateAt_succ he, hq] at hd
  have hn : Machine.next P L g (.wg0 q) e = some (some (.wg0 d)) := hd
  obtain ⟨hb, _, _, a, bs, word, hKind, hWord, hStep | hStep⟩ := peer_step hPrev hn
  · cases hsite.symm.trans hStep.2.1
  · by_cases h : k.val / 2 = (7 : Fin 8).val
    · rw [← hj]
      exact second_pair_history hX hs
        ⟨e.pc, he.trans (by cases e; cases hKind; rfl)⟩ hWord hq hPrev hb hStep h
    · obtain ⟨_, _, _, _, left, right, _, _, _, hSums⟩ := hStep
      have hk := k.isLt
      have hk' : k.val / 2 < (7 : Fin 8).val := by omega
      have hPast := earlier_pair_before_peer hX hs (PTX.len_of_get he).le hq hPrev hk'
      rw [hSums, Function.update_of_ne (by omega : k.val ≠ 2 * (7 : Fin 8).val + 1),
        Function.update_of_ne (by omega : k.val ≠ 2 * (7 : Fin 8).val), ← hb]
      exact hPast.mono (by omega)

omit hX hs hg hi hd in
private theorem block_of_max_transition {g : Nat} {q d : D} {e : Event}
    (hsite : q.site = .maxRead)
    (hn : Machine.next P L g (.wg0 q) e = some (some (.wg0 d))) :
    q.block = d.block := by
  simp only [Machine.next] at hn
  split at hn
  · rename_i v hNext
    cases hn
    simp only [Wg0.next, nextSite, hsite] at hNext
    split at hNext
    · split at hNext
      · obtain ⟨_, _, hMap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hNext)
        obtain ⟨_, hPeer, rfl⟩ := Option.map_eq_some_iff.mp hMap
        exact (peer_preserves_sub hPeer).1.symm
      · cases hNext
    · cases hNext
  · split_ifs at hn <;> cases hn
  · cases hn

/-- The vote still contains each exact local sum of the actual two peer reads of its block. -/
theorem pairs_at_vote (hsite : d.site = .rescaleVote) (k : Fin 16) :
    PairFromPeerReads P L X g i d.block k (d.scoreSums k.val) := by
  obtain ⟨j, e, q, hj, he, hq, hMax, hSums⟩ := Wg0MaxTrace.maxRead_before_vote hX hs hg hi hd hsite
  have hn : Machine.next P L g (.wg0 q) e = some (some (.wg0 d)) := by
    rw [← hj, Frame.stateAt_succ he, hq] at hd
    exact hd
  have hBlock := block_of_max_transition hMax hn
  obtain ⟨w, r, hw, hr, hrSite, hrBlock, hRows⟩ :=
    Wg0MaxTrace.rowMax_state_before_maxRead hX hs hg (PTX.len_of_get he).le hq hMax
  have hlen : w ≤ (X.tr g).length := by omega
  have before := pairs_at_rowMax hX hs hg hlen hr hrSite k
  rw [hSums, hRows, ← hBlock, ← hrBlock]
  exact before.mono (by omega)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0ScoreSumsHistory
