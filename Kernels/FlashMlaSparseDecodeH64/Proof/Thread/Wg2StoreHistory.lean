-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Numeric
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Kernel.Frame
import Lemmas.Flow.Final

@[expose] public section

/-! # The exact sequence of tile writes before a dequantized-buffer publication -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2StoreHistory

open PTX PTX.Proof PTX.Flow Wg2 Wg2.Numeric

variable {P : Params} {L : Launch} {g : Nat}

/-- Stores are interleaved with raw-word loads. The last two stores of each row are consecutive. -/
def storeOrdinal (row : Fin 4) (step : Fin 8) : Nat :=
  20 * row.val + if step.val = 7 then 19 else 6 + 2 * step.val

private def ordinal : Wg2.Site → Option Nat
  | .scale r j => some (20 * r.val + j.val)
  | .raw r s => some (20 * r.val + if s.val = 0 then 4 else 3 + 2 * s.val)
  | .store r s => some (storeOrdinal r s)
  | .fence => some 80
  | .ready => some 81
  | _ => none

private theorem afterScale_ordinal (r j : Fin 4) :
    ordinal (afterScale r j) = some (20 * r.val + j.val + 1) := by
  unfold afterScale
  split_ifs with hj
  · simp [ordinal, Nat.add_assoc]
  · have h := j.isLt
    simp only [ordinal, ↓reduceIte, Option.some.injEq]
    omega

private theorem afterRaw_ordinal (r : Fin 4) (s : Fin 8) :
    ordinal (afterRaw r s) = (ordinal (.raw r s)).map (· + 1) := by
  unfold afterRaw
  split_ifs with hs
  · have he : s = 0 := Fin.ext hs
    simp [ordinal, he]
  · have hh := s.isLt
    have hne : s.val - 1 ≠ 7 := by omega
    simp only [ordinal, storeOrdinal, hne, hs, ↓reduceIte, Option.map_some, Option.some.injEq]
    omega

private theorem afterStore_ordinal (r : Fin 4) (s : Fin 8) :
    ordinal (Wg2.afterStore r s) = some (storeOrdinal r s + 1) := by
  unfold Wg2.afterStore
  have hr := r.isLt
  have hs := s.isLt
  split_ifs with h0 h1 h2
  · have hn : s.val ≠ 7 := by omega
    have hn' : s.val + 2 ≠ 0 := by omega
    simp only [ordinal, storeOrdinal, hn, hn', ↓reduceIte, Option.some.injEq]
    omega
  · have hn : s.val = 6 := by omega
    simp only [ordinal, storeOrdinal, hn]
    rfl
  · have hn : s.val = 7 := by omega
    simp only [ordinal, storeOrdinal, hn, ↓reduceIte,
      Option.some.injEq, Nat.add_zero]
    omega
  · have hn : s.val = 7 := by omega
    simp only [ordinal, storeOrdinal, hn, ↓reduceIte, Option.some.injEq]
    omega

private theorem store_bound (r : Fin 4) (s : Fin 8) : storeOrdinal r s < 80 := by
  have hr := r.isLt
  have hs := s.isLt
  unfold storeOrdinal
  split_ifs <;> omega

private theorem storeSite_of_ordinal (r : Fin 4) (s : Fin 8) {site : Wg2.Site}
    (h : ordinal site = some (storeOrdinal r s)) : site = .store r s := by
  have hr := r.isLt
  have hs := s.isLt
  have hm := store_bound r s
  cases site <;> simp only [ordinal, reduceCtorEq, Option.some.injEq] at h ⊢
  case scale r' j =>
    have hr' := r'.isLt
    have hj := j.isLt
    unfold storeOrdinal at h
    split_ifs at h <;> omega
  case raw r' s' =>
    have hr' := r'.isLt
    have hs' := s'.isLt
    unfold storeOrdinal at h
    split_ifs at h <;> omega
  case store r' s' =>
    have hr' := r'.isLt
    have hs' := s'.isLt
    unfold storeOrdinal at h
    apply congrArg₂ Wg2.Site.store <;> apply Fin.ext <;> split_ifs at h <;> omega
  all_goals omega

set_option maxHeartbeats 1000000 in
private theorem role_prev {d q : D} {e : Event} {n : Nat}
    (hn : Wg2.next P L g q e = some (some d)) (h : ordinal d.site = some (n + 1)) :
    ordinal q.site = some n ∧ q.block = d.block := by
  cases hq : q.site <;>
    simp only [Wg2.next, Wg2.nextSite, hq] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals try (dsimp only at h)
  all_goals
    first
    | rw [afterScale_ordinal] at h
      exact ⟨congrArg some (Nat.add_right_cancel (Option.some.inj h)), rfl⟩
    | rw [afterRaw_ordinal, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, he⟩ := h
      cases Nat.add_right_cancel he
      exact ⟨hv, rfl⟩
    | rw [afterStore_ordinal] at h
      exact ⟨congrArg some (Nat.add_right_cancel (Option.some.inj h)), rfl⟩
    | simp_all [ordinal, lenOrigNext, lenExtraNext, Wg2.init, Wg2.firstSite, afterFree]
  all_goals split_ifs at h

private theorem machine_prev {d : D} {q : Machine.ThreadD} {e : Event} {n : Nat}
    (hn : Machine.next P L g q e = some (some (.wg2 d))) (h : ordinal d.site = some (n + 1)) :
    ∃ q' : D, q = .wg2 q' ∧ ordinal q'.site = some n ∧ q'.block = d.block := by
  cases q with
  | wg2 q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i r hr
      cases hn
      exact ⟨q, rfl, role_prev hr h⟩
    · split_ifs at hn <;> cases hn
    · cases hn
  | prologue q =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          unfold Wg2.init Wg2.firstSite at h
          split_ifs at h <;> cases h
        · cases hn
      · cases hn
    · cases hn
  | head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  | _ =>
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

variable {X : Execution}

private theorem rewind {i b p n : Nat} {d : D} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))) (hBlock : d.block = b)
    (hOrd : ordinal d.site = some (p + n)) :
    ∃ j q, j + n = i ∧ q.block = b ∧ ordinal q.site = some p ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 q)) := by
  induction n generalizing i d with
  | zero => exact ⟨i, d, rfl, hBlock, hOrd, hd⟩
  | succ n ih =>
    cases i with
    | zero => rw [Frame.stateAt_zero] at hd; cases hd
    | succ i =>
      have hlt : i < (X.tr g).length := by omega
      obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
      rw [Frame.stateAt_succ he] at hd
      cases hq : Frame.stateAt (Machine.code P L) X g i with
      | none => simp [hq] at hd
      | some q =>
        rw [hq, Option.bind_some] at hd
        cases q with
        | none =>
          change (some none : Option (Option Machine.ThreadD)) = some (some (.wg2 d)) at hd
          cases hd
        | some q =>
          change Machine.next P L g q e = some (some (.wg2 d)) at hd
          obtain ⟨q', rfl, ho, hb⟩ := machine_prev hd hOrd
          obtain ⟨j, r, hj, hbr, hr, hsr⟩ :=
            ih (Nat.le_of_lt hlt) hq (hb.trans hBlock) ho
          exact ⟨j, r, by omega, hbr, hr, hsr⟩

/-- Every reached ready state has each specified row/step state at its exact distance
from publication, in the same block and the same lane. -/
theorem store_state_before_ready {i : Nat} {d : D} (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d))) (hsite : d.site = .ready)
    (r : Fin 4) (s : Fin 8) :
    ∃ j q, j + (81 - storeOrdinal r s) = i ∧ j < i ∧
      q.block = d.block ∧ q.site = .store r s ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 q)) := by
  have hb := store_bound r s
  have ho : ordinal d.site = some (storeOrdinal r s + (81 - storeOrdinal r s)) := by
    rw [hsite]
    change some 81 = some _
    congr 1
    omega
  obtain ⟨j, q, hj, hq, ho', hstate⟩ := rewind hi hd rfl ho
  exact ⟨j, q, hj, by omega, hq, storeSite_of_ordinal r s ho', hstate⟩

/-- A published buffer has an actual sixteen-byte store of each row and step, with its
executed state, source words, and address within the selected slot. -/
theorem store_before_ready {mem0 : Mem0} {X : Execution} {i : Nat} {d : D} {ready : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some ready)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hsite : d.site = .ready) (r : Fin 4) (s : Fin 8) :
    ∃ j q e u a, j + (81 - storeOrdinal r s) = i ∧ j < i ∧
      q.block = d.block ∧ q.site = .store r s ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 q)) ∧
      X.get (g, j) = some e ∧ (Machine.machine P L g).Fired (some (.wg2 q)) e (some u) ∧
      e.kind = .wr a (dequantChunk q.raw (byteAt q.sc (scaleIdx L g s.val))).toBytes ∧
      a.loc = ⟨.shared, ctaOf L g, L.sharedBase + tileBase (d.block % 2) +
        tileOff L g r.val s.val⟩ ∧ a.size = 16 := by
  have hi : i < (X.tr g).length := PTX.len_of_get he
  have hg := Frame.lt_of_get hX he
  obtain ⟨j, q, hdist, hj, hb, hqs, hq⟩ :=
    store_state_before_ready (Nat.le_of_lt hi) hd hsite r s
  have hjl : j < (X.tr g).length := by omega
  obtain ⟨e, hjGet⟩ : ∃ e, X.get (g, j) = some e := ⟨_, List.getElem?_eq_getElem hjl⟩
  obtain ⟨o, hf⟩ := (hs.produces (hX.thr g hg)).fired_at hjGet hq
  cases o with
  | none =>
    obtain ⟨_, hrun⟩ := hX.thr g hg
    obtain ⟨_, _, hFire⟩ := hf
    have hlast := Run.end_last hrun hjGet (fires_none_ends hFire)
    omega
  | some u =>
    have hRole : (Wg2.machine P L g).Fired (some (.inr q)) e (some u) := hf
    have hinv : Wg2.Inv P L g q := (Exists.choose_spec hRole).1.2
    obtain ⟨a, hKind, hLoc, hSize⟩ := fired_store_event hpre hqs hRole
    rw [hinv.bufBlock, hb] at hLoc
    exact ⟨j, q, e, u, a, hdist, hj, hb, hqs, hq, hjGet, hf, hKind, hLoc, hSize⟩

/-- A block spans 84 positions, from the raw-ready wait through the release that
hands off to the next block or the terminal barrier. Repeated polls preserve the position. -/
private def stamp (d : D) : Nat :=
  match d.site with
  | .lenOrig | .lenExtra | .qUtccp => 0
  | .free => 84 * d.block + 83
  | .barrier => 84 * d.block + 84
  | s => 84 * d.block + ((ordinal s).map (· + 1)).getD 0

private theorem stamp_of_ordinal {d : D} {n : Nat} (h : ordinal d.site = some n) :
    stamp d = 84 * d.block + (n + 1) := by
  cases hd : d.site <;> simp_all [stamp, ordinal]

private theorem stamp_after_ord_inc {d q : D} {n : Nat} (hb : q.block = d.block)
    (hq : ordinal q.site = some n) (hd : ordinal d.site = some (n + 1)) :
    stamp q ≤ stamp d ∧ ((∃ r s, q.site = .store r s) → stamp q < stamp d) := by
  rw [stamp_of_ordinal hq, stamp_of_ordinal hd, hb]
  exact ⟨by omega, fun _ => by omega⟩

set_option maxHeartbeats 1000000 in
private theorem role_stamp {q d : D} {e : Event}
    (hn : Wg2.next P L g q e = some (some d)) :
    stamp q ≤ stamp d ∧ ((∃ r s, q.site = .store r s) → stamp q < stamp d) := by
  cases hq : q.site <;>
    simp only [Wg2.next, Wg2.nextSite, hq] at hn
  case scale r j =>
    repeat' split at hn
    all_goals cases hn
    rw [← hq]
    refine stamp_after_ord_inc (n := 20 * r.val + j.val) ?_ ?_ ?_
    · rfl
    · rw [hq]; rfl
    · exact afterScale_ordinal r j
  case raw r k =>
    repeat' split at hn
    all_goals cases hn
    all_goals
      obtain ⟨n, hn⟩ : ∃ n, ordinal q.site = some n := ⟨_, by rw [hq]; rfl⟩
      have hInc := afterRaw_ordinal r k
      rw [← hq, hn, Option.map_some] at hInc
      rw [← hq]
      refine stamp_after_ord_inc ?_ hn ?_
      · rfl
      · exact hInc
  case store r k =>
    repeat' split at hn
    all_goals cases hn
    all_goals
      rw [← hq]
      refine stamp_after_ord_inc (n := storeOrdinal r k) ?_ ?_ ?_
      · rfl
      · rw [hq]; rfl
      · exact afterStore_ordinal r k
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp_all [stamp, ordinal, afterFree, lenOrigNext, lenExtraNext, Wg2.init]
  all_goals split_ifs
  all_goals simp_all
  all_goals omega

private def followedAbove (n : Nat) : Option (Option Machine.ThreadD) → Prop
  | none | some none | some (some .done) => True
  | some (some (.wg2 q)) => n < stamp q
  | _ => False

private theorem above_step {e : Event} {s : Option (Option Machine.ThreadD)} {n : Nat}
    (h : followedAbove n s) :
    followedAbove n (s.bind fun q => (Machine.machine P L g).next q e) := by
  cases s with
  | none => trivial
  | some s =>
    cases s with
    | none => trivial
    | some s =>
      change followedAbove n (Machine.next P L g s e)
      cases s with
      | done => trivial
      | wg2 q =>
        simp only [Machine.next]
        split
        · rename_i d hn
          have h' := (role_stamp hn).1
          exact Nat.lt_of_lt_of_le h h'
        · split_ifs <;> trivial
        · trivial
      | _ => exact h.elim

private theorem after_store_above {q : D} {e : Event} {r : Fin 4} {s : Fin 8}
    (hq : q.site = .store r s) :
    followedAbove (stamp q) (Machine.next P L g (.wg2 q) e) := by
  simp only [Machine.next]
  split
  · rename_i d hn
    exact (role_stamp hn).2 ⟨r, s, hq⟩
  · split_ifs <;> trivial
  · trivial

private theorem future_above {i j n : Nat} (hi : i ≤ j) (hj : j ≤ (X.tr g).length)
    (h : followedAbove n (Frame.stateAt (Machine.code P L) X g i)) :
    followedAbove n (Frame.stateAt (Machine.code P L) X g j) := by
  induction j with
  | zero => obtain rfl := Nat.eq_zero_of_le_zero hi; exact h
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hi with rfl | hk
    · exact h
    have hkl : k < (X.tr g).length := by omega
    obtain ⟨ev, he⟩ : ∃ ev, X.get (g, k) = some ev := ⟨_, List.getElem?_eq_getElem hkl⟩
    rw [Frame.stateAt_succ he]
    exact above_step (ih (by omega) hkl.le)

private theorem store_before_same_index {i j : Nat} {d q : D} {r : Fin 4} {s : Fin 8} (hij : i < j)
    (hj : j ≤ (X.tr g).length) (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 q))) (hs : d.site = .store r s)
    (hs' : q.site = .store r s) (hb : d.block = q.block) : False := by
  have hil : i < (X.tr g).length := by omega
  obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e := ⟨_, List.getElem?_eq_getElem hil⟩
  have hnext : followedAbove (stamp d) (Frame.stateAt (Machine.code P L) X g (i + 1)) := by
    rw [Frame.stateAt_succ he, hi, Option.bind_some]
    exact after_store_above hs
  have h := future_above hij hj hnext
  rw [hq] at h
  change stamp d < stamp q at h
  simp only [stamp, hs, hs', hb] at h
  exact (Nat.lt_irrefl _ h)

/-- The same thread reaches a particular row/step store at most once per block. -/
theorem store_index_unique {i j : Nat} {d q : D} {r : Fin 4} {s : Fin 8}
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hj : Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 q)))
    (hiLen : i ≤ (X.tr g).length) (hjLen : j ≤ (X.tr g).length) (hsite : d.site = .store r s)
    (hsite' : q.site = .store r s) (hblock : d.block = q.block) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact (store_before_same_index h hjLen hi hj hsite hsite' hblock).elim
  · exact h
  · exact (store_before_same_index h hiLen hj hi hsite' hsite hblock.symm).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2StoreHistory
