-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoaderRing
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Loader

@[expose] public section

/-! # A copy of the use a loader poll waits for comes after the poll's elections

A loader thread `g` at a poll site waits for one use of a ring barrier: the full barrier
`loaderPollBar d`, in the round of its successful polls of the partner empty barrier (`kvPoll`,
`qPoll` of `Loader.Ledger`). A copy of a loader thread `y` of the same CTA on that barrier, in
that round, is a copy of the same use: for a KV slot the copy's use number is the poll's
(`kvPolled`), so the item and the position in it agree (`uB_inj`); for a Q stage the item
agrees. The copy's state has made the elections of the use's poll, the arrival's on the leader
CTA and those of the copies up to it, so more than `g` at the poll (`lane_elects`). No copy is
in the round of a drain poll, since every copy belongs to an item before the drain. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work

noncomputable section

variable {L : Launch}

/-- A use number, written as an item's first use plus a position below `2 n`, determines the item
and the position. -/
theorem uB_inj {i i' r r' : Nat} (hr : r < 2 * n L) (hr' : r' < 2 * n L)
    (h : uB L i + r = uB L i' + r') : i = i' ∧ r = r' := by
  have h1 := uB_div (L := L) (i := i) hr
  have h2 := uB_div (L := L) (i := i') hr'
  rw [h] at h1
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

/-- The uses of the items before item `b` are below its first use. -/
theorem uB_lt {i b r : Nat} (hi : i < b) (hr : r < 2 * n L) : uB L i + r < uB L b := by
  have h := Nat.mul_le_mul_left (2 * n L) (show i + 1 ≤ b by omega)
  unfold uB
  rw [Nat.mul_succ] at h
  omega

/-- A KV use (a K or V tile, not a Q stage). -/
def UseK.kv : UseK → Bool
  | .q0 | .q1 => false
  | _ => true

/-- The position of a KV use in its item: the item's last K and V tiles, then K and V of each
trip. -/
def pos (u : UseK) (t : Nat) : Nat :=
  match u with
  | .k0 => 0
  | .v0 => 1
  | .k => 2 + 2 * t
  | .v => 3 + 2 * t
  | .q0 | .q1 => 0

/-- A KV use's position is below the item's `2 n` uses. -/
theorem pos_lt {u : UseK} {t : Nat} (hn1 : 1 ≤ n L)
    (htr : (u = .k ∨ u = .v) → t + 2 ≤ n L) :
    pos u t < 2 * n L := by
  cases u <;> simp only [pos] <;> first | omega | (have := htr (by simp); omega)

/-- A KV copy completes on the full barrier of its use's slot, in the round of its use. -/
theorem copy_kv {u : UseK} {j : Fin 2} {i t : Nat} (hu : u.kv = true) :
    CopyId.bar L ⟨u, j, i, t⟩ =
        .kvFull ⟨(uB L i + pos u t) % 6, Nat.mod_lt _ (by decide)⟩ ∧
      CopyId.round L ⟨u, j, i, t⟩ = (uB L i + pos u t) / 6 := by
  cases u <;> simp only [UseK.kv, Bool.false_eq_true] at hu <;>
    simp only [CopyId.bar, CopyId.round, CopyId.use, pos, Nat.add_zero, Nat.add_assoc, and_self]

/-- Two KV uses at the same position are at the same elections of the item. -/
theorem pre_pos {g : Nat} {u u' : UseK} {t t' : Nat} (hu : u.kv = true) (hu' : u'.kv = true)
    (h : pos u t = pos u' t') : preElects L g u t = preElects L g u' t' := by
  cases u <;> cases u' <;> simp only [UseK.kv, Bool.false_eq_true] at hu hu' <;>
    simp only [pos] at h
  all_goals first
    | omega
    | rfl
    | (have ht : t = t' := by omega
       subst ht
       rfl)

/-- The elections of an item depend on the thread only through the leader rank. -/
theorem itemElects_congr {g y : Nat} (hr : r0 L y = r0 L g) : itemElects L y = itemElects L g := by
  simp only [itemElects, hr]

/-- The elections of an item before a use depend on the thread only through the leader rank. -/
theorem preElects_congr {g y : Nat} (hr : r0 L y = r0 L g) (u : UseK) (t : Nat) :
    preElects L y u t = preElects L g u t := by
  cases u <;> simp only [preElects, hr]

/-- **A copy of the use a loader poll waits for**, of a thread of the same CTA (so with the
same items and the same leader rank), has made more elections than the poll's state. -/
theorem lane_elects {g y P : Nat} {d d' : D} {u' : UseK} {j' : Fin 2}
    (hn1 : 1 ≤ n L) (hT : T L y = T L g) (hr : r0 L y = r0 L g)
    (hinv : Inv L g d) (hring : d.s = kvB L g d % 6) (hk : loaderKind d.site = .wait)
    (hi' : Inv L y d') (hs' : d'.site = .copy u' j')
    (hbar : CopyId.bar L ⟨u', j', d'.i, d'.t⟩ = loaderPollBar d)
    (hround : CopyId.round L ⟨u', j', d'.i, d'.t⟩ = P)
    (hkv : ∀ s, loaderPollBar d = .kvFull s → P = slotCount (kvPolled L g d) s)
    (hq : ∀ st, loaderPollBar d = .qFull st → P = qPolled L g d st) :
    electOf L g d < electOf L y d' := by
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  obtain ⟨site', i', t', s', ph', qp'⟩ := d'
  simp only at hs'
  subst hs'
  have hit' : i' < T L y := hi'.item rfl
  have htr' : (u' = .k ∨ u' = .v) → t' + 2 ≤ n L := fun h => hi'.trip (by
    rcases h with rfl | rfl <;> rfl)
  have hit : site.inItem = true → i < T L g := hinv.item
  have htr : site.inTrip = true → t + 2 ≤ n L := hinv.trip
  have hel' : electOf L y ⟨.copy u' j', i', t', s', ph', qp'⟩ =
      i' * itemElects L g + preElects L g u' t' + r0 L g + j'.val + 1 := by
    simp only [electOf, itemElects_congr hr, preElects_congr hr, hr]
  rw [hel']
  simp only at hit htr hring hbar hround ⊢
  rcases site with _ | _ | u | u | u | ⟨u, j⟩ | ⟨u, j⟩ | k | _ | _ | _ | _ <;>
    simp only [loaderKind, reduceCtorEq] at hk
  · -- a poll of an item's use
    have hit := hit rfl
    simp only [electOf]
    by_cases hu : u.kv = true
    · have hw : loaderPollBar ⟨.wait u, i, t, s, ph, qp⟩ =
            .kvFull ⟨(uB L i + pos u t) % 6, Nat.mod_lt _ (by decide)⟩ ∧
          kvPolled L g ⟨.wait u, i, t, s, ph, qp⟩ = uB L i + pos u t := by
        cases u <;> simp only [UseK.kv, Bool.false_eq_true] at hu <;> constructor <;>
          simp only [loaderPollBar, kvPolled, kvB, pos, FBar.kvFull.injEq,
            Fin.ext_iff] at hring ⊢ <;>
          omega
      have hP := hkv _ hw.1
      rw [hw.2] at hP
      rw [hw.1] at hbar
      by_cases hu' : u'.kv = true
      · obtain ⟨hb', hr'⟩ := copy_kv (L := L) (j := j') (i := i') (t := t') hu'
        rw [hb', FBar.kvFull.injEq, Fin.ext_iff, Fin.val_mk, Fin.val_mk] at hbar
        rw [hr'] at hround
        simp only [slotCount] at hP
        have huse : uB L i + pos u t = uB L i' + pos u' t' := by omega
        obtain ⟨rfl, hpos⟩ := uB_inj (pos_lt hn1 (fun h => htr (by
          rcases h with rfl | rfl <;> rfl))) (pos_lt hn1 htr') huse
        rw [pre_pos hu hu' hpos]
        omega
      · cases u' <;> simp only [UseK.kv, not_true_eq_false] at hu' <;>
          simp only [CopyId.bar, reduceCtorEq] at hbar
    · cases u <;> simp only [UseK.kv, not_true_eq_false] at hu <;>
        cases u' <;> simp only [CopyId.bar, loaderPollBar, reduceCtorEq, FBar.qFull.injEq,
          zero_ne_one, one_ne_zero] at hbar <;>
        simp only [CopyId.round] at hround <;>
        · have hP := hq _ rfl
          simp only [qPolled, Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte,
            Nat.add_zero] at hP
          subst hround
          simp only [hP, preElects]
          omega
  · -- a drain poll of the KV ring: no copy of the items is in its round
    exfalso
    have hw : loaderPollBar ⟨.drain k, i, t, s, ph, qp⟩ =
          .kvFull ⟨(uB L (T L g) + k.val) % 6, Nat.mod_lt _ (by decide)⟩ ∧
        kvPolled L g ⟨.drain k, i, t, s, ph, qp⟩ = uB L (T L g) + k.val := by
      refine ⟨?_, rfl⟩
      simp only [loaderPollBar, kvB, FBar.kvFull.injEq, Fin.ext_iff] at hring ⊢
      omega
    have hP := hkv _ hw.1
    rw [hw.2] at hP
    rw [hw.1] at hbar
    by_cases hu' : u'.kv = true
    · obtain ⟨hb', hr'⟩ := copy_kv (L := L) (j := j') (i := i') (t := t') hu'
      rw [hb', FBar.kvFull.injEq, Fin.ext_iff, Fin.val_mk, Fin.val_mk] at hbar
      rw [hr'] at hround
      simp only [slotCount] at hP
      have hlt := uB_lt (L := L) (r := pos u' t') (show i' < T L g by omega) (pos_lt hn1 htr')
      omega
    · cases u' <;> simp only [UseK.kv, not_true_eq_false] at hu' <;>
        simp only [CopyId.bar, reduceCtorEq] at hbar
  · -- the drain's Q poll: no copy of the items is in its round
    exfalso
    have hP := hq 1 rfl
    simp only [qPolled] at hP
    cases u' <;> simp only [CopyId.bar, loaderPollBar, reduceCtorEq, FBar.qFull.injEq,
      zero_ne_one] at hbar
    simp only [CopyId.round] at hround
    omega

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
