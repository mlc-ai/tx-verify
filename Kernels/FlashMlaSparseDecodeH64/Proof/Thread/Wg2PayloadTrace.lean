-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2GatherWord

@[expose] public section

/-! # The staged cache words in a dequantizer's local state -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2

open PTX PTX.Flow

private theorem byteAt_mod_window (word k : Nat) :
    Numeric.byteAt word k = word % 256 ^ (k + 1) / 256 ^ k := by
  rw [pow_succ, Nat.mod_mul_right_div_self]
  rfl

private theorem append_scale_prefix (old word n k : Nat) (hk : k < n) :
    Numeric.byteAt (old % 256 ^ n + 256 ^ n * word) k = Numeric.byteAt old k := by
  have hd : 256 ^ (k + 1) ∣ 256 ^ n := pow_dvd_pow _ (by omega)
  have hm : (256 ^ n * word) % 256 ^ (k + 1) = 0 := Nat.mod_eq_zero_of_dvd
    (dvd_mul_of_dvd_left hd _)
  rw [byteAt_mod_window, byteAt_mod_window, Nat.add_mod, Nat.mod_mod_of_dvd _ hd,
    hm, Nat.add_zero, Nat.mod_mod]

private theorem append_scale_new (old word n k : Nat) :
    Numeric.byteAt (old % 256 ^ n + 256 ^ n * word) (n + k) = Numeric.byteAt word k := by
  have hp : 0 < 256 ^ n := pow_pos (by decide) _
  unfold Numeric.byteAt
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hp]
  rw [Nat.div_eq_of_lt (Nat.mod_lt _ hp), Nat.zero_add]

/-- The prefix of scale bytes already loaded for the current row. -/
def ScalePayload (P : Params) (L : Launch) (g : Nat) (d : D) (row n : Nat) : Prop :=
  ∀ k < n, Numeric.byteAt d.sc k =
    gatheredByte P L g d.block (rawRow L g row) (512 + k)

/-- The eight raw input bytes for the indicated step of the current row. -/
def RawPayload (P : Params) (L : Launch) (g block row step word : Nat) : Prop :=
  ∀ k < 8, Numeric.byteAt word k =
    gatheredByte P L g block (rawRow L g row) (elemByte L g step k)

/-- The scale prefix and the current and prefetched words that the active site uses. -/
def CachePayload (P : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  match d.site with
  | .scale row part => ScalePayload P L g d row.val (4 * part.val)
  | .raw row step => ScalePayload P L g d row.val 16 ∧
      (0 < step.val → RawPayload P L g d.block row.val (step.val - 1) d.raw)
  | .store row step => ScalePayload P L g d row.val 16 ∧
      RawPayload P L g d.block row.val step.val d.raw ∧
      (step.val + 1 < 8 → RawPayload P L g d.block row.val (step.val + 1) d.nxt)
  | _ => True

private theorem scale_extend {P : Params} {L : Launch} {g : Nat} {d : D}
    {row part : Fin 4} {bs : List (Option Byte)}
    (hOld : ScalePayload P L g d row.val (4 * part.val))
    (hNew : ∀ k < 4, Numeric.byteAt (scaleBits bs) k =
      gatheredByte P L g d.block (rawRow L g row.val) (512 + 4 * part.val + k)) :
    ScalePayload P L g {d with sc := d.sc % 256 ^ (4 * part.val) +
      256 ^ (4 * part.val) * scaleBits bs} row.val (4 * (part.val + 1)) := by
  intro k hk
  by_cases h : k < 4 * part.val
  · rw [append_scale_prefix _ _ _ _ h]
    exact hOld k h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    rw [append_scale_new, hNew j (by omega)]
    congr 1
    omega

set_option maxHeartbeats 1250000 in
/-- A continuing dequantizer step maintains the logical content of its current and prefetched
words when the actual source bytes match the selected cache row. -/
theorem cachePayload_next {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : CachePayload P L g d)
    (hScale : ∀ row j a bs, d.site = .scale row j → e.kind = .rd a bs →
      ∀ k < 4, Numeric.byteAt (scaleBits bs) k =
        gatheredByte P L g d.block (rawRow L g row.val) (512 + 4 * j.val + k))
    (hRaw : ∀ row j a bs, d.site = .raw row j → e.kind = .rd a bs →
      RawPayload P L g d.block row.val j.val (rawBits bs))
    (hn : next P L g d e = some (some d')) : CachePayload P L g d' := by
  cases hSite : d.site
  case scale row j =>
    have hOld : ScalePayload P L g d row.val (4 * j.val) := by
      simpa only [CachePayload, hSite] using h
    simp only [next, nextSite, hSite] at hn
    split at hn
    · rename_i a bs he
      have hNew := scale_extend (row := row) (part := j) hOld (hScale row j a bs hSite he)
      repeat' split at hn
      all_goals cases hn
      all_goals
        unfold afterScale at *
        split_ifs with hNext
        · exact hNew
        · have hLast : 4 * (j.val + 1) = 16 := by have := j.isLt; omega
          have hSc : ScalePayload P L g _ row.val 16 := hLast ▸ hNew
          exact ⟨hSc, fun hf => (Nat.lt_irrefl 0 hf).elim⟩
    · cases hn
  case raw row j =>
    have hOld : ScalePayload P L g d row.val 16 ∧
        (0 < j.val → RawPayload P L g d.block row.val (j.val - 1) d.raw) := by
      simpa only [CachePayload, hSite] using h
    simp only [next, nextSite, hSite] at hn
    split at hn
    · rename_i a bs he
      have hNew := hRaw row j a bs hSite he
      split at hn
      · split at hn
        · by_cases hZero : j.val = 0
          · rw [ite_eq_left hZero] at hn
            cases hn
            simpa [CachePayload, afterRaw, hZero, ScalePayload] using And.intro hOld.1 hNew
          · rw [ite_eq_right hZero] at hn
            cases hn
            simp only [CachePayload, afterRaw, hZero, ite_false]
            refine ⟨hOld.1, ?_, ?_⟩
            · exact hOld.2 (by omega)
            · intro _
              simpa only [show j.val - 1 + 1 = j.val by omega] using hNew
        · cases hn
      · cases hn
    · cases hn
  case store row j =>
    have hOld : ScalePayload P L g d row.val 16 ∧
        RawPayload P L g d.block row.val j.val d.raw ∧
        (j.val + 1 < 8 → RawPayload P L g d.block row.val (j.val + 1) d.nxt) := by
      simpa only [CachePayload, hSite] using h
    simp only [next, nextSite, hSite] at hn
    repeat' split at hn
    all_goals cases hn
    all_goals
      simp only [CachePayload, afterStore]
      repeat' split_ifs
    all_goals first
      | omega
      | exact ⟨hOld.1, hOld.2.2 (by omega), fun hlt => by
          change j.val + 1 + 1 < 8 at hlt
          exfalso
          omega⟩
      | exact ⟨hOld.1, fun _ => by
          change RawPayload P L g d.block row.val (j.val + 2 - 1) d.nxt
          rw [show j.val + 2 - 1 = j.val + 1 by omega]
          exact hOld.2.2 (by omega)⟩
      | simp [ScalePayload]
  all_goals
    simp only [next, nextSite, hSite] at hn
    repeat' split at hn
    all_goals cases hn
    all_goals
      simp only [CachePayload, lenOrigNext, lenExtraNext, afterFree, Wg2.init, Wg2.firstSite]
      repeat' split_ifs
    all_goals simp [ScalePayload, hSite]

private def payloadState (P : Params) (L : Launch) (g : Nat) : Option Machine.ThreadD → Prop
  | some (.wg2 d) => CachePayload P L g d
  | _ => True

private theorem payloadState_next {P : Params} {L : Launch} {g : Nat}
    {d d' : Option Machine.ThreadD} {e : Event} (hPrefix : payloadState P L g d)
    (hScale : ∀ w row j a bs, d = some (.wg2 w) →
      w.site = .scale row j → e.kind = .rd a bs →
        ∀ k < 4, Numeric.byteAt (scaleBits bs) k =
          gatheredByte P L g w.block (rawRow L g row.val) (512 + 4 * j.val + k))
    (hRaw : ∀ w row j a bs, d = some (.wg2 w) →
      w.site = .raw row j → e.kind = .rd a bs →
        RawPayload P L g w.block row.val j.val (rawBits bs))
    (hn : (Machine.machine P L g).next d e = some d') : payloadState P L g d' := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some s =>
    change Machine.next P L g s e = some d' at hn
    cases s
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn <;> try trivial
            change CachePayload P L g (init P L g)
            unfold CachePayload init firstSite
            split_ifs <;> trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case wg2 w =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' hh
        cases hn
        exact cachePayload_next hPrefix (fun _ _ _ _ => hScale w _ _ _ _ rfl)
          (fun _ _ _ _ => hRaw w _ _ _ _ rfl) hh
      · split_ifs at hn <;> cases hn <;> trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> trivial
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals trivial

/-- The logical cache payload at a followed site is determined by its earlier actual reads. -/
theorem cachePayload_at {P : Params} {L : Launch} {X : Execution}
    {g i : Nat} {d : D}
    (hScale : ∀ j < i, ∀ w e row part a bs,
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 w)) →
      X.get (g, j) = some e → w.site = .scale row part → e.kind = .rd a bs →
      ∀ k < 4, Numeric.byteAt (scaleBits bs) k =
        gatheredByte P L g w.block (rawRow L g row.val) (512 + 4 * part.val + k))
    (hRaw : ∀ j < i, ∀ w e row step a bs,
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 w)) →
      X.get (g, j) = some e → w.site = .raw row step → e.kind = .rd a bs →
      RawPayload P L g w.block row.val step.val (rawBits bs))
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hi : i ≤ (X.tr g).length) : CachePayload P L g d := by
  have invAt : ∀ n ≤ i, ∀ q,
      Frame.stateAt (Machine.code P L) X g n = some q → payloadState P L g q := by
    intro n
    induction n with
    | zero =>
      intro _ q hq
      rw [Frame.stateAt_zero] at hq
      cases hq
      trivial
    | succ n ih =>
      intro hn q hq
      have hlt : n < (X.tr g).length := by omega
      obtain ⟨e, he⟩ : ∃ e, X.get (g, n) = some e :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      rw [Frame.stateAt_succ he] at hq
      obtain ⟨s, hs, hStep⟩ := Option.bind_eq_some_iff.mp hq
      exact payloadState_next (ih (by omega) s hs)
        (fun w _ _ _ _ hw => hScale n (by omega) w e _ _ _ _ (hw ▸ hs) he)
        (fun w _ _ _ _ hw => hRaw n (by omega) w e _ _ _ _ (hw ▸ hs) he) hStep
  exact invAt i le_rfl (some (.wg2 d)) hState


end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2
