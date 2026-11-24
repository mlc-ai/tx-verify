-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrOAccSt
public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueRun
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc
public import Lemmas.Flow.SplitJoin

@[expose] public section

/-! # The correction part of `Cross.NextStopsAtExitOrBadRead`

The correction machine stops (`next = none`) at the exit, or where a step on a value it reads
faults:

* at a load of `α`, a word the comparison `α < 1` rejects; at a load of `l`, a word that does
  not rebuild; a canonical single-precision float passes both (`ltOneE_fin`);
* at the credit after a load of `l`, a word the reciprocal rejects; the word read earlier
  (`Counts.finSt`) is a canonical float, whose reciprocal is a number (`recipE_fin`);
* at a chunk's wait, the products' check (`chunkOk`, and at a final chunk the conversions'
  check `finOk`): it passes when the chunk's values are single-precision floats (a load with
  other values is a `BadRead`, `Counts.rsLd`, `Counts.finLd`) and the pair's halves read as
  numbers (`chunkOk_of`, `finOk_of`): the factor is a canonical word (`Counts.rsSt`), a payload
  or a 32-bit pattern that packs with itself into two copies of itself (`split_join_bits`);
  the reciprocal of a canonical row sum `l` is the payload `1 / l'` (`split_fcPair`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Correction

set_option maxHeartbeats 8000000 in
/-- The sites where the machine can stop. -/
theorem next_none {L : Launch} {g : Nat} {d : D} {e : Event} (hev : Ev L g d e)
    (hn : next L g d e = none) :
    d.site = .exit ∨ (∃ st, d.site = .ldA st) ∨ (∃ st, d.site = .ldL st) ∨ d.site = .credit 4 ∨
      d.site = .credit 5 ∨ (∃ st j, d.site = .rldW st j) ∨ ∃ st j, d.site = .fldW st j := by
  obtain ⟨-, hk⟩ := hev
  rcases e with ⟨epc, ek⟩
  obtain ⟨site, i, t, aw, a, o⟩ := d
  rcases site with _ | _ | st0 | ⟨st0, gen⟩ | a0 | st0 | st0 | ⟨st0, j⟩ | ⟨st0, j⟩ | ⟨st0, j⟩ |
    st0 | ⟨st0, fin⟩ | st0 | st0 | st0 | ⟨st0, j⟩ | ⟨st0, j⟩ | ⟨st0, j, hh, el⟩ | st0 | st0 |
    _ | _ | _
  all_goals (try fin_cases st0)
  all_goals (try fin_cases a0)
  all_goals (try cases gen)
  all_goals (try cases fin)
  all_goals simp only at hk
  all_goals repeat' (first | (obtain rfl := hk) | (obtain ⟨_, hk⟩ := hk))
  all_goals simp only [next, nextItem, afterTrip] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals simp_all

end Correction

/-- The products' check passes for sixteen single-precision floats and a pair whose halves read
as numbers. -/
theorem chunkOk_of {o : List Value} {c : Value} {y0 y1 : ℝ} (ho : F32s o) (hl : o.length = 16)
    (h1 : valFloat .f32 (splitValue 64 c).1 = .ok y0)
    (h2 : valFloat .f32 (splitValue 64 c).2 = .ok y1) : Correction.chunkOk o c = true := by
  unfold Correction.chunkOk
  rw [List.all_eq_true]
  intro q hq
  have hq8 := List.mem_range.mp hq
  obtain ⟨x, hx⟩ := ho _ (List.getElem_mem (show 2 * q < o.length by omega))
  obtain ⟨y, hy⟩ := ho _ (List.getElem_mem (show 2 * q + 1 < o.length by omega))
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show 2 * q < o.length by omega),
    List.getElem?_eq_getElem (show 2 * q + 1 < o.length by omega), Option.getD_some,
    Option.getD_some, hx, hy]
  have hj : splitValue 64 (joinValue (.float .f32 x) (.float .f32 y)) =
      (.float .f32 x, .float .f32 y) := split_join_l rfl
  rw [floatE_mul2_fin (by rw [hj]; exact valFloat_fl x) (by rw [hj]; exact valFloat_fl y) h1 h2]
  rfl

/-- The final check passes for sixteen single-precision floats and a pair whose halves read as
numbers: the products are numbers, which convert to halves. -/
theorem finOk_of {o : List Value} {c : Value} {y0 y1 : ℝ} (ho : F32s o) (hl : o.length = 16)
    (h1 : valFloat .f32 (splitValue 64 c).1 = .ok y0)
    (h2 : valFloat .f32 (splitValue 64 c).2 = .ok y1) : Correction.finOk o c = true := by
  unfold Correction.finOk
  rw [chunkOk_of ho hl h1 h2, Bool.true_and, List.all_eq_true]
  intro q hq
  have hq8 := List.mem_range.mp hq
  obtain ⟨x, hx⟩ := ho _ (List.getElem_mem (show 2 * q < o.length by omega))
  obtain ⟨y, hy⟩ := ho _ (List.getElem_mem (show 2 * q + 1 < o.length by omega))
  have hp : Correction.prodV o c q = .pair (.float .f32 (x * y0)) (.float .f32 (y * y1)) := by
    unfold Correction.prodV mulOutV
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show 2 * q < o.length by omega),
      List.getElem?_eq_getElem (show 2 * q + 1 < o.length by omega), Option.getD_some,
      Option.getD_some, hx, hy]
    have hj : splitValue 64 (joinValue (.float .f32 x) (.float .f32 y)) =
        (.float .f32 x, .float .f32 y) := split_join_l rfl
    exact okVal_of_ok
      (floatE_mul2_fin (by rw [hj]; exact valFloat_fl x) (by rw [hj]; exact valFloat_fl y) h1 h2)
  rw [hp]
  simp only [splitValue]
  rw [cvtPairE_of_valFloat (va := .float .f32 _) (vb := .float .f32 _) (valFloat_fl _)
    (valFloat_fl _)]
  rfl

/-- The halves of a canonical factor word packed with itself read as the factor. -/
theorem rcPair_halves {d : Correction.D} {x : ℝ} (h : F32Val d.aw x) :
    valFloat .f32 (splitValue 64 (Correction.rcPair d)).1 = .ok x ∧
      valFloat .f32 (splitValue 64 (Correction.rcPair d)).2 = .ok x := by
  rw [rcPair_split h, h.2]
  exact ⟨rfl, rfl⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

omit hpre hX ht in
/-- A correction thread's read that is not a `BadRead` reads a canonical float. -/
theorem corr_read_ok {g j pc : Nat} {a : Acc} {bs : List (Option Byte)} (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, j) = some ⟨pc, .rd a bs⟩)
    (hb : ¬ BadRead L X g j) : ∃ x, F32Read bs x := by
  by_contra hn
  exact hb (.inr (.inl ⟨pc, a, bs, he, hw, hw', hn⟩))

omit hpre hX ht in
/-- A load that is not a `BadRead` returns single-precision floats. -/
theorem load_ok {g j pc a : Nat} {vals : List Value}
    (he : X.get (g, j) = some ⟨pc, .tc (.ld a vals .s32x32b)⟩) (hb : ¬ BadRead L X g j) :
    F32s vals := by
  by_contra hn
  exact hb (.inl ⟨pc, a, vals, he, hn⟩)

/-- **The correction part of `Cross.NextStopsAtExitOrBadRead`.** -/
theorem Cross.NextStops_corr {g i : Nat} {d : Correction.D} {e : Event} (hg : g < L.threads)
    (hσ : St L X g i = some (some (.inr (.corr d)))) (he : X.get (g, i) = some e)
    (hn : (code L g).next (.inr (.corr d)) e = none) :
    (∃ pc, e = ⟨pc, .exit⟩) ∨ ∃ j ≤ i, BadRead L X g j := by
  have hσ' : Frame.stateAt (code L) X g i = some (some (.inr (.corr d))) := hσ
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have hwr := role_warp_run hpre hg (Frame.trace (C := code L) hC hX hg) i (.corr d) hσ'
  obtain ⟨hw, hw'⟩ : 8 ≤ warpOf L g ∧ warpOf L g < 12 := hwr
  have hn' : Correction.next L g d e = none := by
    simp only [code] at hn
    cases h : Correction.next L g d e with
    | none => rfl
    | some o => rw [h] at hn; cases hn
  by_cases hx : ∃ pc, e = ⟨pc, .exit⟩
  · exact .inl hx
  right
  by_contra hbad
  have hok : ∀ j ≤ i, ¬ BadRead L X g j := fun j hj hb => hbad ⟨j, hj, hb⟩
  rcases corr_origin hpre hX ht he hw hw' (corr_noUb hpre hX hσ' he) with
    ⟨p0, hp0, -⟩ | ⟨d', t, ins, o, hσ'', hc, hi, -, -, -, hev⟩
  · rw [hσ'] at hp0; cases hp0
  rw [hσ'] at hσ''
  simp only [Option.some.injEq, Sum.inr.injEq, Role.corr.injEq] at hσ''
  subst hσ''
  have hnx : e.kind ≠ .exit := fun h => hx ⟨e.pc, by obtain ⟨epc, ek⟩ := e; simp_all⟩
  have hevE := hev hnx
  have hsites := Correction.next_none hevE hn'
  obtain ⟨-, hk⟩ := hevE
  -- the earlier read and load named by the invariant are not `BadRead`s
  have hrd : ∀ {r : Nat} {pc : Nat} {ac : Acc} {bs : List (Option Byte)},
      r < ((X.tr g).take i).length → ((X.tr g).take i)[r]? = some ⟨pc, .rd ac bs⟩ →
      ∃ x, F32Read bs x := by
    intro r pc ac bs hr hget
    rw [List.length_take] at hr
    rw [take_get (by omega)] at hget
    exact corr_read_ok hw hw' hget (hok r (by omega))
  have hld : ∀ {r : Nat} {pc a : Nat} {vals : List Value},
      r < ((X.tr g).take i).length → ((X.tr g).take i)[r]? = some ⟨pc, .tc (.ld a vals .s32x32b)⟩ →
      F32s vals ∧ vals.length = 16 := by
    intro r pc a vals hr hget
    rw [List.length_take] at hr
    rw [take_get (by omega)] at hget
    obtain ⟨_, _, _, -, -, -, -, -, hlen⟩ := corr_tld hpre hX ht hw hw' hget
    exact ⟨load_ok hget (hok r (by omega)), hlen⟩
  obtain ⟨epc, ek⟩ := e
  obtain ⟨site, ii, tt, aw, aa, oo⟩ := d
  cases site <;> simp only at hk
  all_goals try (simp [Correction.next] at hn'; done)
  case ldA st =>
    obtain ⟨ac, bs, rfl, -⟩ := hk
    obtain ⟨x, v, hv, hF⟩ := corr_read_ok hw hw' he (hok i le_rfl)
    simp [Correction.next, hv, Correction.ltOneE_fin hF.2] at hn'
  case ldL st =>
    obtain ⟨ac, bs, rfl, -⟩ := hk
    obtain ⟨x, v, hv, hF⟩ := corr_read_ok hw hw' he (hok i le_rfl)
    simp [Correction.next, hv] at hn'
  case credit a =>
    fin_cases a <;> simp [Correction.next] at hn'
    · obtain ⟨r, hr, pc, ac, bs, hget, -, hreb, -⟩ :=
        hc.finSt 0 (.inl ⟨rfl, rfl⟩)
      obtain ⟨x, v, hv, hF⟩ := hrd hr hget
      rw [hv] at hreb
      injection hreb with hreb
      subst hreb
      simp [Correction.recipE_fin hF.2] at hn'
    · obtain ⟨r, hr, pc, ac, bs, hget, -, hreb, -⟩ :=
        hc.finSt 1 (.inr (.inl ⟨rfl, rfl⟩))
      obtain ⟨x, v, hv, hF⟩ := hrd hr hget
      rw [hv] at hreb
      injection hreb with hreb
      subst hreb
      simp [Correction.recipE_fin hF.2] at hn'
  case rldW st j =>
    obtain ⟨r, hr, pc, hget, -⟩ := hc.rsLd st j (.inl rfl)
    obtain ⟨ho, hl⟩ := hld hr hget
    obtain ⟨r', hr', pc', ac, bs, hget', -, hreb, -⟩ :=
      hc.rsSt st (.inr (.inr (.inl ⟨j, .inl rfl⟩)))
    obtain ⟨x, v, hv, hF⟩ := hrd hr' hget'
    rw [hv] at hreb
    injection hreb with hreb
    subst hreb
    obtain ⟨h1, h2⟩ := rcPair_halves (d := ⟨.rldW st j, ii, tt, v, aa, oo⟩) hF
    have hch := chunkOk_of ho hl h1 h2
    simp only [Correction.next, hF.bytes_eq, hch, and_self, ↓reduceIte, reduceCtorEq] at hn'
  case fldW st j =>
    obtain ⟨r, hr, pc, hget, -⟩ := hc.finLd st j (.inl rfl)
    obtain ⟨ho, hl⟩ := hld hr hget
    obtain ⟨r', hr', pc', ac, bs, hget', -, hreb, -⟩ := hc.finSt st (by
      unfold Correction.finStat Correction.finRecip Correction.finChunk
      exact .inr (.inr (.inr (.inr (.inr ⟨j, .inl rfl⟩)))))
    obtain ⟨x, v, hv, hF⟩ := hrd hr' hget'
    rw [hv] at hreb
    injection hreb with hreb
    subst hreb
    have hsp := split_fcPair ⟨.fldW st j, ii, tt, v, aa, oo⟩ hF.2
    have hch := finOk_of ho hl (c := Correction.fcPair ⟨.fldW st j, ii, tt, v, aa, oo⟩)
      (by rw [hsp]; exact valFloat_fl _) (by rw [hsp]; exact valFloat_fl _)
    simp only [Correction.next, hch, ↓reduceIte, reduceCtorEq] at hn'
  all_goals first
    | (subst hk; simp [Correction.next] at hn'; done)
    | (obtain ⟨_, hk⟩ := hk; subst hk; simp [Correction.next] at hn'; done)
    | (obtain ⟨_, _, _, hk⟩ := hk; subst hk; simp [Correction.next] at hn'; done)
    | (subst hk; exact hnx rfl)
    | (simp at hsites)

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
