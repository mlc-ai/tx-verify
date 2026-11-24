-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReadBytes

@[expose] public section

/-! # Dequantizer tracking from finite input bytes -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2

open PTX PTX.Proof PTX.Flow

/-- The accumulated scale elements of the current row have finite byte patterns. -/
def ScalePrefix (d : D) : Prop :=
  match d.site with
  | .scale _ j => ∀ i < 4 * j.val, Numeric.byteAt d.sc i < 255
  | _ => True

/-- The source bytes identify a cache row or the typed zero fill. -/
def FiniteInput (d : D) (e : Event) : Prop :=
  match d.site with
  | .scale .. => ∀ a bs, e.kind = .rd a bs →
      (∃ ns : List Nat, ns.length = 4 ∧ (∀ b ∈ ns, b < 255) ∧ bs = ns.map inputByte) ∨
        bs = zeroWord
  | .raw .. => ∀ a bs, e.kind = .rd a bs →
      (∃ ns : List Nat, ns.length = 8 ∧ (∀ b ∈ ns, b < 256 ∧ b ≠ 127 ∧ b ≠ 255) ∧
        bs = ns.map inputByte) ∨ bs = zeroWord ++ zeroWord
  | _ => True

private theorem scale_input {d : D} {e : Event} {a : Acc} {bs : List (Option Byte)} {r j : Fin 4}
    (hd : d.site = .scale r j) (he : e.kind = .rd a bs) (hRead : FiniteInput d e) :
    rebuild 3 bs = .ok (b32 (scaleBits bs)) ∧
      ∀ i : Fin 4, Numeric.byteAt (scaleBits bs) i.val < 255 := by
  simp only [FiniteInput, hd] at hRead
  rcases hRead a bs he with ⟨ns, hlen, hByte, rfl⟩ | rfl
  · exact scale_read_accepts hlen hByte
  · exact scale_zero_accepts

/-- Cache byte validity and the accumulated scale prefix supply the machine's data obligations. -/
theorem validRead_of_finite {d : D} {e : Event}
    (hPrefix : ScalePrefix d) (hRead : FiniteInput d e) : ValidRead d e := by
  cases hd : d.site
  case scale r j =>
    simp only [ValidRead, hd]
    intro a bs he
    obtain ⟨hRebuild, hBytes⟩ := scale_input hd he hRead
    refine ⟨hRebuild, fun hj => ?_⟩
    simp only [ScalePrefix, hd, hj] at hPrefix
    simp only [hj]
    exact scale_update_final hPrefix hBytes
  case raw r j =>
    simp only [ValidRead, FiniteInput, hd] at *
    intro a bs he
    rcases hRead a bs he with ⟨ns, hlen, hByte, rfl⟩ | rfl
    · exact raw_read_accepts hlen hByte
    · exact raw_zero_accepts
  all_goals simp [ValidRead, hd]

private theorem scalePrefix_scale {P : Params} {L : Launch} {g : Nat} {d d' : D}
    {e : Event} {r j : Fin 4} (hd : d.site = .scale r j) (hPrefix : ScalePrefix d)
    (hRead : FiniteInput d e) (hn : next P L g d e = some (some d')) : ScalePrefix d' := by
  simp only [next, nextSite, hd] at hn
  split at hn
  · rename_i a bs he
    obtain ⟨hRebuild, hBytes⟩ := scale_input hd he hRead
    rw [hRebuild] at hn
    split at hn
    · simp only [ite_true] at hn
      split at hn
      · cases hn
      · cases hn
        by_cases hl : j.val + 1 < 4
        · simp only [afterScale, dite_eq_left hl, ScalePrefix]
          intro i hi
          simp only [ScalePrefix, hd] at hPrefix
          exact scale_update_prefix hPrefix hBytes i (by omega)
        · simp [ScalePrefix, afterScale, hl]
    · cases hn
  · cases hn

variable {P : Params}

/-- Every continuing step with finite source bytes preserves the scale prefix invariant. -/
theorem scalePrefix_next {L : Launch} {g : Nat} {d d' : D} {e : Event} (hPrefix : ScalePrefix d)
    (hRead : FiniteInput d e) (hn : next P L g d e = some (some d')) : ScalePrefix d' := by
  cases hd : d.site
  case scale r j => exact scalePrefix_scale hd hPrefix hRead hn
  all_goals
    simp only [next, nextSite, hd] at hn
    repeat' split at hn
    all_goals cases hn
    all_goals
      simp only [ScalePrefix, lenOrigNext, lenExtraNext, afterRaw, afterStore, afterFree]
      repeat' split_ifs
      all_goals first | exact hPrefix | simp

private def scaleInvariant : Option Machine.ThreadD → Prop
  | some (.wg2 d) => ScalePrefix d
  | _ => True

private theorem scaleInvariant_next {L : Launch} {g : Nat} {d d' : Option Machine.ThreadD}
    {e : Event} (hPrefix : scaleInvariant d) (hRead : ∀ w, d = some (.wg2 w) → FiniteInput w e)
    (hn : (Machine.machine P L g).next d e = some d') : scaleInvariant d' := by
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
            change ScalePrefix (init P L g)
            unfold ScalePrefix init firstSite
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
        exact scalePrefix_next hPrefix (hRead w rfl) hh
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

/-- Finite source witnesses for earlier reads give the scale prefix at the current followed
site. This conclusion does not require the execution to be globally tracked. -/
theorem scalePrefix_at {L : Launch} {X : Execution} {g i : Nat} {d : D}
    (hA : ∀ j < i, ∀ w e,
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 w)) →
      X.get (g, j) = some e → FiniteInput w e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (hi : i ≤ (X.tr g).length) : ScalePrefix d := by
  have invAt : ∀ n ≤ i, ∀ q,
      Frame.stateAt (Machine.code P L) X g n = some q → scaleInvariant q := by
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
      exact scaleInvariant_next (ih (by omega) s hs)
        (fun w hw => hA n (by omega) w e (hw ▸ hs) he) hStep
  exact invAt i le_rfl (some (.wg2 d)) hState

/-- The dequantizer keeps following the current event when it and its preceding cache reads
have finite source witnesses. Other roles do not enter this local statement. -/
theorem next_tracked_of_finite {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {d : D}
    {e : Event} {o : Option TState} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : (Machine.machine P L g).Sound)
    (hA : ∀ j ≤ i, ∀ w e,
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 w)) →
      X.get (g, j) = some e → FiniteInput w e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.wg2 d)))
    (he : X.get (g, i) = some e) (hf : (Machine.machine P L g).Fired (some (.wg2 d)) e o) :
    Machine.next P L g (.wg2 d) e ≠ some none := by
  have hp := scalePrefix_at (fun j hj => hA j hj.le) hState (PTX.len_of_get he).le
  exact never_dismiss hpre hX hs hState he hf (validRead_of_finite hp (hA i le_rfl d e hState he))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2
