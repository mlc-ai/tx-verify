-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollAt
public import Lemmas.Kernel.Progress.WarpCollPair
public import Lemmas.Kernel.Progress.BarMate
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Reg
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # The collectives of two lanes of a warp, from a classification of its states

`warpPair_of_cls`: the facts of two lanes of a warp (`Sched.WarpPair`) from a classification of
the states of the warp's lanes by their collectives (`CollCls`). A warp's collectives are a list
of program counters in order (`cn`: the pc of the `n`-th collective, none past the last), the
number of collectives a state has made is `nc`, and the time table puts the state at the `n`-th
collective at the slot `slot n` and every earlier state of that count below it (`time_lt`).
The role supplies the five facts about its states; the rest (the one position and static part,
the release, the exit, the lag and the stopped lane) is here. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- A lane whose last event is a register request it does not wait for is released. -/
theorem released_of_setMax (hX : Consistent L kernel Assumptions.all m X) (hh : h < L.threads)
    {pc i n : Nat} {inc : Bool}
    (he : X.get (h, (X.tr h).length - 1) = some ⟨pc, .setMaxReg inc n i⟩)
    (hr : ¬ Sched.RegWait L X h) : Step.Released L X h := by
  by_contra hnr
  rcases Sched.thread_cases hX hh (fun pc n hk' => by
      rw [he] at hk'; cases hk') hnr with h | h | h | h | h | h | h
  · obtain ⟨pc, op, hk', -⟩ := h
    rw [he] at hk'; cases hk'
  · exact hr h
  · obtain ⟨pc, grp, dst, act, hk', -⟩ := h
    rw [he] at hk'; cases hk'
  · obtain ⟨id, c', pc, -, hk', -⟩ := h
    change X.get _ = _ at hk'
    rw [he] at hk'; cases hk'
  · obtain ⟨k, -, ⟨⟨ev, hk', hcl⟩, -⟩, -⟩ := h
    rw [he] at hk'; cases hk'
    cases hcl
  · obtain ⟨pc, id, c', hk', -⟩ := h
    rw [he] at hk'; cases hk'
  · obtain ⟨pc, md, n, hk', -⟩ := h
    rw [he] at hk'; cases hk'

/-- **The classification of the states of the lanes `A` of one warp** by their collectives. -/
structure CollCls (P : Params) (L : Launch) (X : Execution) (A : Nat → Prop)
    (S : ∀ g, (thread P L g).D → Sched.CollShape) where
  /-- The program counter of the warp's `n`-th collective. -/
  cn : Nat → Option Nat
  /-- The time of the state at the `n`-th collective. -/
  slot : Nat → Nat
  /-- The number of collectives a state has made. -/
  nc : ∀ x, (thread P L x).D → Nat
  count : ∀ {x k σ}, A x → Frame.stateAt (thread P L) X x k = some (some σ) →
    ((X.tr x).take k).countP Sched.isWarpColl = nc x σ
  /-- A state is at a collective exactly when its pc is the one of its count. -/
  at_ : ∀ {x k σ}, A x → Frame.stateAt (thread P L) X x k = some (some σ) →
    (CollAt P L x σ ↔ cn (nc x σ) = some ((thread P L x).pc σ))
  /-- A collective event is fired from a state at a collective. -/
  isP : ∀ {x k σ e}, A x → Frame.stateAt (thread P L) X x k = some (some σ) →
    X.get (x, k) = some e → Sched.isWarpColl e = true → CollAt P L x σ
  slot_mono : ∀ {a b}, a < b → (cn b).isSome = true → slot a < slot b
  time_at : ∀ {x k σ}, A x → Frame.stateAt (thread P L) X x k = some (some σ) →
    CollAt P L x σ → time P L x σ = slot (nc x σ)
  time_lt : ∀ {x k σ}, A x → Frame.stateAt (thread P L) X x k = some (some σ) →
    ¬ CollAt P L x σ → ∀ n, (cn n).isSome = true → nc x σ ≤ n → time P L x σ < slot n
  static : ∀ {x y k k' σ σ'}, A x → A y → Frame.stateAt (thread P L) X x k = some (some σ) →
    Frame.stateAt (thread P L) X y k' = some (some σ') → CollAt P L x σ → CollAt P L y σ' →
    nc x σ = nc y σ' → S x σ = S y σ'
  /-- A lane exits after every collective of the warp. -/
  exit : ∀ {y k pc σ}, A y → Frame.stateAt (thread P L) X y k = some (some σ) →
    X.get (y, k) = some ⟨pc, .exit⟩ → ∀ n, (cn n).isSome = true → n < nc y σ
  /-- After a blocking event the machine runs on, to a state at no collective, or a register
  request to a collective at which every lane of the warp has made a request, or a `bar.sync`
  to a collective at which every lane of the warp has made its `bar.sync` of the same ordinal. -/
  last : ∀ {x k σ e}, A x → X.get (x, k) = some e →
    Frame.stateAt (thread P L) X x k = some (some σ) → ¬ Sched.Unblocking e.kind →
    (thread P L x).next σ e ≠ none ∧ ∀ σ', (thread P L x).next σ e = some (some σ') →
      ¬ CollAt P L x σ' ∨ ((∃ inc n i, e.kind = .setMaxReg inc n i) ∧
        ∀ y σy, A y → SameWarp L y x →
          Frame.stateAt (thread P L) X y (X.tr y).length = some (some σy) → CollAt P L y σy →
          nc y σy = nc x σ' → ∃ j pc inc n i, X.get (y, j) = some ⟨pc, .setMaxReg inc n i⟩) ∨
      (∃ id cnt, e.kind = .bar id cnt .sync ∧
        ∀ y σy, A y → SameWarp L y x →
          Frame.stateAt (thread P L) X y (X.tr y).length = some (some σy) → CollAt P L y σy →
          nc y σy = nc x σ' → ∃ pc cnt', X.get (y, (X.tr y).length - 1) =
            some ⟨pc, .bar id cnt' .sync⟩ ∧
            ((X.tr y).take ((X.tr y).length - 1)).countP (Execution.isBarId id) =
              ((X.tr x).take k).countP (Execution.isBarId id))

/-- **The collectives of two lanes of a warp**, from a classification. -/
theorem warpPair_of_cls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X)
    (hgrp : ∀ {g i pc id : Nat} {cnt : Option Nat} {md : BarMode}, g < L.threads →
      X.get (g, i) = some ⟨pc, .bar id cnt md⟩ →
      ∃ q : Finset Nat, NamedBar.Shape L cnt q id ∧ NamedBar.Sources L X cnt q id)
    {A : Nat → Prop}
    {S : ∀ g, (thread P L g).D → Sched.CollShape} (C : CollCls P L X A S)
    (hs : SameWarp L g h) (hAg : A g) (hAh : A h) :
    Sched.WarpPair m ⟨thread P L, time P L⟩ X (CollAt P L) S g h := by
  have hg := hs.1.1
  have hh := hs.1.2.1
  have hF := follow_iff.mp hFw
  have hCnt : ∀ {x σ}, A x → Frame.stateAt (thread P L) X x (X.tr x).length = some (some σ) →
      (X.tr x).countP Sched.isWarpColl = C.nc x σ := fun hA hσ => by
    have := C.count hA hσ
    rwa [List.take_length] at this
  have hPos : ∀ {x k σ}, A x → Sched.CollPos ⟨thread P L, time P L⟩ X (CollAt P L) x k σ →
      C.cn (C.nc x σ) = some ((thread P L x).pc σ) := by
    rintro x k σ hA ⟨hσ, ⟨e, he, hc⟩ | ⟨-, hat⟩⟩
    · exact (C.at_ hA hσ).mp (C.isP hA hσ he hc)
    · exact (C.at_ hA hσ).mp hat
  refine ⟨fun {k k' σ σ'} hP hP' hn => ?_, fun {σ σ'} hσ hcg hσ' hch hn hrel => ?_,
    fun {k pc σ σ'} hσ hcg hσ' he => ?_, fun {σ} hσ hcg hle hno hnn => ?_, fun hph hσ' => ?_⟩
  · -- one position, one static part
    have hnc : C.nc g σ = C.nc h σ' := by
      rw [← C.count hAg hP.1, ← C.count hAh hP'.1, hn]
    have e1 := hPos hAg hP
    have e2 := hPos hAh hP'
    rw [hnc] at e1
    have hpc : (thread P L g).pc σ = (thread P L h).pc σ' := by
      have := e1.symm.trans e2
      exact Option.some.inj this
    refine ⟨hpc, C.static hAg hAh hP.1 hP'.1 ?_ ?_ hnc⟩
    · exact (C.at_ hAg hP.1).mpr (by rw [hnc]; exact e1)
    · exact (C.at_ hAh hP'.1).mpr e2
  · -- released
    left
    by_contra hnr
    have hlen : 0 < (X.tr h).length := by
      by_contra h0
      exact hnr (Sched.released_nil (List.length_eq_zero_iff.mp
        (show (X.tr h).length = 0 by omega)))
    obtain ⟨e, he⟩ : ∃ e, X.get (h, (X.tr h).length - 1) = some e :=
      ⟨_, List.getElem?_eq_getElem
        (show (X.tr h).length - 1 < (X.tr h).length by omega)⟩
    have hne : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := fun pc f hf => hub ⟨_, pc, f, by rw [he, hf]⟩
    obtain ⟨σ0, hσ0, -⟩ := Frame.good_stateU (J := (table P L).J)
      (fun _ _ => thread_sound hp) hX he hne (hF h hh _)
    have hun : ¬ Sched.Unblocking e.kind := fun hu => hnr (Sched.released_of_unblocking he hu)
    have hσ1 : Frame.stateAt (thread P L) X h ((X.tr h).length - 1 + 1) = some (some σ') := by
      rw [show (X.tr h).length - 1 + 1 = (X.tr h).length by omega]; exact hσ'
    rw [Frame.stateAt_succ (C := thread P L) (show (X.tr h)[(X.tr h).length - 1]? = some e
        from he), hσ0] at hσ1
    rcases (C.last hAh he hσ0 hun).2 σ' hσ1 with h1 | ⟨⟨inc, nn, i, hk⟩, hreq⟩ |
        ⟨id, cnt, hk, hbar⟩
    · exact h1 hch
    · have hnc : C.nc g σ = C.nc h σ' := by rw [← hCnt hAg hσ, ← hCnt hAh hσ', hn]
      obtain ⟨j, pc', inc', n', i', hj⟩ := hreq g σ hAg hs hσ hcg hnc
      obtain ⟨pc, kd⟩ := e
      simp only at hk
      subst hk
      refine hnr (released_of_setMax hX hh he ?_)
      rintro ⟨pc2, inc2, nn2, inst2, hreq2, hnr2⟩
      have hsame := reg_match hp hX hFw hub (e := (g, j)) (f := (h, (X.tr h).length - 1))
        hg hh hs hj hreq2
      refine hnr2 (SetMaxNReg.ready_of_sameRequest hj hsame ?_)
      have hjl : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hj).1
      rcases Nat.lt_or_ge (j + 1) (X.tr g).length with h1 | h1
      · exact hX.dependency.ready _ (by simp [Returned, hj, Kind.resume, h1])
      · obtain rfl : j = (X.tr g).length - 1 := by omega
        exact hrel.ready _ _ hj rfl
    · have hnc : C.nc g σ = C.nc h σ' := by rw [← hCnt hAg hσ, ← hCnt hAh hσ', hn]
      obtain ⟨pcg, cntg, hgl, hord⟩ := hbar g σ hAg hs hσ hcg hnc
      obtain ⟨pc, kd⟩ := e
      simp only at hk
      subst hk
      obtain ⟨q, hG, hS⟩ := hgrp hh he
      refine hnr (Sched.released_of_mate hX hS hG hh hs.1.2.2 hgl he ?_ hrel)
      exact hord
  · -- exit
    have hc := (C.at_ hAg hσ).mp hcg
    have := C.exit hAh hσ' he (C.nc g σ) (by rw [hc]; rfl)
    rw [← C.count hAh hσ'] at this
    rwa [hCnt hAg hσ]
  · -- lag
    have hc := (C.at_ hAg hσ).mp hcg
    cases hσ' : Frame.stateAt (thread P L) X h (X.tr h).length with
    | none => exact absurd hσ' hnn
    | some o =>
      cases o with
      | none => exact absurd hσ' (hF h hh _).1
      | some σ' =>
        refine lt_of_eq_of_lt (Sched.threadTime_of (M := ⟨thread P L, time P L⟩) hσ') ?_
        show time P L h σ' < time P L g σ
        rw [C.time_at hAg hσ hcg]
        have hle' : C.nc h σ' ≤ C.nc g σ := by rw [← hCnt hAg hσ, ← hCnt hAh hσ']; exact hle
        by_cases hch : CollAt P L h σ'
        · have hne : C.nc h σ' ≠ C.nc g σ := fun heq =>
            hno ⟨by rw [hCnt hAg hσ, hCnt hAh hσ', heq], σ', hσ', hch⟩
          rw [C.time_at hAh hσ' hch]
          exact C.slot_mono (lt_of_le_of_ne hle' hne) (by rw [hc]; rfl)
        · exact C.time_lt hAh hσ' hch _ (by rw [hc]; rfl) hle'
  · -- a stopped lane is released
    by_contra hnr
    obtain ⟨i, σ, hi, h1, h2⟩ := Frame.first_stop (C := thread P L)
      (fun x k hx => (hF x hx k).1) hh hσ'
    have hlt : i + 1 = (X.tr h).length := by
      by_contra hne
      obtain ⟨e, he⟩ : ∃ e, X.get (h, i + 1) = some e :=
        ⟨_, List.getElem?_eq_getElem (show i + 1 < (X.tr h).length by omega)⟩
      rcases Frame.firedU (C := thread P L) (fun g hg => thread_sound hp) hX he with
        ⟨σ', o, h3, -⟩ | ⟨-, pc, f, rfl⟩
      · rw [h2] at h3; cases h3
      · exact hub ⟨_, pc, f, he⟩
    obtain ⟨e, he⟩ : ∃ e, X.get (h, i) = some e := ⟨_, List.getElem?_eq_getElem hi⟩
    have hun : ¬ Sched.Unblocking e.kind := fun hu => hnr (Sched.released_of_unblocking
      (show X.get (h, (X.tr h).length - 1) = some e by
        rw [show (X.tr h).length - 1 = i by omega]; exact he) hu)
    rw [Frame.stateAt_succ (C := thread P L) (show (X.tr h)[i]? = some e from he), h1] at h2
    exact (C.last hAh he h1 hun).1 h2

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
