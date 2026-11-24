-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCollSched
public import Lemmas.Flow.WarpAgree
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarp

@[expose] public section

/-! # The lanes of a warp at the warp collectives (`WarpCollFacts.exit`, `lag`)

* `exit`: lanes exit with one count of warp collectives, above the count of every lane of the
  warp at a warp collective (`WarpExitAgree`, `WarpExitAbove`), so a bound fixed by the warp
  exists (`exists_bound_of_exit`).
* `lag`: the warp collectives' schedule (`WarpSched`: a `CollSched` of `Sched.isWarpColl` with
  strict clauses at the trace's end, for a stopped machine and between ordinals) places every lane
  that has made at most `n` warp collectives, and is not at its `n`-th, before the time `S key n` of
  a lane at its `n`-th; the positivity of that time is `WarpLagPos`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The warp collectives' schedule of each warp, with its strict clauses (per role: the prologue's,
the loader's, the MMA warp's, the softmax and correction warps' collective sites). -/
structure WarpSched (L : Launch) (X : Execution) (S : Nat × Nat → Nat → Nat) : Prop where
  sched : Sched.CollSched (timed L) X Sched.isWarpColl (warpKey L) (fun _ => True) S
  /-- A state at the trace's end at a warp collective is at the collective's time. -/
  endAt : ∀ {g : Nat} {d : ThreadD}, g < L.threads → St L X g (X.tr g).length = some (some d) →
    nextKind d = .warp → stateTime L g d = S (warpKey L g) ((X.tr g).countP Sched.isWarpColl)
  /-- A state at the trace's end at no warp collective is earlier than the next one. -/
  endLt : ∀ {g : Nat} {d : ThreadD}, g < L.threads → St L X g (X.tr g).length = some (some d) →
    nextKind d ≠ .warp → stateTime L g d < S (warpKey L g) ((X.tr g).countP Sched.isWarpColl)
  /-- A machine stopped at an event other than a warp collective is earlier than the next one,
  by more than one. -/
  stopLt : ∀ {g : Nat} {d : ThreadD} {e : Event}, g < L.threads →
    St L X g (X.tr g).length = none → St L X g ((X.tr g).length - 1) = some (some d) →
    X.get (g, (X.tr g).length - 1) = some e → Sched.isWarpColl e = false →
    stateTime L g d + 1 < S (warpKey L g) ((X.tr g).countP Sched.isWarpColl)
  /-- Consecutive collectives are more than one apart. -/
  gap : ∀ c n, S c n + 1 < S c (n + 1)

/-- The positivity clause of `lag` (prologue package: a lane at its `n`-th warp collective with a
lagging lane of its warp is past the first state). -/
def WarpLagPos (L : Launch) (X : Execution) : Prop :=
  ∀ {g h : Nat} {d : ThreadD}, g < L.threads → h < L.threads → SameWarp L g h →
    St L X g (X.tr g).length = some (some d) → nextKind d = .warp →
    (X.tr h).countP Sched.isWarpColl ≤ (X.tr g).countP Sched.isWarpColl →
    ¬ ((X.tr h).countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl ∧
      ∃ d', St L X h (X.tr h).length = some (some d') ∧ nextKind d' = .warp) →
    0 < stateTime L g d

/-- **`WarpCollFacts.lag`.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.WarpCollFacts_lag {S : Nat × Nat → Nat → Nat}
    (hs : WarpSched L X S) (hpos : WarpLagPos L X) :
    ∀ {g h : Nat} {d : ThreadD}, g < L.threads → h < L.threads → SameWarp L g h →
      St L X g (X.tr g).length = some (some d) → nextKind d = .warp →
      (X.tr h).countP Sched.isWarpColl ≤ (X.tr g).countP Sched.isWarpColl →
      ¬ ((X.tr h).countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl ∧
        ∃ d', St L X h (X.tr h).length = some (some d') ∧ nextKind d' = .warp) →
      0 < stateTime L g d ∧ endTime L X h < stateTime L g d := by
  intro g h d hg hh hw hσ hk hc hn
  have hp := hpos hg hh hw hσ hk hc hn
  refine ⟨hp, ?_⟩
  have hkey := warpKey_eq hw
  rw [hs.endAt hg hσ hk, hkey] at hp ⊢
  rcases Nat.lt_or_ge ((X.tr h).countP Sched.isWarpColl) ((X.tr g).countP Sched.isWarpColl) with hlt
      | hge
  · exact (Sched.threadTime_le_sched hs.sched hh trivial).trans_lt (Sched.sched_lt
      hs.sched.mono _ hlt)
  have heq : (X.tr h).countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl := by omega
  rw [← heq] at hp ⊢
  unfold Sched.threadTime; dsimp only [timed]
  split
  · rename_i d' hσ'
    exact hs.endLt hh hσ' fun hk' => hn ⟨heq, d', hσ', hk'⟩
  · exact hp
  · rename_i hσ0
    split
    · rename_i d' hσ'
      have hlen := Sched.len_pos_of_stop hσ0
      have hj : (X.tr h).length - 1 < (X.tr h).length := by omega
      have he : X.get (h, (X.tr h).length - 1) = some (X.tr h)[(X.tr h).length - 1] :=
        List.getElem?_eq_getElem hj
      have hsp := Sched.split_last (X := X) (g := h) hlen
      cases hpe : Sched.isWarpColl (X.tr h)[(X.tr h).length - 1]
      · exact hs.stopLt hh hσ0 hσ' he hpe
      · have h1 : stateTime L _ _ = _ := hs.sched.atEv hh trivial hσ' he hpe
        have h2 := congrArg (List.countP Sched.isWarpColl) hsp
        rw [List.countP_append] at h2
        simp only [List.countP_singleton, hpe] at h2
        simp at h2
        rw [h2, h1]
        exact hs.gap _ _
    · exact hp

/-- Two lanes of a warp exit with one count of warp collectives. -/
def WarpExitAgree (L : Launch) (X : Execution) : Prop :=
  ∀ {g h k k' pc pc' : Nat} {d d' : ThreadD}, SameWarp L g h →
    St L X g k = some (some d) → St L X h k' = some (some d') →
    X.get (g, k) = some ⟨pc, .exit⟩ → X.get (h, k') = some ⟨pc', .exit⟩ →
    ((X.tr g).take k).countP Sched.isWarpColl = ((X.tr h).take k').countP Sched.isWarpColl

/-- A lane at its exit has made more warp collectives than a lane of its warp at a warp
collective. -/
def WarpExitAbove (L : Launch) (X : Execution) : Prop :=
  ∀ {g h k pc : Nat} {d d' : ThreadD}, SameWarp L g h →
    St L X g (X.tr g).length = some (some d) → nextKind d = .warp →
    St L X h k = some (some d') → X.get (h, k) = some ⟨pc, .exit⟩ →
    (X.tr g).countP Sched.isWarpColl < ((X.tr h).take k).countP Sched.isWarpColl

/-- **`WarpCollFacts.exit`.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.WarpCollFacts_exit (hagree : WarpExitAgree L X)
    (habove : WarpExitAbove L X) :
    ∃ T : Nat × Nat → Nat,
      (∀ {g : Nat} {d : ThreadD}, g < L.threads → St L X g (X.tr g).length = some (some d) →
        nextKind d = .warp → (X.tr g).countP Sched.isWarpColl < T (warpKey L g)) ∧
      (∀ {g k pc : Nat} {d : ThreadD}, g < L.threads → St L X g k = some (some d) →
        X.get (g, k) = some ⟨pc, .exit⟩ →
        T (warpKey L g) ≤ ((X.tr g).take k).countP Sched.isWarpColl) := by
  obtain ⟨T, h1, h2⟩ := exists_bound_of_exit (warpKey L) L.threads
    (fun g o => ∃ d, St L X g (X.tr g).length = some (some d) ∧ nextKind d = .warp ∧
      o = (X.tr g).countP Sched.isWarpColl)
    (fun g => (X.tr g).length + 1)
    (by
      rintro g o - ⟨d, -, -, rfl⟩
      have := List.countP_le_length (p := Sched.isWarpColl) (l := X.tr g)
      omega)
    (fun g c => ∃ k pc d, St L X g k = some (some d) ∧ X.get (g, k) = some ⟨pc, .exit⟩ ∧
      c = ((X.tr g).take k).countP Sched.isWarpColl)
    (by
      rintro g h c c' hg hh hk ⟨k, pc, d, hσ, he, rfl⟩ ⟨k', pc', d', hσ', he', rfl⟩
      exact hagree (sameWarp_of_key hg hh hk) hσ hσ' he he')
    (by
      rintro g h c o hg hh hk ⟨k, pc, d', hσ', he', rfl⟩ ⟨d, hσ, hkd, rfl⟩
      exact habove (sameWarp_of_key hg hh hk) hσ hkd hσ' he')
  exact ⟨T, fun {g d} hg hσ hk => h1 hg ⟨d, hσ, hk, rfl⟩,
    fun {g k pc d} hg hσ he => h2 hg ⟨k, pc, d, hσ, he, rfl⟩⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
