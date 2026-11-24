-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Final
public import Lemmas.Protocol.PairTmaRing.Blocker
public import Kernels.Fp16Gemm8192.Proof.Protocol.Elected

@[expose] public section

/-! # Who blocks an MMA thread at a full wait

A blocked MMA thread waits for its slot's full barrier in the leader CTA to complete the phase it is
in (`InputFullBlocked`). The full barrier's accounting says that phase either still awaits its
arrival, or has fewer than six completed copies (`PairTmaRing.full_short`). A pending arrival is
the leader CTA's loader's: that loader has arrived fewer times than the phase, since each of its
arrivals is an arrival unit of the barrier (`PairTmaRing.arrivals_le_units`). Otherwise the copies
are not all complete: a copy issued on the barrier is not notified (`PairTmaRing.unnotified`), or
the copies of the two CTAs' elected loaders, each a completion of the barrier, fall short of three
per phase (`PairTmaRing.issues_le_completions`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The full object of a slot is the slot's full barrier in the leader CTA. -/
theorem slot_full_eq (L : Launch) (c : Nat) (s : Fin 4) :
    (slot L c s).full 0 = fullLoc L c s :=
  (fullLoc_bar L c s).symm

/-- The lane `0` of warp 11 of CTA `d` (for a CTA `d` of the grid). -/
theorem warp11_lane (hpre : Pre P L mem0) {d : Nat} (hd : d < L.grid) :
    d * L.block + 32 * 11 < L.threads ∧ (d * L.block + 32 * 11) / L.block = d ∧
      (d * L.block + 32 * 11) % L.block / 32 = 11 := by
  have hb := hpre.block
  unfold Launch.threads
  rw [hb]
  exact ⟨by omega, by omega, by omega⟩

/-- **The blocker of a full phase.** The full barrier of slot `s` in cluster `c`, in the phase
`before` it is in, is not complete at the end of the execution, and one of its blockers holds. -/
theorem full_blocked (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (c : Nat) (s : Fin 4) (hc : 2 * c < L.grid) {before : MBarrier.State}
    (hstate : MBarrier.stateBefore (X.objects (fullLoc L c s))
      (X.objects (fullLoc L c s)).length = some before) :
    (∃ i mapAddress s', X.TensorIssue i mapAddress s' ∧ s'.mbar = fullLoc L c s ∧
        ¬ ∃ obs, X.tensor i = some obs ∧ obs.effects.notified = true) ∨
    (∃ h, h < L.threads ∧ h / L.block / 2 = c ∧ h % L.block / 32 = 11 ∧
        (∃ j pc' mask inst, X.Elect (h, j) pc' mask inst (laneOf L h)) ∧
        (X.tr h).countP (issuesTo (fullLoc L c s)) < 3 * (before.phase + 1)) ∨
    (∃ h, h < L.threads ∧ h / L.block = 2 * c ∧ h % L.block / 32 = 11 ∧
        (∃ j pc' mask inst, X.Elect (h, j) pc' mask inst (laneOf L h)) ∧
        arrivals (fullLoc L c s) (X.tr h) < before.phase + 1) ∨
    (∃ h, h < L.threads ∧ h / L.block / 2 = c ∧ h % L.block / 32 = 11 ∧
        ∀ j pc' mask inst leader, ¬ X.Elect (h, j) pc' mask inst leader) := by
  have hblock := hpre.block
  have hgrid := hpre.grid
  have hF : (slot L c s).full 0 = fullLoc L c s := slot_full_eq L c s
  have hst' : stateBefore (X.objects ((slot L c s).full 0))
      (X.objects ((slot L c s).full 0)).length = some before := by rw [hF]; exact hstate
  have H := hyp hpre hX ht c s
  have hshort := PairTmaRing.full_short hX H hst'
  simp only [pslot, hF] at hshort
  rcases hshort with harr1 | ⟨harr0, hlt⟩
  swap
  · -- the phase's arrival is in, and its copies are not all complete
    by_cases hE1 : ∃ h, h < L.threads ∧ h / L.block = 2 * c + 1 ∧ h % L.block / 32 = 11 ∧
        ∃ j pc' mask inst, X.Elect (h, j) pc' mask inst (laneOf L h)
    · by_cases hE0 : ∃ h, h < L.threads ∧ h / L.block = 2 * c ∧ h % L.block / 32 = 11 ∧
          ∃ j pc' mask inst, X.Elect (h, j) pc' mask inst (laneOf L h)
      · obtain ⟨h0, hh0, hh0c, hh0w, hel0⟩ := hE0
        obtain ⟨h1, hh1, hh1c, hh1w, hel1⟩ := hE1
        by_cases hM : ∀ i mapAddress s', X.TensorIssue i mapAddress s' →
            s'.mbar = fullLoc L c s → ∃ r ∈ X.objects (fullLoc L c s), r.id =
              .async i (.notify .load)
        · -- every copy on the barrier is notified: the two loaders' copies are its completions
          have hne : h0 ≠ h1 := by
            intro e
            subst e
            omega
          have hsum := PairTmaRing.issues_le_completions hX H hne (fun i ma s' hT hmb => by
            simp only [pslot, hF] at hmb ⊢
            exact hM i ma s' hT hmb)
          simp only [pslot, hF] at hsum
          by_cases hc0 : (X.tr h0).countP (issuesTo (fullLoc L c s)) < 3 * (before.phase + 1)
          · exact Or.inr (Or.inl ⟨h0, hh0, by omega, hh0w, hel0, hc0⟩)
          · exact Or.inr (Or.inl ⟨h1, hh1, by omega, hh1w, hel1, by omega⟩)
        · -- a copy on the barrier is not notified
          push Not at hM
          obtain ⟨i, mapAddress, s', hT, hmb, hnr⟩ := hM
          exact Or.inl ⟨i, mapAddress, s', hT, hmb, PairTmaRing.unnotified hX hT hmb hnr⟩
      · -- no loader of CTA `2c` is elected: its warp-11 lane `0` has no election event
        obtain ⟨hl0, hd0, hw0⟩ := warp11_lane hpre (d := 2 * c) hc
        refine Or.inr (Or.inr (Or.inr ⟨2 * c * L.block + 32 * 11, hl0, ?_, hw0, ?_⟩))
        · rw [hd0]
          omega
        · intro j pc' mask inst leader hel
          obtain ⟨h', j', hh', ⟨⟨-, -, hdiv'⟩, hwarp'⟩, hE'⟩ := elected_of_elect hpre hX hel
          exact hE0 ⟨h', hh', by omega, by omega, j', pc', mask, inst, hE'⟩
    · -- no loader of CTA `2c + 1` is elected: its warp-11 lane `0` is not
      obtain ⟨hl1, hd1, hw1⟩ := warp11_lane hpre (d := 2 * c + 1) (by omega)
      refine Or.inr (Or.inr (Or.inr ⟨(2 * c + 1) * L.block + 32 * 11, hl1, ?_, hw1, ?_⟩))
      · rw [hd1]
        omega
      · intro j pc' mask inst leader hel
        obtain ⟨h', j', hh', ⟨⟨-, -, hdiv'⟩, hwarp'⟩, hE'⟩ := elected_of_elect hpre hX hel
        exact hE1 ⟨h', hh', by omega, by omega, j', pc', mask, inst, hE'⟩
  · -- the phase's arrival is pending: the leader CTA's loader has not arrived for it
    by_cases hE0 : ∃ h, h < L.threads ∧ h / L.block = 2 * c ∧ h % L.block / 32 = 11 ∧
        ∃ j pc' mask inst, X.Elect (h, j) pc' mask inst (laneOf L h)
    · obtain ⟨h, hh, hhc, hhw, hel⟩ := hE0
      refine Or.inr (Or.inr (Or.inl ⟨h, hh, hhc, hhw, hel, ?_⟩))
      have := PairTmaRing.arrivals_le_units hX H h
      simp only [pslot, hF] at this
      omega
    · obtain ⟨hl0, hd0, hw0⟩ := warp11_lane hpre (d := 2 * c) hc
      refine Or.inr (Or.inr (Or.inr ⟨2 * c * L.block + 32 * 11, hl0, ?_, hw0, ?_⟩))
      · rw [hd0]
        omega
      · intro j pc' mask inst leader hel
        obtain ⟨h', j', hh', ⟨⟨-, -, hdiv'⟩, hwarp'⟩, hE'⟩ := elected_of_elect hpre hX hel
        exact hE0 ⟨h', hh', by omega, by omega, j', pc', mask, inst, hE'⟩

/-- **The blocked MMA thread's phase is its successful polls of the full barrier.** The thread's
failed poll is its last event. The successful polls of its consumer on the full barrier are its own
(`consumer_unique`), so the consumer's count is the thread's successful polls. The phase is that
count or one more (the ring invariant), and the parities agree (`poll_parity`). -/
theorem phase_eq_polls (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g : Nat} {m : Mma.D} {s : Fin 4} {pc : Nat} {sc : MbarScope}
    {before : MBarrier.State} (hg : g < L.threads) (hlead : g / L.block % 2 = 0)
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.mma m))))
    (hlast : (X.tr g).getLast? =
      some ⟨pc, .wait (fullLoc L (g / L.block / 2) s) (m.fp % 2) false true sc⟩)
    (hstate : MBarrier.stateBefore (X.objects (fullLoc L (g / L.block / 2) s))
      (X.objects (fullLoc L (g / L.block / 2) s)).length = some before)
    (hpar : before.phase % 2 = m.fp % 2) :
    before.phase = Flow.okPolls (fullLoc L (g / L.block / 2) s) (X.tr g) := by
  have hblock := hpre.block
  obtain ⟨c, hc⟩ : ∃ c, g / L.block / 2 = c := ⟨_, rfl⟩
  rw [hc] at hlast hstate ⊢
  have hgc : g / L.block = 2 * c := by omega
  -- the failed poll is the last event of the thread
  obtain ⟨pre, hpre_eq⟩ := List.getLast?_eq_some_iff.mp hlast
  have hk : X.get (g, pre.length) =
      some ⟨pc, .wait (fullLoc L c s) (m.fp % 2) false true sc⟩ := by
    show (X.tr g)[pre.length]? = _
    rw [hpre_eq]
    simp
  have htake : (X.tr g).take pre.length = pre := by
    rw [hpre_eq]
    exact List.take_left' rfl
  have hPe : Flow.okPolls (fullLoc L c s) (X.tr g) = Flow.okPolls (fullLoc L c s) pre := by
    rw [hpre_eq]
    apply okPolls_snoc_zero
    simp [okPoll, sourceWaitSuccess]
  obtain ⟨d, hσk⟩ : ∃ d, Frame.stateAt (code L) X g pre.length = some (some d) := by
    obtain ⟨d', hσ'⟩ := Frame.event_state ht.sound hX ht.tracked hk nofun
    exact ⟨d', hσ'⟩
  -- the failed poll's parity is the parity of the thread's successful polls
  have hpp := ht.poll_parity (b := ⟨.input, s.val, true⟩) (cta := 2 * c) (p := m.fp % 2)
    (ok := false) (acq := true) (sc := sc) hg hk hσk (by rw [fullLoc_bar])
    (by simp only [Bar.Valid, Ring.slots]; exact s.isLt)
  have hoff : (⟨.input, s.val, true⟩ : Bar).pollOffset = 0 := rfl
  rw [hoff, htake, ← fullLoc_bar] at hpp
  -- the thread is the consumer of its warp
  have hrole := ht.role_warp hg (le_refl _) hσ
  simp only [roleWarp] at hrole
  obtain ⟨-, hw89⟩ := hrole
  let b : Fin 2 := ⟨g % L.block / 32 - 8, by omega⟩
  have hcons : consumerThread L c b g = true := by
    simp only [consumerThread, decide_eq_true_eq]
    refine ⟨hgc, ?_⟩
    show g % L.block / 32 = 8 + (g % L.block / 32 - 8)
    omega
  have hN := consumer_okPolls hpre hX ht hcons hk (by rw [slot_full_eq])
  rw [slot_full_eq] at hN
  have hst' : stateBefore (X.objects ((slot L c s).full 0))
      (X.objects ((slot L c s).full 0)).length = some before := by rw [slot_full_eq]; exact hstate
  obtain ⟨h1, h2⟩ := PairTmaRing.full_final_phase hX (hyp hpre hX ht c s) b hst'
  simp only [pslot] at h1 h2
  rw [slot_full_eq, ← hN] at h1 h2
  omega

/-- **The input ring's blocked MMA thread at a full wait** (the export `InputFullBlocked`). -/
theorem inputFullBlocked (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : InputFullBlocked L X := by
  intro g m s pc sc before hg hlead hσ _ hlast hstate hpar
  have hblock := hpre.block
  have hgrid : g / L.block < L.grid := by
    have : g < L.grid * L.block := hg
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact this
  have hdiv : 2 * (g / L.block / 2) = g / L.block := by omega
  have hc : 2 * (g / L.block / 2) < L.grid := by omega
  refine ⟨phase_eq_polls hpre hX ht hg hlead hσ hlast hstate hpar, ?_⟩
  rcases full_blocked hpre hX ht (g / L.block / 2) s hc hstate with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨h', hh, hdh, hw, hel, harr⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨h', hh, hdh.trans hdiv, hw, hel, harr⟩))
  · exact Or.inr (Or.inr (Or.inr h))

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
