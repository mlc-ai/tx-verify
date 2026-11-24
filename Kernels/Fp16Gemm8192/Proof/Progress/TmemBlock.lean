-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.TmemLanes

@[expose] public section

/-! # Who an uncovered Tensor Memory operation waits for

An uncovered paired Tensor Memory operation of a lane of a pair, in a safe execution: take the
first `n` whose operations are not all made and covered by the pair (`PairDone`). If every lane
has made its `n`-th operation, a step completing the `n`-th operations is ready (`pair_ready`);
otherwise a lane that has made at most `n` operations, no more than the uncovered one's, is
pending (`pair_dichotomy`). Such a lane is earlier in the rank table than a thread that has just
made a later operation (`time_lt_of_tmem`): the rank table places the operations of warp 0 at
the allocation, in the prologue, and at the relinquishment and the deallocation, in the exit
stage. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Tmem.Pair Classical

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The `n`-th operations of the pair of `key` are made and covered. -/
def PairDone (L : Launch) (X : Execution) (key n : Nat) : Prop :=
  ∀ s, s < 2 → ∀ ℓ : Fin 32, ∃ j, TmemOp X (pairLane L 0 key s ℓ) n j ∧
    Covered L X (pairLane L 0 key s ℓ, j)

/-- **The dichotomy at an uncovered operation**: a ready step of its pair, or a pending lane
of the pair that has made no more operations than the uncovered one's. -/
theorem pair_dichotomy (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hX : Consistent L kernel Prod mem0 X) (hub : ¬ HasUb X) (htc : ¬ AlignedMismatch L kernel X)
    {g j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request} (hg : g < L.threads)
    (he : X.get (g, j) = some ⟨pc, .tc (.resource grp dst act)⟩) (hn : ¬ Covered L X (g, j)) :
    ((∃ c r, Step.EntryReady L X c r) ∨ ∃ q, Step.PairingReady L X q) ∨
      ∃ h, Frame.Pending L X h ∧ h % L.block / 32 = 0 ∧
        tmemOps (X.tr h) ≤ tmemOps ((X.tr g).take j) := by
  have hb := hpre.block
  have hgr := hpre.grid
  have hcl := hpre.cluster
  obtain ⟨h0, -, -, hsh, -⟩ := ht.tmem_event hg (noUb_of hub g) he
  have hm3 := lt_of_tmemShape hsh
  have hgc : g / L.block < L.grid :=
    (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [Launch.threads] using hg)
  generalize hq : g / L.block = q at hgc
  obtain ⟨key, hkd⟩ : ∃ key, key = q - q % 2 := ⟨_, rfl⟩
  have hkey : key % 2 = 0 := by omega
  have hk : key + 1 < L.grid := by omega
  obtain ⟨s0, ℓ0, hs0, hℓ0, hg0⟩ := pairLane_of hkey (by rw [hq]; omega) h0
  have hop0 : TmemOp X (pairLane L 0 key s0 ℓ0) (tmemOps ((X.tr g).take j)) j := by
    rw [← hg0]
    exact ⟨⟨_, _, _, _, he⟩, rfl⟩
  have hnd : ¬ PairDone L X key (tmemOps ((X.tr g).take j)) := by
    intro hd
    obtain ⟨j', hop', hc⟩ := hd s0 hs0 ⟨ℓ0, hℓ0⟩
    have hc' : Covered L X (pairLane L 0 key s0 ℓ0, j) := by
      rw [tmemOp_unique hop' hop0] at hc
      exact hc
    rw [← hg0] at hc'
    exact hn hc'
  have hex : ∃ n, ¬ PairDone L X (key) n := ⟨_, hnd⟩
  obtain ⟨n, hnd', hdone⟩ : ∃ n, ¬ PairDone L X key n ∧ ∀ m < n, PairDone L X key m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_not.mp (Nat.find_min hex hm)⟩
  have hnm : n ≤ tmemOps ((X.tr g).take j) := by
    by_contra hlt
    exact hnd (hdone _ (by omega))
  by_cases hiss : ∀ s, s < 2 → ∀ ℓ : Fin 32,
      n < tmemOps (X.tr (pairLane L 0 key s ℓ))
  · left
    simp only [PairDone, not_forall, not_exists, not_and] at hnd'
    obtain ⟨s1, hs1, ℓ1, hno⟩ := hnd'
    obtain ⟨j1, hop1⟩ := tmemOp_exists (hiss s1 hs1 ℓ1)
    refine pair_ready hX (ht.warpOps hpre) htc (n := n) hkey hk (fun s hs ℓ => ?_)
      (fun m hm s hs ℓ j hop => ?_)
    · obtain ⟨jj, hopj⟩ := tmemOp_exists (hiss s hs ℓ)
      exact ⟨jj, hopj, fun hc => hno j1 hop1
        (covered_all hX (ht.warpOps hpre) hkey hs ℓ.isLt hs1 ℓ1.isLt hopj hc hop1)⟩
    · obtain ⟨j', hop', hc⟩ := hdone m hm s hs ℓ
      rwa [tmemOp_unique hop hop']
  · right
    push Not at hiss
    obtain ⟨s, hs, ℓ, hle⟩ := hiss
    have hℓ := ℓ.isLt
    have hdm := pairLane_div_mod (ht.warpOps hpre) (key := key) (s := s) ℓ.isLt
    have hlt := pairLane_lt (ht.warpOps hpre) hk hs ℓ.isLt
    refine ⟨_, ⟨hlt, ?_, ?_⟩, by rw [hdm.2]; omega, by omega⟩
    · have hne : X.tr g ≠ [] := by
        intro h0'
        have := len_of_get he
        rw [h0'] at this
        simp at this
      apply not_canceled_of_peer hX hg hne
      rw [hdm.1]
      rw [clusterOfCta_eq hpre, clusterOfCta_eq hpre, hq]
      omega
    · intro pc' hl
      have hlen : 0 < (X.tr (pairLane L 0 key s ℓ)).length := by
        rcases h : X.tr (pairLane L 0 key s ℓ) with _ | ⟨x, xs⟩
        · rw [h] at hl; cases hl
        · simp
      have hget : X.get (pairLane L 0 key s ℓ,
          (X.tr (pairLane L 0 key s ℓ)).length - 1) = some ⟨pc', .exit⟩ := by
        change (X.tr _)[_]? = _
        rw [← List.getLast?_eq_getElem?]
        exact hl
      have h3 := ht.tmem_exit hlt (noUb_of hub _) (by rw [hdm.2]; omega) hget
      have h4 : tmemOps ((X.tr (pairLane L 0 key s ℓ)).take
          ((X.tr (pairLane L 0 key s ℓ)).length - 1)) ≤
          tmemOps (X.tr (pairLane L 0 key s ℓ)) :=
        (List.take_sublist _ _).countP_le
      omega

/-- The time of a thread at its trace's end, in the rank table, when it just made its `m`-th
operation. -/
theorem time_after {g : Nat} {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length =
    some (some d)) {m : Nat}
    (ha : TmemAfter m d) (hm : m < 3) :
    (m = 0 → 42 ≤ threadTime L X g) ∧ (m = 1 → threadTime L X g = exitBase L X + 6) ∧
      (m = 2 → threadTime L X g = exitBase L X + 10) := by
  rcases m with _ | _ | _ | m
  · obtain ⟨p, rfl, hs⟩ := ha
    rw [threadTime_of hσ rfl]
    refine ⟨fun _ => ?_, by omega, by omega⟩
    rcases hs with hs | hs <;> simp [ThreadD.vtime, hs, Prologue.Site.vtime]
  · obtain ⟨c, rfl, hs⟩ := ha
    rw [threadTime_exit (o := 6) hσ (by simp [ThreadD.exitOff, Consumer.exitOff, hs])]
    exact ⟨by omega, fun _ => rfl, by omega⟩
  · obtain ⟨c, rfl, hs⟩ := ha
    rw [threadTime_exit (o := 10) hσ (by simp [ThreadD.exitOff, Consumer.exitOff, hs])]
    exact ⟨by omega, by omega, fun _ => rfl⟩
  · omega

/-- **A lane with no more operations than a thread's last is earlier than it.** -/
theorem time_lt_of_tmem (ht : ThreadFacts L X) (hub : ¬ HasUb X) {g h m : Nat} {d : ThreadD}
    (hh : h < L.threads) (hh0 : h % L.block / 32 = 0)
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (ha : TmemAfter m d)
      (hm : m < 3)
    (hle : tmemOps (X.tr h) ≤ m) : threadTime L X h < threadTime L X g := by
  obtain ⟨t0, t1, t2⟩ := time_after hσ ha hm
  have hbase : 1 ≤ exitBase L X := by simp only [exitBase]; omega
  cases hσh : Frame.stateAt (code L) X h (X.tr h).length with
  | none =>
    have : threadTime L X h = 0 := by simp [threadTime, hσh]
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
    · have := t0 rfl; omega
    · have := t1 rfl; omega
    · have := t2 rfl; omega
  | some σ =>
    cases σ with
    | none =>
      have : threadTime L X h = 0 := by simp [threadTime, hσh]
      rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
      · have := t0 rfl; omega
      · have := t1 rfl; omega
      · have := t2 rfl; omega
    | some dh =>
      have hst := ht.tmem_stage hh (noUb_of hub h) hh0 hσh
      generalize hn : tmemOps (X.tr h) = n at hst hle
      rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
      · obtain ⟨p, rfl, hv⟩ := hst
        have h1 : threadTime L X h = p.site.vtime := threadTime_of hσh rfl
        have h2 := threadTime_lt_exitBase (X := X) hh hσh rfl
        rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
        · have := t0 rfl; omega
        · have := t1 rfl; omega
        · have := t2 rfl; omega
      · have hm1 : m = 1 ∨ m = 2 := by omega
        have hg' : exitBase L X + 6 ≤ threadTime L X g := by
          rcases hm1 with rfl | rfl
          · have := t1 rfl; omega
          · have := t2 rfl; omega
        rcases hst with hx | ⟨o, hx, ho⟩
        · have := threadTime_lt_exitBase (X := X) hh hσh hx
          omega
        · rw [threadTime_exit hσh hx]
          omega
      · obtain ⟨o, hx, ho⟩ := hst
        have := t2 (by omega)
        rw [threadTime_exit hσh hx]
        omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
