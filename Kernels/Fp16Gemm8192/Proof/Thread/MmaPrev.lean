-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.RankCounts

@[expose] public section

/-! # An MMA's place in its task, and the MMA before it

An MMA of K step `j` at slot `s` of the trip at block `q` is the task's MMA number
`4 (q + s) + j`: its thread's commits are `q + s` modulo the task's 128 blocks, and its accumulator
commits count the completed tasks (`mma_block_fact`). An accumulating MMA follows another MMA of its
thread with no MMA between, the MMA one earlier in the same task (`mma_prev_fact`): K step `j - 1`
right before it, or for `j = 0` the last MMA of the previous block, before the previous block's
commit and the failed polls of the slot's full barrier (`full_back`). An accumulator commit follows
the task's last MMA by two events, with the block's commit between (`acc_commit_last_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The state before a slot's full poll: the poll itself failed, the previous slot's commit, the
previous trip's last commit, or the accumulator poll. -/
theorem Mma.next_full_pred {m m' : Mma.D} {e : Event} (hn : Mma.next L g m e = some (some m'))
    {s : Fin 4} (h : m'.site = .full s) :
    (m.site = .full s ∧ m.q = m'.q) ∨
    (∃ s' : Fin 4, m.site = .commit s' ∧ ((s'.val + 1 = s.val ∧ m.q = m'.q) ∨
      (s'.val = 3 ∧ s.val = 0 ∧ m.q + 4 = m'.q))) ∨
    (m.site = .accWait ∧ s.val = 0 ∧ m.q = m'.q) := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  cases site
  all_goals simp only [Mma.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Option.map_eq_some_iff] at hn)
  all_goals (try obtain ⟨_, -, rfl⟩ := hn)
  all_goals (try (unfold Mma.endOfTrip at h; split_ifs at h))
  all_goals (try (unfold Mma.endOfTrip))
  all_goals (try split_ifs)
  all_goals (try simp_all)
  all_goals (try omega)
  all_goals (try (subst_vars; rfl))

/-- The state before a slot's first MMA is the slot's full poll. -/
theorem Mma.next_mma0_pred {m m' : Mma.D} {e : Event} (hn : Mma.next L g m e = some (some m'))
    {s : Fin 4} (h : m'.site = .mma s 0) : m.site = .full s ∧ m.q = m'.q := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  cases site
  all_goals simp only [Mma.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Option.map_eq_some_iff] at hn)
  all_goals (try obtain ⟨_, -, rfl⟩ := hn)
  all_goals (try (unfold Mma.endOfTrip at h; split_ifs at h))
  all_goals simp_all

/-- The state before an accumulator commit is the last trip's last commit. -/
theorem Mma.next_accCommit_pred {m m' : Mma.D} {e : Event} (hn : Mma.next L g m e = some (some m'))
    (h : m'.site = .accCommit) : m.site = .commit 3 := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  cases site
  all_goals simp only [Mma.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Option.map_eq_some_iff] at hn)
  all_goals (try obtain ⟨_, -, rfl⟩ := hn)
  all_goals (try (unfold Mma.endOfTrip at h; split_ifs at h))
  all_goals (try simp_all)
  all_goals (try (apply Fin.ext; omega))

/-- The MMA thread's commits to the input empty barriers step by its commit sites. -/
theorem mcount_step (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g <
    L.threads)
    {i : Nat} {m : Mma.D} (hi : i < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g i = some (some (.inr (.mma m)))) :
    mmaCount L g ((X.tr g).take (i + 1)) =
      mmaCount L g ((X.tr g).take i) + if ∃ s, m.site = .commit s then 1 else 0 := by
  have he : (X.tr g)[i]? = some (X.tr g)[i] := List.getElem?_eq_getElem hi
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨tt, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have ht : (X.tr g).take (i + 1) = (X.tr g).take i ++ [(X.tr g)[i]] := by
    rw [List.take_add_one, he]; rfl
  rw [ht, mmaCount_eq, mmaCount_eq]
  have hcs := commitsTo_iff_site hpre hg hat hc hfire
  by_cases hs : ∃ s, m.site = .commit s
  · obtain ⟨s0, hs0⟩ := hs
    simp only [show ∃ s, m.site = .commit s from ⟨s0, hs0⟩, ↓reduceIte]
    refine mcount_snoc (r := s0) fun s => ?_
    rw [commits_snoc, hcs s, hs0]
    by_cases h : s0 = s
    · subst h; simp
    · simp [h]
  · simp only [hs, ↓reduceIte, Nat.add_zero]
    refine mcount_snoc_none fun s => ?_
    rw [hcs s]
    exact decide_eq_false fun h => hs ⟨s, h⟩


/-- The MMA thread's site against its commits at a state of its run (`Mma.Counts.cond`). -/
theorem mma_cond (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {i : Nat} {m : Mma.D} (hσ : Frame.stateAt (code L) X g i = some (some (.inr (.mma m)))) :
    MmaCond m (mmaCount L g ((X.tr g).take i)) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hC : Mma.Counts L g m ((X.tr g).take i) := threadCounts_run hpre hg htr i _ hσ
  rw [mmaCount_eq]
  exact hC.cond

/-- **The failed polls of a slot's full barrier back to the commit before them.** From a state at
slot `s`'s full poll, not the task's first block, the thread's latest commit is to the slot before
(`s - 1`, or slot 3 of the previous trip), one block before; between them the thread stays at the
full poll. -/
theorem full_back (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) : ∀ i (m : Mma.D) (s : Fin 4), i ≤ (X.tr g).length →
    Frame.stateAt (code L) X g i = some (some (.inr (.mma m))) → m.site = .full s → 0 < m.q +
      s.val →
    ∃ ic mc, ∃ s' : Fin 4, ic < i ∧ Frame.stateAt (code L) X g ic = some (some (.inr (.mma mc))) ∧
      mc.site = .commit s' ∧ mc.q + s'.val + 1 = m.q + s.val ∧
      mmaCount L g ((X.tr g).take i) = mmaCount L g ((X.tr g).take ic) + 1 ∧
      ∀ i', ic < i' → i' < i → ∃ m', Frame.stateAt (code L) X g i' = some (some (.inr (.mma m'))) ∧
        m'.site = .full s := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro m s hle hσ hs hpos
  obtain ⟨i1, rfl⟩ : ∃ i1, i = i1 + 1 := ⟨i - 1, by have := mma_state_pos hσ; omega⟩
  have hi1 : i1 < (X.tr g).length := by omega
  have he : (X.tr g)[i1]? = some (X.tr g)[i1] := List.getElem?_eq_getElem hi1
  obtain ⟨m0, hσ0, hn⟩ := stateAt_mma_pred he hσ (by rw [hs]; simp)
  have hM := mcount_step hpre hX hg hi1 hσ0
  rcases Mma.next_full_pred hn hs with ⟨h0s, h0q⟩ | ⟨s', h0s, hcase⟩ | ⟨h0s, hs0, -⟩
  · obtain ⟨ic, mc, s', hic, hσc, hcs, hq, hMc, hall⟩ :=
      ih i1 (by omega) m0 s hi1.le hσ0 h0s (by rw [h0q]; exact hpos)
    refine ⟨ic, mc, s', by omega, hσc, hcs, by rw [hq, h0q], ?_, fun i' h1 h2 => ?_⟩
    · rw [hM, hMc]
      simp [h0s]
    · rcases Nat.lt_or_ge i' i1 with h3 | h3
      · exact hall i' h1 h3
      · obtain rfl : i' = i1 := by omega
        exact ⟨m0, hσ0, h0s⟩
  · refine ⟨i1, m0, s', by omega, hσ0, h0s, ?_, ?_, fun i' h1 h2 => absurd h2 (by omega)⟩
    · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · rw [h2]; omega
      · omega
    · rw [hM]
      simp only [show ∃ s, m0.site = .commit s from ⟨s', h0s⟩, ↓reduceIte]
  · exfalso
    have hc0 := mma_cond hpre hX hg hσ0
    have hc1 := mma_cond hpre hX hg hσ
    simp only [MmaCond, h0s] at hc0
    simp only [MmaCond, hs] at hc1
    rw [hM] at hc1
    simp only [h0s, reduceCtorEq, exists_false, ↓reduceIte, Nat.add_zero] at hc1
    omega

/-- **The MMA before an accumulating MMA**: the MMA one earlier in the same task, with no MMA of
the thread between. -/
theorem mma_prev_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {m : Mma.D} {s j : Fin 4} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.mma m)))) (hs : m.site = .mma s j)
    (hacc : Mma.accumulates m.q s.val j.val = true) :
    ∃ k' m', ∃ s' j' : Fin 4, k' < k ∧ Frame.stateAt (code L) X g k' =
      some (some (.inr (.mma m'))) ∧
      m'.site = .mma s' j' ∧
      (∃ pc dst sp acc mask, X.get (g, k') = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
      (∀ i pc dst sp acc mask, k' < i → i < k →
        X.get (g, i) ≠ some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
      4 * (mmaCount L g ((X.tr g).take k') % 128) + j'.val + 1 =
        4 * (mmaCount L g ((X.tr g).take k) % 128) + j.val ∧
      mmaCount L g ((X.tr g).take k') / 128 = mmaCount L g ((X.tr g).take k) / 128 := by
  -- an MMA event's state is at an MMA site
  have hmma : ∀ i pc dst sp acc mask (mi : Mma.D), X.get (g, i) =
    some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
      Frame.stateAt (code L) X g i = some (some (.inr (.mma mi))) → ∃ si ji : Fin 4, mi.site =
        .mma si ji := by
    intro i pc dst sp acc mask mi hget hσi
    obtain ⟨mi', si, ji, hd, hsi, -⟩ := mma_issue_fact hpre hX hg hget hσi rfl
    simp only [Sum.inr.injEq, Prologue.Role.mma.injEq] at hd
    subst hd
    exact ⟨si, ji, hsi⟩
  rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
  · -- the first MMA of a block: back over the full poll to the previous block's last MMA
    have hpos : 0 < m.q + s.val := by
      by_contra hc
      have h1 : m.q = 0 := by omega
      have h2 : s.val = 0 := by omega
      simp [Mma.accumulates, h1, h2, hj0] at hacc
    obtain ⟨k1, rfl⟩ : ∃ k1, k = k1 + 1 := ⟨k - 1, by have := mma_state_pos hσ; omega⟩
    have he1 : (X.tr g)[k1]? = some (X.tr g)[k1] := List.getElem?_eq_getElem (by omega)
    obtain ⟨m1, hσ1, hn1⟩ := stateAt_mma_pred he1 hσ (by rw [hs]; simp)
    obtain ⟨h1s, h1q⟩ := Mma.next_mma0_pred hn1 (s := s) (by rw [hs]; congr; exact Fin.ext hj0)
    obtain ⟨ic, mc, s', hic, hσc, hcs, hq, hMc, hall⟩ :=
      full_back hpre hX hg k1 m1 s (by omega) hσ1 h1s (by rw [h1q]; exact hpos)
    obtain ⟨k', rfl⟩ : ∃ k', ic = k' + 1 := ⟨ic - 1, by have := mma_state_pos hσc; omega⟩
    obtain ⟨m', hσ', hs'⟩ := mma_back (t := 3) (by omega) hσc (.inl ⟨rfl, hcs⟩)
    have hM1 := mcount_step hpre hX hg (by omega) hσ1
    have hM' := mcount_step hpre hX hg (by omega) hσ'
    simp only [h1s, reduceCtorEq, exists_false, ↓reduceIte, Nat.add_zero] at hM1
    simp only [hs', reduceCtorEq, exists_false, ↓reduceIte, Nat.add_zero] at hM'
    have hcK := mma_cond hpre hX hg hσ
    have hcC := mma_cond hpre hX hg hσc
    simp only [MmaCond, hs] at hcK
    simp only [MmaCond, hcs] at hcC
    have hk'l : k' < (X.tr g).length := by omega
    have hek : X.get (g, k') = some (X.tr g)[k'] := List.getElem?_eq_getElem hk'l
    obtain ⟨pck, dk, acck, maskk, hkk⟩ := mma_site_event hpre hX hg hek hσ' hs'
    refine ⟨k', m', s', 3, by omega, hσ', hs', ⟨pck, dk, _, acck, maskk, by rw [hek, hkk]⟩,
      fun i pc dst sp acc mask h1 h2 hget => ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge i (k' + 1 + 1) with h3 | h3
      · obtain rfl : i = k' + 1 := by omega
        obtain ⟨si, ji, hsi⟩ := hmma _ pc dst sp acc mask mc hget hσc
        rw [hcs] at hsi
        cases hsi
      · rcases Nat.lt_or_ge i k1 with h4 | h4
        · obtain ⟨m'', hσ'', hs''⟩ := hall i (by omega) h4
          obtain ⟨si, ji, hsi⟩ := hmma _ pc dst sp acc mask m'' hget hσ''
          rw [hs''] at hsi
          cases hsi
        · obtain rfl : i = k1 := by omega
          obtain ⟨si, ji, hsi⟩ := hmma _ pc dst sp acc mask m1 hget hσ1
          rw [h1s] at hsi
          cases hsi
    · rw [hj0]
      change 4 * (mmaCount L g ((X.tr g).take k') % 128) + 3 + 1 = _
      rw [hM1] at hcK
      have : mmaCount L g ((X.tr g).take (k' + 1)) = mmaCount L g ((X.tr g).take k') := hM'
      omega
    · rw [hM1]
      have : mmaCount L g ((X.tr g).take (k' + 1)) = mmaCount L g ((X.tr g).take k') := hM'
      rw [hM1] at hcK
      omega
  · -- K step `j - 1` right before
    obtain ⟨k1, rfl⟩ : ∃ k1, k = k1 + 1 := ⟨k - 1, by have := mma_state_pos hσ; omega⟩
    obtain ⟨m', hσ', hs'⟩ := mma_back (t := ⟨j.val - 1, by omega⟩) (by omega) hσ
      (.inr ⟨by simp only; omega, by rw [hs]; congr; apply Fin.ext; simp only; omega⟩)
    have hM' := mcount_step hpre hX hg (by omega) hσ'
    simp only [hs', reduceCtorEq, exists_false, ↓reduceIte, Nat.add_zero] at hM'
    have hk'l : k1 < (X.tr g).length := by omega
    have hek : X.get (g, k1) = some (X.tr g)[k1] := List.getElem?_eq_getElem hk'l
    obtain ⟨pck, dk, acck, maskk, hkk⟩ := mma_site_event hpre hX hg hek hσ' hs'
    refine ⟨k1, m', s, ⟨j.val - 1, by omega⟩, by omega, hσ', hs',
      ⟨pck, dk, _, acck, maskk, by rw [hek, hkk]⟩,
      fun i pc dst sp acc mask h1 h2 => absurd h2 (by omega), ?_, ?_⟩
    · rw [hM']; simp only; omega
    · rw [hM']

/-- **An MMA's place in its task.** An MMA of K step `j` at slot `s` is at block `q + s` of its
task (modulo 128), with as many accumulator commits before it as completed tasks, and its
round-robin share of commits to the slot; it accumulates unless it is the task's first. -/
theorem mma_block_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k : Nat} {m : Mma.D} {s j : Fin 4} {pc dst : Nat}
    {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.mma m)))) (hs : m.site = .mma s j) :
    mmaCount L g ((X.tr g).take k) % 128 = m.q + s.val ∧ m.q % 4 = 0 ∧
    ((X.tr g).take k).countP (commitsTo (inputEmpty L (g / L.block) s.val)) =
      (mmaCount L g ((X.tr g).take k) + 3 - s.val) / 4 ∧
    ((X.tr g).take k).countP
        (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) =
      mmaCount L g ((X.tr g).take k) / 128 ∧
    acc = Mma.accumulates m.q s.val j.val := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨hrank, hcond⟩ := mma_counts hpre hg htr hσ
  simp only [hs] at hcond
  have hC : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  have hR := hC.accRound
  have hw := role_warp hpre hX hg k (List.getElem?_eq_some_iff.mp he).1.le _ hσ
  simp only [roleWarp] at hw
  simp only [hs, reduceCtorEq, ↓reduceIte, Nat.add_zero, ← mmaCount_eq, hw.1, Mma.accBar,
    Prologue.warpOf] at hR
  obtain ⟨tt, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hev := Mma.mma_event hpre hg s j hs hat hc hfire
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at hev
  exact ⟨hcond.1, hcond.2, hrank s, hR, hev.2.2.2.1⟩

/-- **The task's last MMA before an accumulator commit.** Two events before an accumulator commit
the thread made its MMA of K step 3 at slot 3, the task's last: its commits are one fewer than 128
per accumulator commit then made. -/
theorem acc_commit_last_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {jc : Nat} {m : Mma.D} (hjc : jc ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g jc = some (some (.inr (.mma m)))) (hs : m.site = .accCommit) :
    2 ≤ jc ∧ (∃ m2, Frame.stateAt (code L) X g (jc - 2) = some (some (.inr (.mma m2))) ∧ m2.site =
      .mma 3 3) ∧
    (∃ pc dst sp acc mask, X.get (g, jc - 2) = some ⟨pc, .tc (.mma dst sp acc mask)⟩) ∧
    (∃ pc sp, X.get (g, jc - 1) = some ⟨pc, .tc (.commit sp)⟩) ∧
    mmaCount L g ((X.tr g).take (jc - 2)) + 1 =
      128 * (((X.tr g).take jc).countP
        (commitsTo (Bar.loc L (g / L.block) ⟨.acc, g % L.block / 32 % 2, true⟩)) + 1) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨j1, rfl⟩ : ∃ j1, jc = j1 + 1 := ⟨jc - 1, by have := mma_state_pos hσ; omega⟩
  have he1 : (X.tr g)[j1]? = some (X.tr g)[j1] := List.getElem?_eq_getElem (by omega)
  obtain ⟨m1, hσ1, hn1⟩ := stateAt_mma_pred he1 hσ (by rw [hs]; simp)
  have h1s := Mma.next_accCommit_pred hn1 hs
  obtain ⟨j2, rfl⟩ : ∃ j2, j1 = j2 + 1 := ⟨j1 - 1, by have := mma_state_pos hσ1; omega⟩
  obtain ⟨m2, hσ2, hs2⟩ := mma_back (t := 3) (by omega) hσ1 (.inl ⟨rfl, h1s⟩)
  have hM1 := mcount_step hpre hX hg (by omega) hσ1
  have hM2 := mcount_step hpre hX hg (by omega) hσ2
  simp only [show ∃ s, m1.site = .commit s from ⟨3, h1s⟩, ↓reduceIte] at hM1
  simp only [hs2, reduceCtorEq, exists_false, ↓reduceIte, Nat.add_zero] at hM2
  have hC : Mma.Counts L g m ((X.tr g).take (j2 + 1 + 1)) := threadCounts_run hpre hg htr _ _ hσ
  have hR := hC.accRound
  have hcond := hC.cond
  have hw := role_warp hpre hX hg _ hjc _ hσ
  simp only [roleWarp] at hw
  simp only [hs, ↓reduceIte, ← mmaCount_eq, hw.1, Mma.accBar, Prologue.warpOf] at hR
  simp only [MmaCond, hs, ← mmaCount_eq] at hcond
  have hj2 : j2 < (X.tr g).length := by omega
  have he2 : X.get (g, j2) = some (X.tr g)[j2] := List.getElem?_eq_getElem hj2
  obtain ⟨pc, dst, acc, mask, hk2⟩ := mma_site_event hpre hX hg he2 hσ2 hs2
  have hj1 : j2 + 1 < (X.tr g).length := by omega
  have he1' : X.get (g, j2 + 1) = some (X.tr g)[j2 + 1] := List.getElem?_eq_getElem hj1
  obtain ⟨tt, ins, o1, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he1' hσ1
  have hcev := Mma.commit_event hpre hg 3 h1s hat hc hfire
  refine ⟨by omega, ⟨m2, by simpa using hσ2, hs2⟩, ⟨pc, dst, _, acc, mask, by
    simp only [show j2 + 1 + 1 - 2 = j2 by omega]; rw [he2, hk2]⟩, ⟨_, _, by
    simp only [show j2 + 1 + 1 - 1 = j2 + 1 by omega]; rw [he1', hcev]⟩, ?_⟩
  simp only [show j2 + 1 + 1 - 2 = j2 by omega]
  omega

end

end PTX.Kernels.Fp16Gemm8192.Proof
