-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Progress.Lag
public import Lemmas.Step.BulkDrain
public import Lemmas.Step.MmaDrain

@[expose] public section

/-! # `tc_gemm` progress: the asynchronous operations of a maximal execution

The MMA's operand bytes have sources (`operandSources`): one thread issues the kernel's only MMA,
whose 4096-byte operand A and 256-byte operand B are read from `sA` and `sB`; thread 0's
successful poll of `bar0` before it observed both copies, which wrote these buffers, and every
write of an operand byte is that copy's. So a maximal execution has completed the MMA
(`mma_done`) and delivered the commit (`commit_notified`). It has notified both copies
(`copies_notified`): once the MMA is issued the poll before it observed them; before, no Tensor
Core instruction reads, and the copies' sources are allocated inputs no write covers. So the
bulk, MMA and commit obligations are closed (`async_closed`), and the polls of a thread that
made the arrival on `bar0`, or of a thread after the commit, find their phase completed
(`bar0_done`, `bar1_done`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

omit hpre in
/-- **The MMA's operand bytes have sources**: the copies of `A` and `B`, which thread 0's poll of
`bar0` before the MMA observed. -/
theorem operandSources : OperandSources L X 4096 256 := by
  refine ⟨fun {i j} ⟨d, sp, acc, mask, hi⟩ ⟨d', sp', acc', mask', hj⟩ _ => ?_, ?_⟩
  · rw [(hW.mmaIssue hi).1, (hW.mmaIssue hj).1]
  intro i d sp acc mask hi
  obtain ⟨rfl, -, rfl, -, -⟩ := hW.mmaIssue hi
  have hm : hd 0 + 2 + (P 0).n0 < m 0 := by
    obtain ⟨pc, he⟩ := hi
    exact (hW.mma he).2.1
  have hget : X.get (0, hd 0 + 1 + (P 0).n0) = some (wait0E L.sharedBase true) := by
    rw [hW.get_of_lt (by decide) (by omega), fullAt_w0t]
  obtain ⟨hoA, hoB⟩ := wait_observes_copies hX hW hget
  obtain ⟨sA', rawA, ⟨pcA, hbA⟩, -, hwA, -⟩ := hX.copy_effects hoA (hW.copy_form _)
  obtain ⟨sB', rawB, ⟨pcB, hbB⟩, -, hwB, -⟩ := hX.copy_effects hoB (hW.copy_form _)
  obtain ⟨-, -, -, ⟨-, rfl⟩ | ⟨h7, -⟩⟩ := hW.bulk hbA
  swap; · cases h7
  obtain ⟨-, -, -, ⟨h6, -⟩ | ⟨-, rfl⟩⟩ := hW.bulk hbB
  · cases h6
  refine ⟨show TcMma.Valid mmaDesc by decide, show TcMma.Operand.a.bytes mmaDesc = 4096 by decide,
    show TcMma.Operand.b.bytes mmaDesc = 256 by decide, rfl,
    fun isB k loc hf => ?_, fun isB k => ?_⟩
  · rcases hf with ⟨d', s', acc', mask', hi', hbl⟩ | ⟨a', src, cta, ⟨pc, hc⟩, -⟩
    · obtain ⟨-, -, rfl, -, -⟩ := hW.mmaIssue hi'
      cases isB
      · rw [ite_eq_right (by decide), mmaSpec_a] at hbl
        split_ifs at hbl with hk
        · exact hk
      · rw [ite_eq_left rfl, mmaSpec_b] at hbl
        split_ifs at hbl with hk
        · exact hk
    · exact (hW.no_cp hc).elim
  · cases isB
    · have hk : k.val < 4096 := k.isLt
      have hq : offA (k.val / 32) (k.val % 32) < 4096 := by unfold offA; omega
      refine ⟨⟨(sA L.sharedBase).at (offA (k.val / 32) (k.val % 32)), _, _, rawA, hwA,
        Acc.covers_at hq⟩, .inl ⟨_, _, _, _, hi, ?_⟩, fun w a' bs hw hc => .inl ?_⟩
      · rw [ite_eq_right (by decide), mmaSpec_a, ite_eq_left hk]
      · exact (hW.copyA_writer hw hq hc).1
    · have hk : k.val < 256 := k.isLt
      have hq : offB (k.val % 32) (k.val / 32) < 256 := by unfold offB; omega
      refine ⟨⟨(sB L.sharedBase).at (offB (k.val % 32) (k.val / 32)), _, _, rawB, hwB,
        Acc.covers_at hq⟩, .inl ⟨_, _, _, _, hi, ?_⟩, fun w a' bs hw hc => .inl ?_⟩
      · rw [ite_eq_left rfl, mmaSpec_b, ite_eq_left hk]
      · exact (hW.copyB_writer hw hq hc).1

omit hX in
/-- The copies write their destinations whole from allocated inputs of the same size that no
write covers. -/
theorem bulkSources : BulkSources mem0 X := by
  intro i s mb ⟨pc, hb⟩ _
  obtain ⟨g, j⟩ := i
  obtain ⟨-, -, -, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := hW.bulk hb
  · exact ⟨rfl, rfl, rfl, fun k hk => ⟨inputA_alloc hpre (Acc.covers_at hk),
      fun _ _ _ hw => no_write_inputA hpre hW hw hk⟩⟩
  · exact ⟨rfl, rfl, rfl, fun k hk => ⟨inputB_alloc hpre (Acc.covers_at hk),
      fun _ _ _ hw => no_write_inputB hpre hW hw hk⟩⟩

end

section
variable (hpre : Pre L A B D a b mem0) (hmax : Maximal L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hmax hW

/-- **A maximal execution has completed the MMA.** -/
theorem mma_done {i : EvId} {d : Nat} {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d sp acc mask) : X.async.mmaDone i = true :=
  Maximal.mma_all_done wfFree hmax (syncGuarded hW hpre hmax.1)
    (operandSources hmax.1 hW) hi

/-- **A maximal execution has delivered the commit.** -/
theorem commit_notified {i : EvId} {s : TcCommit.Spec} {r : Fin 16} {mb : Loc}
    (hi : X.Commit i s) (htg : TcCommit.target s r = some mb) : r ∈ X.tcNotified i := by
  refine Maximal.commit_notified_of_started wfFree hmax hi htg fun x hx => ?_
  obtain ⟨-, -, hta, -⟩ := hx
  rcases hta with ⟨d, s', acc, mask, hmi⟩ | ⟨c, pc, hc⟩ | ⟨sh, pc, hs⟩
  · exact hmax.1.tma.2.1.2 x (mma_done hpre hmax hW hmi)
  · obtain ⟨g, j⟩ := x
    exact (hW.no_cp hc).elim
  · obtain ⟨g, j⟩ := x
    exact (hW.no_shift hs).elim

/-- **A maximal execution has notified both copies.** -/
theorem copies_notified {i : EvId} {s : AsyncCopy.Spec} (hb : X.Copy i s) :
    (X.async.copies i).notified = true := by
  have hX := hmax.1
  by_cases hmm : hd 0 + 2 + (P 0).n0 < m 0
  · have hget : X.get (0, hd 0 + 1 + (P 0).n0) = some (wait0E L.sharedBase true) := by
      rw [hW.get_of_lt (by decide) (by omega), fullAt_w0t]
    obtain ⟨hA, hB⟩ := wait_observes_copies hX hW hget
    obtain ⟨_, _, ⟨_, _, hnA, _⟩, _⟩ := hA.copy
    obtain ⟨_, _, ⟨_, _, hnB, _⟩, _⟩ := hB.copy
    obtain ⟨pc, he⟩ := hb
    obtain ⟨g, j⟩ := i
    obtain ⟨-, -, rfl, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := hW.bulk he
    · exact hnA
    · exact hnB
  · have hno : ∀ i d s accum mask, ¬ X.MmaIssue i d s accum mask := by
      intro i d s accum mask ⟨pc, he⟩
      obtain ⟨g, j⟩ := i
      obtain ⟨-, hj, rfl, rfl, -⟩ := hW.mma he
      exact hmm hj
    exact Maximal.bulk_notified wfFree hmax (bulkSources hpre hW)
      (copyReadOk_of_noTcRead hno (fun ⟨_, _⟩ _ _ _ ⟨_, hs⟩ => hW.no_tst hs)
        (fun ⟨_, _⟩ _ ⟨_, hc⟩ => hW.no_cp hc) (fun ⟨_, _⟩ _ ⟨_, hs⟩ => hW.no_shift hs)) hb
      (hW.copy_spec hb).1

/-- **The bulk, MMA and commit obligations of a maximal execution are closed.** -/
theorem async_closed {o : Descent.Obligation} (ho : Descent.Obl L X o) :
    o ≠ .bulk ∧ o ≠ .mma ∧ o ≠ .commit := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · refine ho fun _ _ hb => ?_
    rw [(hW.copy_spec hb).1]
    exact copies_notified hpre hmax hW hb
  · refine ho fun i hi => ?_
    rcases hi with ⟨d, s, accum, mask, hi⟩ | ⟨c, ⟨pc, hc⟩⟩ | ⟨s, ⟨pc, hs⟩⟩
    · exact mma_done hpre hmax hW hi
    · obtain ⟨_, _⟩ := i; exact (hW.no_cp hc).elim
    · obtain ⟨_, _⟩ := i; exact (hW.no_shift hs).elim
  · exact ho fun _ _ _ _ hi htg => commit_notified hpre hmax hW hi htg

/-- **After the copies' issue, the phase of `bar0` is completed** in a maximal execution: the
arrival and both copies are recorded. -/
theorem bar0_done (h7 : 7 < m 0) :
    ∃ s, stateBefore (X.objects (bar0 L.sharedBase)) (X.objects (bar0 L.sharedBase)).length =
      some s ∧ s.phase % 2 ≠ 0 := by
  have hX := hmax.1
  have ht := table0 hX hW
  have hget : X.get (0, 5) = some (arriveE L.sharedBase) := by
    rw [hW.get_of_lt (by decide) (by omega), fullAt_head _ (by decide)]
    rfl
  have ha : objectAction X X.async (bar0 L.sharedBase) (.thread (0, 5)) =
      some (.arrive 1 4352) := by
    simp [objectAction, hget, arriveE]
  obtain ⟨r, hr, hid, -⟩ := (ht.hist hX).arrive_recorded hX (List.mem_singleton_self _) ha
  obtain ⟨s, hs, -, hiff⟩ := (ht.hist hX).final_state hX (List.ne_nil_of_mem hr)
  have h1 : s.phase = 1 := by
    refine hiff.mpr ⟨fun a ha => ?_, fun c hc => (ht.hist hX).copy_recorded hX hc ?_⟩
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨r, hr, hid⟩
    simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact copies_notified hpre hmax hW (hW.bulkA (by omega))
    · exact copies_notified hpre hmax hW (hW.bulkB h7)
  exact ⟨s, hs, by rw [h1]; decide⟩

/-- **After the commit, the phase of `bar1` is completed** in a maximal execution: the commit's
arrive-on is recorded. -/
theorem bar1_done (hc : hd 0 + 3 + (P 0).n0 < m 0) :
    ∃ s, stateBefore (X.objects (bar1 L.sharedBase)) (X.objects (bar1 L.sharedBase)).length =
      some s ∧ s.phase % 2 ≠ 0 := by
  have hX := hmax.1
  have ht := table1 hpre hX hW
  have hget : X.get (0, hd 0 + 3 + (P 0).n0) = some (commitE L.sharedBase) := by
    rw [hW.get_of_lt (by decide) hc, fullAt_commit]
  have hn := commit_notified hpre hmax hW ⟨_, hget⟩ (commitSpec_target_zero (S := L.sharedBase))
  have ha : objectAction X X.async (bar1 L.sharedBase) (commitRef P) = some (.arrive 1 0) := by
    simp [commitRef, objectAction, hget, commitE, commitSpec_target_zero, hn]
  obtain ⟨r, hr, hid, -⟩ := (ht.hist hX).arrive_recorded hX (List.mem_singleton_self _) ha
  obtain ⟨s, hs, -, hiff⟩ := (ht.hist hX).final_state hX (List.ne_nil_of_mem hr)
  have h1 : s.phase = 1 := hiff.mpr ⟨fun a ha => by
    obtain rfl := List.mem_singleton.mp ha
    exact ⟨r, hr, hid⟩, fun c hc => by simp at hc⟩
  exact ⟨s, hs, by rw [h1]; decide⟩

end

end

end PTX.Kernels.TcGemm.Proof
