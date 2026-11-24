-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.BlockPhase

@[expose] public section

/-! # The ledger of a blocked response barrier

The response barrier of a CTA at the whole execution, in a phase `f` with its pending arrival bit,
has `f + 1` arrivals counting the pending one (`UnitTx.units`), at least `f` completions
(`UnitTx.phase_le_completed`), and at most `f + 1` (`completions_le_phase`); a completion count of
`f + 1` with a pending bit of zero would advance the phase: its transaction balance is zero. So
either the scheduler's arrival for the phase is still pending (`pending = 1`, its arrivals are
`f`), or the arrival is in and the phase's completion is not (`pending = 0`, its arrivals are
`f + 1` and its completions `f`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.ClcRing

open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The arrivals of a response barrier's history are its arrival units: all are fault-free unit
arrivals expecting the response's bytes. -/
theorem units_eq_arrivals (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (c : Nat) (i : Fin 2) :
    unitsBefore (X.objects ((slot L c).full i)) (X.objects ((slot L c).full i)).length =
      (X.objects ((slot L c).full i)).countP isArrival := by
  have hclean := fault_free hpre hX ht ((slot L c).full_mem i)
  have hu : UnitTx (X.objects ((slot L c).full i)) 16 := resp_unitTx hpre hX ht (2 * c + i.val)
  unfold unitsBefore
  rw [List.take_length,
    arrivalUnits_eq_length (fun r hr c' tx hf ha => (hu.arrive r hr hf c' tx ha).1),
    ← List.countP_eq_length_filter]
  refine List.countP_congr fun q hq => ?_
  rw [countedArrive_iff, isArrival_iff]
  constructor
  · rintro ⟨hf, c', tx, ha⟩
    obtain ⟨rfl, rfl⟩ := hu.arrive q hq hf c' tx ha
    exact ⟨ha, hf⟩
  · rintro ⟨ha, hf⟩
    exact ⟨hf, 1, 16, ha⟩

/-- **The completions of a response barrier are at most one more than its phase.** -/
theorem completions_le (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (c : Nat) {i : Fin 2} {before : MBarrier.State}
    (hstate : stateBefore (X.objects ((slot L c).full i)) (X.objects ((slot L c).full i)).length =
      some before) :
    (X.objects ((slot L c).full i)).countP isCompletion ≤ before.phase + 1 := by
  have h := completions_le_phase hpre hX ht hstate
  rw [List.take_length, ← countP_completion_eq hX ht (fun _ hq => hq)] at h
  exact h

/-- **The response barrier's ledger split.** At the whole execution, the final state `before` of a
response barrier of cluster `c` has its arrivals and completions fixed by its phase. -/
theorem ledger_split (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (c : Nat) {i : Fin 2} {before : MBarrier.State}
    (hstate : stateBefore (X.objects ((slot L c).full i)) (X.objects ((slot L c).full i)).length =
      some before) :
    (before.pending = 1 ∧ (X.objects ((slot L c).full i)).countP isArrival = before.phase) ∨
    (before.pending = 0 ∧ (X.objects ((slot L c).full i)).countP isArrival = before.phase + 1 ∧
      (X.objects ((slot L c).full i)).countP isCompletion = before.phase) := by
  have hch := (hX.tma.2.2.1 ((slot L c).full i)).1
  have hni := objects_noInval hX ht ((slot L c).full i)
  have hu : UnitTx (X.objects ((slot L c).full i)) 16 := resp_unitTx hpre hX ht (2 * c + i.val)
  obtain ⟨hpend, hunits⟩ := hu.units hch hni le_rfl hstate
  rw [incrementsBefore_zero hX ht _] at hpend hunits
  have htx := hu.tx hch hni le_rfl hstate
  have hfl := hu.phase_le_completed (by norm_num) hch hni le_rfl hstate
  have hC := completions_le hpre hX ht c hstate
  rw [units_eq_arrivals hpre hX ht c i] at hunits htx
  rw [List.take_length, ← countP_completion_eq hX ht (fun _ hq => hq)] at htx hfl
  rcases (show before.pending = 0 ∨ before.pending = 1 by omega) with h0 | h1
  · right
    refine ⟨h0, by omega, ?_⟩
    by_contra hne
    have htx0 : before.tx = 0 := by
      rw [htx]
      have : (X.objects ((slot L c).full i)).countP isCompletion = before.phase + 1 := by omega
      rw [this]
      omega
    have := stateBefore_pending_pos hch hstate htx0
    omega
  · left
    exact ⟨h1, by omega⟩

/-- **A notified target has its completion record.** A notify of cluster CTA `c` by the request `i`
is a completion of the barrier `{s.mbar with cta := c}`, which covers every such action of the log
(`CoversObject`), so the record is in the barrier's log, with the completion's action. -/
theorem notified_record (hX : Consistent L kernel Prod mem0 X) {i : EvId} {s : Clc.Spec}
    {tg : List Nat} (hi : X.ClcIssue i s tg) {c : Nat} (hc : c ∈ tg) (hn : c ∈ (X.clc i).notified) :
    ∃ r ∈ X.objects { s.mbar with cta := c }, r.id = .async i (.notify (.cta c)) ∧
      r.action = .completeTx 16 := by
  obtain ⟨pc, hget⟩ := hi
  have hact : objectAction X X.async { s.mbar with cta := c } (.async i (.notify (.cta c))) =
      some (.completeTx 16) := by
    simp [objectAction, hget, hc, hn]
  obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 { s.mbar with cta := c }).2.2 _ _ hact
  have hact' := ((hX.tma.2.2.1 { s.mbar with cta := c }).2.1 r hr).1
  rw [hid, hact] at hact'
  exact ⟨r, hr, hid, (Option.some.inj hact').symm⟩


/-- **The response barrier's three branches.** At the whole execution, cluster `c`'s response
barrier `i` in its final phase `n` has one of: its CTA's scheduler's arrivals at most `n` (the
arrival for the phase is pending); an issued cancellation request, one of whose targets is not
notified; or the leader scheduler's issued requests at most `n`. The request's multicast to every
CTA of its cluster (`hmulti`, a thread fact of the scheduler's instruction) and the CTA's presence
(`hcta`) are explicit premises. -/
theorem ledger_branches (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (c : Nat)
    (hmulti : ∀ (h ki pc : Nat) (sp : Clc.Spec) (tg : List Nat),
      X.get (h, ki) = some ⟨pc, .clcIssue sp tg⟩ → ∀ c', c' < L.grid → c' / 2 = h / L.block / 2 →
        c' ∈ tg)
    {i : Fin 2} (hcta : 2 * c + i.val < L.grid)
    {before : MBarrier.State}
    (hstate : stateBefore (X.objects ((slot L c).full i)) (X.objects ((slot L c).full i)).length =
      some before) :
    (X.objects ((slot L c).full i)).countP isArrival ≤ before.phase ∨
    (∃ i' s tg, X.ClcIssue i' s tg ∧ ¬ ∀ c' ∈ tg, c' ∈ (X.clc i').notified) ∨
    (X.tr (producer L X c)).countP (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩)) ≤
      before.phase := by
  have hsplit := ledger_split hpre hX ht c hstate
  rcases hsplit with ⟨-, hA⟩ | ⟨-, -, hC⟩
  · left
    omega
  · right
    by_cases hprod : before.phase + 1 ≤
        (X.tr (producer L X c)).countP (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩))
    · left
      obtain ⟨j, x, hjx, hcl, hcnt⟩ := MbarRing.Slot.exists_nth_countP
        (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩)) hprod
      obtain ⟨pcI, sp, tg, hxe⟩ : ∃ pcI sp tg, x = ⟨pcI, .clcIssue sp tg⟩ := by
        cases x with
        | mk pcx kind =>
          cases kind <;> simp [clcIssuesTo] at hcl
          case clcIssue sp' tg' =>
            exact ⟨pcx, sp', tg', rfl⟩
      subst hxe
      have hget : X.get (producer L X c, j) = some ⟨pcI, .clcIssue sp tg⟩ := hjx
      have hsp : sp.mbar = Bar.loc L (2 * c) ⟨.clc, 0, true⟩ := by
        simpa [clcIssuesTo] using hcl
      have hprod_cta : producer L X c / L.block / 2 = c := by
        rw [producer_cta hpre c]
        omega
      refine ⟨(producer L X c, j), sp, tg, ⟨pcI, hget⟩, ?_⟩
      intro hall
      have hin : 2 * c + i.val ∈ tg :=
        hmulti (producer L X c) j pcI sp tg hget (2 * c + i.val) hcta (by
          rw [hprod_cta]
          omega)
      obtain ⟨r, hr, hid, hact⟩ := notified_record hX ⟨pcI, hget⟩ hin (hall _ hin)
      have hobj : ({ sp.mbar with cta := 2 * c + i.val } : Loc) = (slot L c).full i := by
        rw [hsp]
        rfl
      rw [hobj] at hr
      obtain ⟨jd, hjd⟩ := List.mem_iff_getElem?.mp hr
      have hfault : r.fault = none := fault_free hpre hX ht ((slot L c).full_mem i) r hr
      obtain ⟨s, hids, -, hord⟩ := completion_ordinal hpre hX ht hjd hfault hact
      have hj : reqIdx L X c s = j := by
        rw [hid] at hids
        simp only [item, Ref.async.injEq, Prod.mk.injEq] at hids
        exact hids.1.2.symm
      rw [← hj] at hget
      have hs : s = before.phase := by
        rw [← issuesBefore_reqIdx hget]
        have : issuesBefore L X c (producer L X c) (reqIdx L X c s) = before.phase := by
          rw [hj]; exact hcnt
        exact this
      have hcount1 : completedTxCount ((X.objects ((slot L c).full i)).take (jd + 1)) =
          completedTxCount ((X.objects ((slot L c).full i)).take jd) + 1 := by
        rw [List.take_add_one, hjd]
        simp [completedTxCount, hact, hfault]
      have hmono : completedTxCount ((X.objects ((slot L c).full i)).take (jd + 1)) ≤
          completedTxCount (X.objects ((slot L c).full i)) := by
        simp only [completedTxCount]
        exact (List.take_sublist _ _).countP_le
      rw [← countP_completion_eq hX ht (fun _ hq => hq)] at hmono
      omega
    · right
      omega

end

end PTX.Kernels.Fp16Gemm8192.Proof.ClcRing
