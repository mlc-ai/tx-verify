-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Observe
public import Lemmas.Protocol.GatedFaults
public import Lemmas.Protocol.KindRingGate
public import Lemmas.Protocol.TmaUnitsFault

@[expose] public section

/-! # The barriers of one lane's tensor copies do not fault

A full barrier of one lane's tensor copies and expecting arrivals is a `TmaUnits` object of the
lane. In a ring of kinds whose producer is that lane (`tma_fault_ring`), every item of use
`t ≥ 1` follows the lane's `t + 1` polls of the empty barrier, so by the ring's gate
(`KRing.gateF`) it follows the consumer's poll of the full barrier with `t - 1` earlier ones, and
that poll's record precedes the item's in the history: the object is gated
(`TmaUnits.Obj.fault_free`). The raw ring's `rawReady s` is such an object. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section

variable {L : Launch} {m : Mem0} {X : Execution}

/-- **A recorded arrival item of use `t` is the lane's arrival after `t` earlier ones.** -/
theorem tma_arrive_item {F : Loc} {y n bytes : Nat} (O : TmaUnits.Obj X F y n bytes) {k : Nat}
    {r} {x : Fin (n + 1) × Nat} (hk : (X.objects F)[k]? = some r)
    (hid : r.id = TmaUnits.it X F y n x.1 x.2) {c tx : Nat} (ha : r.action = .arrive c tx) :
    ∃ j pc rel sc, X.get (y, j) = some ⟨pc, .arrive F (n * bytes) 1 rel sc⟩ ∧
      arrivals F ((X.tr y).take j) = x.2 ∧ r.id = .thread (y, j) := by
  obtain ⟨-, rfl, j, pc, rel, sc, hj, he⟩ := O.arrive hk ha
  have hx0 : x.1.val = 0 := by
    by_contra hne
    rw [hj] at hid
    simp [TmaUnits.it, hne] at hid
  have hj2 : j = nthEv X (arrivesOn F) y x.2 := by
    rw [hj] at hid
    simp only [TmaUnits.it, hx0, ↓reduceIte, Ref.thread.injEq, TmaUnits.op, Prod.mk.injEq,
      true_and] at hid
    exact hid
  refine ⟨j, pc, rel, sc, he, ?_, hj⟩
  unfold arrivals
  rw [hj2]
  exact (nthEv_spec_of_get (hj2 ▸ he)).2

/-- **A recorded copy item of use `t` is the lane's `(n t + a)`-th tensor load to the barrier.** -/
theorem tma_copy_item {F : Loc} {y n bytes : Nat} (O : TmaUnits.Obj X F y n bytes) {k : Nat}
    {r} {x : Fin (n + 1) × Nat} (hk : (X.objects F)[k]? = some r)
    (hid : r.id = TmaUnits.it X F y n x.1 x.2) {b : Nat} (ha : r.action = .completeTx b) :
    ∃ j pc al sp, X.get (y, j) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = F ∧
      ((X.tr y).take j).countP (issuesTo F) = n * x.2 + (x.1.val - 1) ∧
      r.id = .async (y, j) (.notify .load) := by
  obtain ⟨-, j, pc, al, sp, hj, he, hm⟩ := O.copy hk ha
  have hx0 : x.1.val ≠ 0 := by
    intro h0
    rw [hj] at hid
    simp [TmaUnits.it, h0] at hid
  have hj2 : j = nthEv X (issuesTo F) y (n * x.2 + (x.1.val - 1)) := by
    rw [hj] at hid
    simp only [TmaUnits.it, hx0, ↓reduceIte, Ref.async.injEq, and_true, TmaUnits.op,
      Prod.mk.injEq, true_and] at hid
    exact hid
  refine ⟨j, pc, al, sp, he, hm, ?_, hj⟩
  rw [hj2]
  exact (nthEv_spec_of_get (hj2 ▸ he)).2

/-- **A full barrier of one lane's tensor copies in a ring of kinds does not fault.** -/
theorem tma_fault_ring (hX : Consistent L kernel Assumptions.all m X) {F E : Loc}
    {y n bytes nc : Nat} (O : TmaUnits.Obj X F y n bytes) (hn : 0 < n)
    (hfit : 2 * (n * bytes) ≤ MBarrier.limit)
    (R : KRing L kernel X 1 (nc + 1) (n + 1)) (hF : R.F = F) (hE : R.E = E) (hP : R.prod 0 = y)
    (hS : R.SF = TmaUnits.S X F y n bytes)
    (harr : ∀ {j pc tx cnt rel sc}, X.get (y, j) = some ⟨pc, .arrive F tx cnt rel sc⟩ →
      arrivals F ((X.tr y).take j) < okPolls E ((X.tr y).take j))
    (hcopy : ∀ {j pc al sp}, X.get (y, j) = some ⟨pc, .tensorIssue al sp⟩ → sp.mbar = F →
      ((X.tr y).take j).countP (issuesTo F) < n * okPolls E ((X.tr y).take j)) :
    ∀ r ∈ X.objects F, r.fault = none := by
  have key : ∀ {k i t : Nat} {r}, (X.objects F)[k]? = some r →
      ((∃ c tx, r.action = .arrive c tx) ∨ ∃ b, r.action = .completeTx b) →
      i < (X.tr y).length → 1 ≤ t → t + 1 ≤ okPolls E ((X.tr y).take i) →
      Relation.ReflTransGen (DepStep L kernel X) (.thread (y, i), false) (r.id, false) →
      ∃ kw w sw, kw < k ∧ (X.objects F)[kw]? = some w ∧ w.reply.waited = some true ∧
        MBarrier.stateBefore (X.objects F) kw = some sw ∧ t ≤ sw.phase := by
    intro k i t r hk hact hi ht hpoll hpath
    have hg' := R.gateF hX (a := 0) (i := i) (u := t - 1) (by rw [hP]; exact hi)
      (by rw [hE, hP, Nat.sub_add_cancel ht]; exact hpoll) 0
    rw [hP, hF] at hg'
    obtain ⟨pc, par, acq, sc, hw, hcnt⟩ := poll_of_path hg'
    obtain ⟨kw, w, sw, hkw, hwid, ⟨p', hwa⟩, hww, hsw, hge⟩ := poll_phase_ge_for_thread hX
      (Nat.zero_le 1) O.noInval (PairTmaRing.poll_clean hX O.init O.noInval)
      (fun he => by have := R.parF 0 (hF ▸ he); rw [hF] at this; exact this) hw
    refine ⟨kw, w, sw, ?_, hkw, hww, hsw, by omega⟩
    exact Unit.Gate.poll_before hX (hg'.trans_left hpath) hk rfl hkw hwid (by
      rcases hact with ⟨_, _, h⟩ | ⟨_, h⟩ <;> rw [h, hwa] <;> simp)
  refine O.fault_free hX hn hfit ?_ ?_
  · intro k r x hk hid hact hpos
    rcases id hact with ⟨c, tx, ha⟩ | ⟨b, ha⟩
    · obtain ⟨j, pc, rel, sc, he, hc, hj⟩ := tma_arrive_item O hk hid ha
      have hb := harr he
      rw [hc] at hb
      exact key hk hact (len_of_get he) hpos hb (by rw [hj])
    · obtain ⟨j, pc, al, sp, he, hm, hc, hj⟩ := tma_copy_item O hk hid ha
      have hb := hcopy he hm
      rw [hc] at hb
      have hb' : x.2 + 1 ≤ okPolls E ((X.tr y).take j) := by
        have : x.2 < okPolls E ((X.tr y).take j) :=
          Nat.lt_of_mul_lt_mul_left (a := n) (by omega)
        omega
      refine key hk hact (len_of_get he) hpos hb' ?_
      have hpr := object_record_present hX.tma (List.mem_of_getElem? hk)
      rw [hj] at hpr ⊢
      obtain ⟨ob, hob, hn⟩ := id hpr
      obtain ⟨x', y', k', hwp⟩ := tensor_write_present hX.effectValidity hob hn
      exact (((Relation.TransGen.single (DepStep.issue (L := L) (K := kernel)
        (p := .write (.load x' y' k')) ⟨_, he⟩ hwp (fun _ h => by cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h))).tail (DepStep.node hwp)).tail (DepStep.stage
          (c := (.async (y, j) (.notify .load), false))
          (.inr ⟨rfl, rfl, rfl, rfl, hwp, hpr⟩))).to_reflTransGen
  · intro t hnot x hx
    by_contra hlt
    have hr := R.reachF hX (x := x) (by rw [hS]; exact hx) 0 (j := t) (by omega)
    have hu : t < okPolls R.F (X.tr (R.cons 0)) := Poll.nth_present.mp (present_of_path hr)
    have := (R.full_observes hX hu 0).1
    rw [hS] at this
    exact hnot this

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
