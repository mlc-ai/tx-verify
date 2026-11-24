-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PollPhase
public import Lemmas.MBarrier.MBarrierRound

@[expose] public section

/-! # Transaction counts for a completed raw-ready phase -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol

open MBarrier

/-- With one arrival and a fixed size for each completion, the observed phase contains
the number of completions whose bytes balance its expected transaction bytes. -/
theorem transaction_completion_count {ι : Type} {log : List (Record ι)}
    {q arriveBytes completionBytes completions : Nat}
    (hpositive : 0 < completionBytes) (hbytes : arriveBytes = completionBytes * completions)
    (h : CheckedLog log) (hni : NoInval log)
    (harrive : ∀ r ∈ log, r.fault = none → ∀ c tx,
      r.action = .arrive c tx → c = 1 ∧ tx = arriveBytes)
    (hcomplete : ∀ r ∈ log, r.fault = none → ∀ n, r.action = .completeTx n → n = completionBytes)
    (hexpected : ∀ i s, i ≤ log.length → stateBefore log i = some s → s.expected = 1)
    (hinc : incrementsBefore log log.length = 0)
    {j : Nat} {s : State} (hj : j ≤ log.length) (hs : stateBefore log j = some s)
    (hq : q < s.phase) :
    ∃ C : Finset Nat, (∀ k, k ∈ C ↔ k < log.length ∧ ∃ r, log[k]? = some r ∧
          r.action = .completeTx completionBytes ∧ r.fault = none ∧ phaseAt log k = some q) ∧
      C.card = completions := by
  classical
  let U := (Finset.range log.length).filter (fun k => UnitArrivalIn log q k)
  let completesIn (k : Nat) := ∃ r, log[k]? = some r ∧
    r.action = .completeTx completionBytes ∧ r.fault = none ∧ phaseAt log k = some q
  let C := (Finset.range log.length).filter completesIn
  refine ⟨C, fun k => by simp [C, completesIn], ?_⟩
  have hU : U.card = 1 := h.card_unit_arrivals_phase hni
    (fun _ _ _ _ hr hf ha => (harrive _ (List.mem_of_getElem? hr) hf _ _ ha).1)
    hexpected hinc hj hs hq
  obtain ⟨endPos, hend, hcross⟩ := h.crossing hni hj hs hq
  have hendLen : endPos < log.length := by omega
  have hsum := (h.completion_sums hni hendLen hcross).1
  obtain ⟨_, after, _, _, hafter, hnext⟩ := hcross
  have beforeEnd {k : Nat} (hk : k < log.length) (hp : phaseAt log k = some q) :
      k ∈ Finset.range (endPos + 1) := by
    apply Finset.mem_range.mpr
    by_contra hge
    obtain ⟨t, ht, hle⟩ := h.phase_mono hni (show endPos + 1 ≤ k by omega) hk.le hafter
    simp only [phaseAt, ht, Option.map_some, Option.some.injEq] at hp
    omega
  have hUsub : U ⊆ Finset.range (endPos + 1) := by
    intro k hk
    obtain ⟨hkl, _, _, _, _, _, hp⟩ := Finset.mem_filter.mp hk
    exact beforeEnd (Finset.mem_range.mp hkl) hp
  have hCsub : C ⊆ Finset.range (endPos + 1) := by
    intro k hk
    obtain ⟨hkl, _, _, _, _, hp⟩ := Finset.mem_filter.mp hk
    exact beforeEnd (Finset.mem_range.mp hkl) hp
  have hpoint : ∀ k ∈ Finset.range (endPos + 1),
      (if phaseAt log k = some q then txDeltaAt log k else 0) =
        arriveBytes * (if k ∈ U then (1 : Int) else 0) -
          completionBytes * (if k ∈ C then (1 : Int) else 0) := by
    intro k hk
    have hk' : k < log.length := by have := Finset.mem_range.mp hk; omega
    obtain ⟨r, hr⟩ : ∃ r, log[k]? = some r := ⟨_, List.getElem?_eq_getElem hk'⟩
    have hrGet := (List.getElem?_eq_some_iff.mp hr).2
    by_cases hp : phaseAt log k = some q
    · by_cases hf : r.fault = none
      · cases ha : r.action with
        | arrive c tx =>
          obtain ⟨hc, ht⟩ := harrive r (List.mem_of_getElem? hr) hf c tx ha
          subst c
          subst tx
          simp [U, C, completesIn, UnitArrivalIn, hk', hp, hrGet, hf, ha,
            txDeltaAt, Record.txDelta, Action.txDelta]
        | completeTx n =>
          have hn := hcomplete r (List.mem_of_getElem? hr) hf n ha
          subst n
          simp [U, C, completesIn, UnitArrivalIn, hk', hp, hrGet, hf, ha,
            txDeltaAt, Record.txDelta, Action.txDelta]
        | _ =>
          simp [U, C, completesIn, UnitArrivalIn, hp, hr, hf, ha,
            txDeltaAt, Record.txDelta, Action.txDelta]
      · simp [U, C, completesIn, UnitArrivalIn, hp, hr, hf, txDeltaAt, Record.txDelta]
    · simp [U, C, completesIn, UnitArrivalIn, hp]
  have hcardU : (U.card : Int) =
      ∑ k ∈ Finset.range (endPos + 1), if k ∈ U then (1 : Int) else 0 := by
    rw [Finset.card_eq_sum_ite hUsub]
    push_cast
    rfl
  have hcardC : (C.card : Int) =
      ∑ k ∈ Finset.range (endPos + 1), if k ∈ C then (1 : Int) else 0 := by
    rw [Finset.card_eq_sum_ite hCsub]
    push_cast
    rfl
  have hbalance : (0 : Int) = arriveBytes * (U.card : Int) - completionBytes * (C.card : Int) := by
    rw [← hsum, phaseTx, Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hcardU, hcardC]
  have hc : (arriveBytes : Int) = (completionBytes : Int) * (completions : Int) := by
    exact_mod_cast hbytes
  rw [hU, hc] at hbalance
  have hprod : (completionBytes : Int) * (completions : Int) =
      (completionBytes : Int) * (C.card : Int) := by
    apply sub_eq_zero.mp
    simpa only [Nat.cast_one, mul_one] using hbalance.symm
  have hprodNat : completionBytes * completions = completionBytes * C.card := by
    exact_mod_cast hprod
  exact (Nat.eq_of_mul_eq_mul_left hpositive hprodNat).symm

/-- A completed raw-ready phase contains all 16 gather4 notifications. -/
theorem rawReady_completion_count {ι : Type} {log : List (Record ι)} {q : Nat}
    (h : CheckedLog log) (hni : NoInval log)
    (harrive : ∀ r ∈ log, r.fault = none → ∀ c tx, r.action = .arrive c tx → c = 1 ∧ tx = 36864)
    (hcomplete : ∀ r ∈ log, r.fault = none → ∀ n, r.action = .completeTx n → n = 2304)
    (hexpected : ∀ i s, i ≤ log.length → stateBefore log i = some s → s.expected = 1)
    (hinc : incrementsBefore log log.length = 0)
    {j : Nat} {s : State} (hj : j ≤ log.length) (hs : stateBefore log j = some s)
    (hq : q < s.phase) :
    ∃ C : Finset Nat, (∀ k, k ∈ C ↔ k < log.length ∧ ∃ r, log[k]? = some r ∧
          r.action = .completeTx 2304 ∧ r.fault = none ∧ phaseAt log k = some q) ∧
      C.card = 16 := by
  exact transaction_completion_count (by decide) (by decide) h hni harrive hcomplete hexpected
    hinc hj hs hq

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol
