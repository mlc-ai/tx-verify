-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Protocol.Events
public import Lemmas.Step.CtaBarNamed
public import Kernels.BlockSum.Proof.NoBarArrive

@[expose] public section

/-! # The CTA barrier

Every arrival on barrier `0` is a thread's third event, for the whole CTA (`count = none`, the
CTA's 8 warps). So the records of a CTA's barrier history follow the named-barrier protocol of the
8 warps of the CTA (`protocol`), and every arrival has ordinal `0`. A thread that passed its
barrier released generation `0` (`released`). Then every thread of the CTA has arrived, and what
it did before its arrival happens before what any thread of the CTA does after passing
(`shared_sync`). -/

namespace PTX.Kernels.BlockSum.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

/-- The barrier's thread count, omitted, is the CTA's 8 warps. -/
theorem target_none (hpre : Pre L A B x mem0) : target L.block none = .ok 8 := by
  rw [hpre.block]; rfl

theorem warps_bound (hpre : Pre L A B x mem0) : ∀ w ∈ Finset.range 8, w < L.block / 32 := by
  intro w hw
  rw [hpre.block]
  simpa using hw

/-- No arrival on barrier `0` precedes a thread's barrier arrival. -/
theorem barId_take_two (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) (g : Nat) :
    ((X.tr g).take 2).countP (Execution.isBarId 0) = 0 := by
  rw [List.countP_eq_zero]
  intro ev hm hbar
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  have hj2 : j < 2 := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take, ite_eq_left hj2] at hj
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> simp [Execution.isBarId] at hbar
  rename_i id cnt mode
  cases mode
  case arrive => exact (hX.noBarArrive Fact.out (g, j) _ _ _ hj).elim
  have := (bar_cases hpre hX ht (show X.IsBarrier (g, j) id cnt pc from hj)).1
  omega

/-- **The barrier's protocol**: every arrival on barrier `0` in a CTA's history is by one of its
8 warps, for the whole CTA. -/
theorem protocol (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {c : Nat} (hc : c < L.grid) :
    NamedBar.Protocol none (Finset.range 8) 0 (X.barriers c) := by
  refine NamedBar.protocol_of_src hX (fun e pc cnt hbar hec => ?_) hc (by rw [hpre.block]; decide)
  obtain ⟨-, -, hcnt, -⟩ := bar_cases hpre hX ht hbar
  refine ⟨?_, hcnt⟩
  rw [Finset.mem_range, hpre.block]
  omega

theorem protocol_prefix (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {c : Nat} (hc : c < L.grid) (i : Nat) :
    NamedBar.Protocol none (Finset.range 8) 0 ((X.barriers c).take i) :=
  fun r hr => protocol hpre hX ht hc r (List.mem_of_mem_take hr)

theorem cta_lt (hpre : Pre L A B x mem0) {g : Nat} (hg : g < L.threads) : g / L.block < L.grid := by
  have hb : 0 < L.block := by rw [hpre.block]; decide
  exact (Nat.div_lt_iff_lt_mul hb).mpr hg

theorem prefixFor (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {e : EvId} (he : e.1 < L.threads) :
    NamedBar.PrefixFor L X none (Finset.range 8) 0 e := by
  intro index warp cnt lanes hr _
  have hproto := protocol hpre hX ht (cta_lt hpre he)
  exact ⟨protocol_prefix hpre hX ht (cta_lt hpre he) index, hproto _ (List.mem_of_getElem? hr) rfl⟩

/-- **A passed barrier released generation `0` of its CTA.** -/
theorem released (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {h pc : Nat} (hf : X.IsBarrier (h, 2) 0 none pc)
    (hpassed : 3 < (X.tr h).length) : Released L.block (X.barriers (h / L.block)) 0 0 := by
  have hge := Frame.lt_of_get hX hf
  have hk := NamedBar.passed_key hX (n := 8) (by decide) (target_none hpre) hf
    (by simp only; omega) (prefixFor hpre hX ht hge) (Finset.card_range 8) (warps_bound hpre)
  obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_returned hX hf (by simp only; omega)
  have := CtaBarK.key_unique hX.ctaBar hkey hk
  simp only [barId_take_two hpre hX ht h] at this
  subst this
  exact hdone

/-- **A reached arrival of a CTA whose generation `0` is released is recorded in it.** -/
theorem key_of_released (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g pc : Nat} (he : X.IsBarrier (g, 2) 0 none pc)
    (hd : Released L.block (X.barriers (g / L.block)) 0 0) :
    CtaBarK L X (g, 2) 0 ∧ CtaBarDone L X (g / L.block) 0 := by
  have hge := Frame.lt_of_get hX he
  have hw : (g % L.block) / 32 ∈ Finset.range 8 := by
    rw [hpre.block, Finset.mem_range]; omega
  have hk := NamedBar.reached_key_of_release hX (n := 8) (by decide) (target_none hpre)
    (p := Finset.range 8) (by decide) he hge hw (barId_take_two hpre hX ht g) hd
    (fun i _ => protocol_prefix hpre hX ht (cta_lt hpre hge) (i + 1)) (Finset.card_range 8)
    (warps_bound hpre)
  exact ⟨hk, hd⟩

/-- The CTA barrier orders each thread's shared store before the reads of its CTA's threads after
their barrier: every thread of the CTA has arrived at the barrier (its third event), and its
second event happens before. -/
def SharedSync (L : Launch) (X : Execution) : Prop :=
  ∀ r w k pc a bs, w < L.threads → w / 256 = r / 256 → X.get (r, k) = some ⟨pc, .rd a bs⟩ →
    2 < k → 2 < (X.tr w).length ∧ baseCausality L X (w, 1) (r, k)

/-- **The barrier synchronizes the CTA.** -/
theorem shared_sync (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) : SharedSync L X := by
  intro r w k pc a bs hw hwc he hk
  have hr := Frame.lt_of_get hX he
  have hlen := len_of_get he
  simp only at hlen
  have hB := hpre.block
  have hbr := bar_of_later hpre hX ht he (by intro _ _ h; cases h) (by omega)
  have hd := released hpre hX ht hbr (by omega)
  have hcw : w / L.block = r / L.block := by rw [hB]; exact hwc
  have hwr : (w / L.block) * L.block + w % L.block = w := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod w L.block
  have hwp : (w % L.block) / 32 ∈ Finset.range 8 := by rw [hB, Finset.mem_range]; omega
  -- the arrival of `w`
  obtain ⟨pcw, hbw⟩ : ∃ pcw, X.IsBarrier (w, 2) 0 none pcw := by
    by_cases hex : ∃ j pcx, X.get (w, j) = some ⟨pcx, .exit⟩
    · obtain ⟨j, pcx, hx⟩ := hex
      exact ⟨_, bar_of_exit hpre hX ht hx⟩
    · push Not at hex
      rw [← hcw] at hd
      obtain ⟨e, pce, he1, hbe, -, -⟩ := NamedBar.released_member_key hX (n := 8) (by decide)
        (target_none hpre) (p := Finset.range 8) (cta_lt hpre hw) (by decide) hd
        (fun i _ => protocol_prefix hpre hX ht (cta_lt hpre hw) (i + 1)) (Finset.card_range 8)
        (warps_bound hpre) (Nat.mod_lt _ (by omega)) hwp (by rw [hwr]; exact hex)
      obtain ⟨e1, e2⟩ := e
      simp only at he1
      rw [hwr] at he1
      subst he1
      obtain ⟨rfl, -, -, -⟩ := bar_cases hpre hX ht hbe
      exact ⟨pce, hbe⟩
  have hlw := len_of_get hbw
  simp only at hlw
  refine ⟨hlw, ?_⟩
  exact NamedBar.reached_same_ordinal_baseCausality hX (n := 8) (by decide) (target_none hpre)
    (p := Finset.range 8) (by decide) ⟨hw, hr, hcw⟩ hbw hbr (by omega) hwp
    (prefixFor hpre hX ht hr)
    (by rw [barId_take_two hpre hX ht w, barId_take_two hpre hX ht r])
    (fun i _ => protocol_prefix hpre hX ht (cta_lt hpre hr) (i + 1)) (Finset.card_range 8)
    (warps_bound hpre) (by omega) hk hlen

end
end PTX.Kernels.BlockSum.Proof
