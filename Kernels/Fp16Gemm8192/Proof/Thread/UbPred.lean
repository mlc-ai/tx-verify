-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClcQuery

@[expose] public section

/-! # The steps into a first-CTA query and into the deallocation

A role reaches its first-CTA query only from its status query, by a query whose response cancels a
CTA, keeping the response it holds (`next_first`). A consumer reaches its deallocation only from
its load of the base word, holding the value the bytes it read rebuild to (`Consumer.next_dealloc`).
-/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {L : Launch} {g : Nat}

set_option maxHeartbeats 4000000 in
theorem Loader.next_first {d d' : Loader.D} {e : Event} (hn : Loader.next L g d e = some (some d'))
    (h3 : d'.site = .clcFirst) : d.site = .clcStatus ∧ d'.resp = d.resp ∧
      ∃ q r, e.kind = .clcQuery q r ∧ r.firstCta.isSome = true := by
  obtain ⟨site, m, n, q, cp, r, x⟩ := d
  cases site
  all_goals simp only [Loader.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Option.map_eq_some_iff] at hn)
  all_goals (try obtain ⟨_, -, rfl⟩ := hn)
  all_goals (try (unfold Loader.endOfTrip at h3; split_ifs at h3))
  all_goals simp_all

set_option maxHeartbeats 4000000 in
theorem Mma.next_first {d d' : Mma.D} {e : Event} (hn : Mma.next L g d e = some (some d'))
    (h3 : d'.site = .clcFirst) : d.site = .clcStatus ∧ d'.resp = d.resp ∧
      ∃ q r, e.kind = .clcQuery q r ∧ r.firstCta.isSome = true := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := d
  cases site
  all_goals simp only [Mma.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Option.map_eq_some_iff] at hn)
  all_goals (try obtain ⟨_, -, rfl⟩ := hn)
  all_goals (try (unfold Mma.endOfTrip at h3; split_ifs at h3))
  all_goals simp_all

set_option maxHeartbeats 4000000 in
theorem Scheduler.next_first {d d' : Scheduler.D} {e : Event}
    (hn : Scheduler.next L g d e = some (some d')) (h3 : d'.site = .clcFirst) :
    d.site = .clcStatus ∧ d'.resp = d.resp ∧
      ∃ q r, e.kind = .clcQuery q r ∧ r.firstCta.isSome = true := by
  obtain ⟨site, ap, cp, r, x⟩ := d
  cases site
  all_goals simp only [Scheduler.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Option.map_eq_some_iff] at hn)
  all_goals (try obtain ⟨_, -, rfl⟩ := hn)
  all_goals (try (unfold Scheduler.loopHead at h3; split_ifs at h3))
  all_goals simp_all

set_option maxHeartbeats 8000000 in
theorem Consumer.next_first {d d' : Consumer.D} {e : Event}
    (hn : Consumer.next L g d e = some (some d')) (h3 : d'.site = .clcFirst) :
    d.site = .clcStatus ∧ d'.resp = d.resp ∧
      ∃ q r, e.kind = .clcQuery q r ∧ r.firstCta.isSome = true := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  all_goals simp only [Consumer.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Option.map_eq_some_iff] at hn)
  all_goals (try obtain ⟨_, -, rfl⟩ := hn)
  all_goals simp_all

set_option maxHeartbeats 8000000 in
theorem Consumer.next_dealloc {d d' : Consumer.D} {e : Event}
    (hn : Consumer.next L g d e = some (some d')) (h3 : d'.site = .dealloc) :
    d.site = .ldBase ∧ ∃ a bs, e.kind = .rd a bs ∧ rebuild 3 bs = .ok d'.base := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  all_goals simp only [Consumer.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Option.map_eq_some_iff] at hn)
  all_goals (try obtain ⟨_, -, rfl⟩ := hn)
  all_goals simp_all

end

end PTX.Kernels.Fp16Gemm8192.Proof
