-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Machine

@[expose] public section

/-! # The startup's termination measure

The startup's sites in program order (`measure`, `0` to `34`): every transition raises it
(`measure_step`), so a thread makes at most `35` startup events. The glued measure
(`Common/Measure.lean`) puts the warpgroups' states above it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
open PTX

/-- The rank of a site in program order. -/
def Site.rank : Site → Nat
  | .sh j => j.val
  | .elect j => 2 + j.val
  | .init n => 4 + n.val
  | .fence => 27
  | .alloc => 28
  | .allocSt => 29
  | .ld => 30
  | .trap => 31
  | .relinq => 32
  | .bar => 33
  | .enter _ => 34

/-- **The startup's measure.** -/
def measure (d : D) : Nat := d.site.rank

theorem measure_le (d : D) : measure d ≤ 34 := by
  obtain ⟨site, x1, x2⟩ := d
  cases site <;> simp only [measure, Site.rank] <;> omega

/-- **Every startup transition raises the measure.** -/
theorem measure_step {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : succ L g d e = some (some d')) : measure d < measure d' := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j =>
    simp only [succ] at h
    split at h
    · simp only [word32] at h
      split at h
      · rcases j with ⟨_ | _ | _, hj⟩
        · simp only [Option.some.injEq] at h
          subst h
          simp [measure, Site.rank]
        · simp only [Option.some.injEq] at h
          split_ifs at h <;> subst h <;> simp [measure, Site.rank]
        · omega
      · cases h
    · cases h
  | elect j =>
    simp only [succ] at h
    split at h
    · rcases j with ⟨_ | _ | _, hj⟩
      · simp only [Option.some.injEq] at h
        subst h
        simp [measure, Site.rank]
      · simp only [Option.some.injEq] at h
        split_ifs at h <;> subst h <;> simp [measure, Site.rank]
      · omega
    · cases h
  | init n =>
    simp only [succ, Option.some.injEq] at h
    subst h
    simp only [measure, initSucc]
    split
    · simp [Site.rank]
    · simp only [Site.rank]
      omega
  | ld =>
    simp only [succ] at h
    split at h <;> try cases h
    split at h <;> try cases h
    simp only [afterLd] at h
    split at h <;> try cases h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
      simp [measure, Site.rank]
  | alloc =>
    simp only [succ, Option.some.injEq] at h
    split_ifs at h <;> subst h <;> simp [measure, Site.rank]
  | bar =>
    simp only [succ, Option.some.injEq] at h
    subst h
    simp only [measure, enterOf]
    split_ifs <;> simp [Site.rank]
  | trap => simp [succ] at h
  | enter r => simp [succ] at h
  | fence => simp only [succ, Option.some.injEq] at h; subst h; simp [measure, Site.rank]
  | allocSt => simp only [succ, Option.some.injEq] at h; subst h; simp [measure, Site.rank]
  | relinq => simp only [succ, Option.some.injEq] at h; subst h; simp [measure, Site.rank]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Startup
