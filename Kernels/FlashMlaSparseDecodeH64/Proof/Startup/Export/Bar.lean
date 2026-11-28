-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Startup
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # The startup's named barrier

`barRow_startup`: a named-barrier event of the startup (below pc 103) is its `bar.sync 0` of the
whole CTA at pc 97 (the row `BarRow.Startup`); `startup_exit`: no startup event is `exit`. The
state behind the event is a startup state (`startup_at`) at the event's pc, and only the barrier
site's event is a barrier event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The startup's events by kind: a barrier event is the `bar.sync 0` at 97, and none is `exit`. -/
private theorem startup_kind (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {kd : Kind} (he : X.get (g, k) = some ⟨pc, kd⟩)
    (hub : ∀ f, kd ≠ .ub f) (hpc : pc < 103) :
    (∀ id cnt md, kd = .bar id cnt md → pc = 97 ∧ kd = .bar 0 none .sync) ∧ kd ≠ .exit := by
  obtain ⟨⟨site, x1, x2⟩, hR, -, hev, hx, -, hpc'⟩ := startup_at hp hX hFw he hub hpc
  cases site with
  | sh j => fin_cases j <;> obtain ⟨r, ok, hk⟩ := hev <;> subst hk <;> simp
  | elect j =>
    obtain ⟨inst, ld, -, hk⟩ := hev
    subst hk
    simp
  | init n => simp only [Startup.Ev] at hev; subst hev; simp
  | allocSt =>
    obtain ⟨col, -, hk⟩ := hev
    subst hk
    simp
  | ld =>
    rcases hev with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · subst hk
      simp
    · exact absurd hk (hub f)
  | trap => exact absurd hev (hub _)
  | bar => exact ⟨fun _ _ _ _ => ⟨hpc', hev⟩, by simp only [Startup.Ev] at hev; simp [hev]⟩
  | enter r => simp [Startup.exitOf] at hx
  | fence | alloc | relinq => simp only [Startup.Ev] at hev; subst hev; simp

/-- **Row `BarRow.Startup`**: a barrier event of the startup is the `bar.sync 0` at 97. -/
theorem barRow_startup (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : BarRow.Startup P L X := by
  intro g k e _ he hpc hb
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | bar id cnt md =>
    obtain ⟨h97, hk⟩ := (startup_kind hp hX hFw he (fun _ h => by cases h) hpc).1 id cnt md rfl
    exact ⟨h97, hk⟩
  | _ => simp [Execution.isBar] at hb

/-- **No startup event is `exit`**: a thread's exit is at pc 103 or later. -/
theorem startup_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) : 103 ≤ pc := by
  by_contra h
  exact (startup_kind hp hX hFw he (fun _ h => by cases h) (by omega)).2 rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
