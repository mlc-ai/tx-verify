-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.DataScript

@[expose] public section

/-! # The facts of a state against a warp's script

`ScriptFacts cn slot c pc clk`: a state with pc `pc` and clock `clk` at script position `c` is at a
collective exactly when the script has its pc at `c`, the time of a collective is its slot, and any
other state is earlier than every later slot. A worker's startup states have them for any script
that begins with the startup's shuffle. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow

def ScriptFacts (cn : Nat → Option Nat) (slot : Nat → Nat) (c pc clk : Nat) : Prop :=
  (isWarpAt pc = true ↔ cn c = some pc) ∧ (isWarpAt pc = true → clk = slot c) ∧
  (isWarpAt pc = false → ∀ n, (cn n).isSome = true → c ≤ n → clk < slot n)

/-- **The startup states** of a script that begins with the shuffle at slot 24 and whose later
slots are past the startup's clocks. -/
theorem start_script {cn : Nat → Option Nat} {slot : Nat → Nat} (h0 : cn 0 = some 17)
    (s0 : slot 0 = 24) (big : ∀ n, 1 ≤ n → 100 ≤ slot n)
    (h1 : ∀ r : Startup.Entry, cn 1 ≠ some r.pc) (s : Startup.Site) :
    ScriptFacts cn slot (startCount s) s.pc (startClock s) := by
  have wi : isWarpAt s.pc = true ↔ s = .shfl := by
    cases s <;> simp only [Startup.Site.pc, reduceCtorEq, iff_false, iff_true] <;>
      first | decide +kernel | (rename_i r; cases r <;> simp [Startup.Entry.pc] <;> decide +kernel)
  by_cases e : s = .shfl
  · subst e
    refine ⟨?_, fun _ => by simp [startCount, startClock, s0], fun h => ?_⟩
    · simp [startCount, h0, Startup.Site.pc]; decide +kernel
    · exact absurd (wi.mpr rfl) (by simp [h])
  · have hf : isWarpAt s.pc = false := by
      cases h : isWarpAt s.pc
      · rfl
      · exact absurd (wi.mp h) e
    refine ⟨?_, fun h => absurd (wi.mp h) e, fun _ n hn hle => ?_⟩
    · rw [hf]
      simp only [Bool.false_eq_true, false_iff]
      rcases s with _ | _ | _ | _ | _ | _ | _ | r
      · simp [startCount, h0, Startup.Site.pc]
      · simp [startCount, h0, Startup.Site.pc]
      · simp [startCount, h0, Startup.Site.pc]
      · simp [startCount, h0, Startup.Site.pc]
      · simp [startCount, h0, Startup.Site.pc]
      · simp [startCount, h0, Startup.Site.pc]
      · exact absurd rfl e
      · exact h1 r
    · have clk : startClock s < 24 ∨ ∃ r, s = .enter r := by
        cases s <;> first | exact absurd rfl e | exact .inr ⟨_, rfl⟩ | (left; simp [startClock])
      rcases clk with c | ⟨r, rfl⟩
      · have c0 : startCount s = 0 := by cases s <;> simp_all [startCount, startClock]
        by_cases n0 : n = 0
        · subst n0; omega
        · have := big n (by omega); omega
      · have := big n (by simpa [startCount] using hle)
        simp only [startClock]; omega

/-- No startup site is at the exit pc. -/
theorem start_pc_ne (s : Startup.Site) : s.pc ≠ 2855 := by
  rcases s with _ | _ | _ | _ | _ | _ | _ | r
  any_goals simp [Startup.Site.pc]
  cases r <;> simp [Startup.Entry.pc]

/-- A dispatch state at the exit pc is in a later round. -/
theorem dispatch_ret_round {dd : Dispatch.D} (al : Dispatch.Allowed dd)
    (h : dd.site.pc = 2855) : dd.round ≠ 0 := by
  obtain ⟨s, r⟩ := dd
  rintro rfl
  cases s <;> simp_all [Dispatch.Allowed, Dispatch.round0, Dispatch.round1, Dispatch.Site.pc]

end PTX.Kernels.InklingRelDecode.Proof
