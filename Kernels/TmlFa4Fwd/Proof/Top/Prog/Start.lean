-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Common.SharedSites
import Kernels.TmlFa4Fwd.Proof.Common.DataSound

@[expose] public section

/-! # A released lane at a startup state

The progress class this file owns. `Prog.Start.Rest` is what is still open of it; it is empty.
Every startup site whose instruction is outside the released template (`RestAt`) is a warp
collective (`CollAt`: the three shuffles and the sixteen elections; the initializations, the fence
and the barrier are not in `Rest`), checked on the code (`start_code`). A startup state is never at
its role entry (the glued machine's invariant: the startup's exit is `none`). So a released lane at
a startup state with its instruction in `Rest` is at a warp collective (`Prog.start`), which the
class `Top/Prog/WarpColl.lean` steps. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- A startup state at an instruction in `Rest`. -/
def Prog.Start.At (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  (∃ s n, σ = (.inl s, n)) ∧ RestAt p L g σ

/-- The pcs of the startup's sites before its role entry. -/
def startPcs : List Nat :=
  [25, 34, 35] ++ (List.finRange 16).map Startup.electPc ++
    (List.finRange 34).map Startup.initPc ++ [172, 173]

/-- **Every startup instruction in `Rest` is a warp collective.** -/
theorem start_code : startPcs.all (fun pc => match kernel.code[pc]? with
    | some ins => !(Descent.opKind ins.op).Rest || decide (Descent.opKind ins.op = .warp)
    | none => true) = true := by
  decide +kernel

theorem start_pc_mem (s : Startup.Site) (hs : ∀ r, s ≠ .enter r) : s.pc ∈ startPcs := by
  cases s with
  | sh j => fin_cases j <;> decide
  | elect j => simp [startPcs, Startup.Site.pc, List.mem_map]
  | init n => simp [startPcs, Startup.Site.pc, List.mem_map]
  | fence => decide
  | bar => decide
  | enter r => exact absurd rfl (hs r)

/-- **A released lane at a startup state with its instruction in `Rest` is at a warp
collective.** -/
theorem Prog.start (hp : Pre p L m) (hs : SafeGoal kernel Assumptions.all L m) :
    ∀ X, Maximal L kernel Assumptions.all m X → ∀ g σ, Frame.Pending L X g →
      Frame.stateAt (thread p L) X g (X.tr g).length = some (some σ) →
      Prog.Start.At p L g σ → CollAt p L g σ := by
  intro X hmax g σ hpd hσ ⟨⟨s, n, hsn⟩, hrest⟩
  subst hsn
  have hX := hmax.1
  obtain ⟨t, hr⟩ := Frame.run_some hX (Sched.safe_noUb (hs.2 X hX)) hpd
  obtain ⟨t1, ins, -, -, hinv, -, -⟩ :=
    strict_end_at hp hpd.1 hr hσ rfl
  have hx : exit L g s = none := hinv.2
  have hne : ∀ r, s.site ≠ .enter r := fun r he => by simp [exit, he] at hx
  refine ⟨hrest, fun ins hc => ?_⟩
  have hc' : kernel.code[s.site.pc]? = some ins := hc
  have hmem := List.all_eq_true.mp start_code _ (start_pc_mem s.site hne)
  rw [hc'] at hmem
  have hR := hrest ins hc
  simp only [hR, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hmem
  exact hmem

end PTX.Kernels.TmlFa4Fwd.Proof.Top
