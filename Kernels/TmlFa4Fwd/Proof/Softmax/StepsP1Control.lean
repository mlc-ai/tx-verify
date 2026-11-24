-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.Pk1
public import Kernels.TmlFa4Fwd.Proof.Softmax.Lift
public import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsFirstCtl
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # Control steps of the first round's probability publication

The first P publication follows the same control events with its probability table. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem lookupD_of_mem_nodup {G : List (Nat × Value)} (hnd : (G.map Prod.fst).Nodup)
    {q : Nat × Value} (hq : q ∈ G) : lookupD G q.1 = q.2 := by
  have := lookup_prefix (X := []) hnd hq
  simp only [List.append_nil] at this
  simp only [lookupD, this, Option.getD_some]

/-- The P part's value of a register of the exponent stretch's terms. -/
theorem valueOfD_p1 {d : D} (hd : valuesData p L g d = p1Data p L g d.v) {r : Nat}
    (hr : r ∈ (expoE p L g d.v).map Prod.fst) :
    valueOfD p L g d r = lookupD (expoE p L g d.v) r := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  rw [valueOfD_prefix (G := expoE p L g d.v) (X := halvesP1 _) hd (expoE_nodup ..) q hq,
    lookupD_of_mem_nodup (expoE_nodup ..) hq]

/-- The event of a site writes no data register its state names. -/
theorem hev_of {d : D} {pc : Nat} {ins0 : Instr} (h0 : kernel.code[pc]? = some ins0)
    (hpc : d.site.pc = pc)
    (hb : (dataAt d).all (fun r => !(eventWrites ins0.op).contains r) = true) :
    ∀ ins, kernel.code[d.site.pc]? = some ins →
      (dataAt d).all (fun r => !(eventWrites ins.op).contains r) = true := by
  intro ins hc
  rw [hpc, h0] at hc
  cases hc
  exact hb

/-- The landing obligation of a lifted control site. -/
macro "lift_land" : tactic => `(tactic| (
  intro e d' hn
  simp only [PTX.Kernels.TmlFa4Fwd.Proof.Softmax.succ] at hn
  repeat' (first | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals first | exact ⟨rfl, by kernel_rfl⟩ | cases hn | (exfalso; simp_all)))

set_option hygiene false in
/-- A control site of the first round's P part, lifted (`pc` the site's, `hi` the next event's). -/
macro "lift_p1 " pc:num hi:num : tactic => `(tactic| (
  refine stepAt_lift (stepAt_first_pctl hp hg _ rfl rfl (by simp)) $pc $hi (by kernel_rfl)
    (by kernel_rfl) (by simp [Site.pc, Rd.pc])
    (by simp [Site.pc, Rd.pc]) (hev_of (by code_lookup) rfl (by kernel_rfl)) ?_
  lift_land))

theorem stepAt_pst1_2 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pst .first 2, v, 0, []⟩ := by lift_p1 4844 4845
theorem stepAt_pwst1_0 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pwst .first 0, v, 0, []⟩ := by lift_p1 4845 4847
theorem stepAt_pst1_3 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pst .first 3, v, 0, []⟩ := by lift_p1 4856 4857
theorem stepAt_pwst1_1 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pwst .first 1, v, 0, []⟩ := by lift_p1 4857 4858
theorem stepAt_pws1 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pws .first, v, 0, []⟩ := by lift_p1 4858 4859
theorem stepAt_pel1 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.pel .first, v, 0, []⟩ := by lift_p1 4859 4874
theorem stepAt_parr2_1 (hp : Pre p L m) (hg : g < L.threads) (v : V) :
    (codeD p L g).StepAt ⟨.parr2 .first, v, 0, []⟩ := by lift_p1 4867 4874

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
