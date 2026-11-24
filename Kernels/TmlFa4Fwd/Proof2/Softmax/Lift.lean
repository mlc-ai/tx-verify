-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Base
public import Kernels.TmlFa4Fwd.Proof2.Softmax.GenRules
public import Lemmas.Flow.RegionFrame

@[expose] public section

/-! # Control steps of the data machine from the control machine

A control site's step of the data machine `codeD` from its step of the control machine `code`
(`stepAt_lift`): the site's event and the local code up to the next event write none of the data
registers the state names (`regionB`, `eventWrites`, Boolean checks on the code), and each
successor has the state's data table and names no data register the state does not
(`valuesData`, a Boolean check on the live registers). The data facts then carry over unchanged,
so a control site's step is checked on the control facts only, whatever data the state holds. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section

variable {p : Params} {L : Launch} {g : Nat}

/-- The data registers a state names. -/
noncomputable def dataAt (d : D) : List Nat := (liveD (livePc d)).filter fun r => !ctl r

theorem mem_liveD_live {pc r : Nat} (h : r ∈ liveD pc) :
    r ∈ PTX.Kernels.TmlFa4Fwd.Flow.live pc := by
  unfold liveD liveF at h
  split at h
  · exact (List.mem_filter.mp h).1
  · exact h

theorem mem_factsD {d : D} {q : Nat × Value} (h : q ∈ (code p L g).facts d) :
    q ∈ factsD p L g d := by
  obtain ⟨r, v⟩ := q
  simp only [facts, factsFrom, List.mem_map] at h
  obtain ⟨r', hr', e⟩ := h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  simp only [ctlLive, List.mem_filter] at hr'
  rw [← valueOfD_ctl d hr'.2]
  exact mem_factsFrom (by
    unfold liveD liveF; split <;> simp [List.mem_filter, hr'.1, hr'.2])

/-- The facts of a successor with the state's data table, from its control facts and the data
facts before the step. -/
theorem land_data {d d' : D} (hv : valuesData p L g d' = valuesData p L g d)
    (hl : (liveD (livePc d')).all (fun r => ctl r ||
      ((dataAt d).contains r && ((valuesData p L g d').map Prod.fst).contains r)) = true)
    {S T : Nat → Option Value} (hS : Holds S (factsD p L g d))
    (hT : Holds T ((code p L g).facts d')) (hST : ∀ r ∈ dataAt d, T r = S r) :
    Holds T (factsD p L g d') := by
  refine holds_of_pointwise fun r hr => ?_
  have h := List.all_eq_true.mp hl r hr
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
  rcases h with hc | ⟨hd, hk⟩
  · rw [valueOfD_ctl d' hc]
    exact holds_mem hT (mem_factsFrom (by
      simp only [ctlLive, List.mem_filter]; exact ⟨mem_liveD_live hr, hc⟩))
  · rw [hST r hd]
    have hrd : r ∈ liveD (livePc d) := (List.mem_filter.mp hd).1
    have hs := holds_mem hS (mem_factsFrom hrd)
    rw [hs]
    obtain ⟨x, hx⟩ := lookup_some hk
    have hx' := hx
    rw [hv] at hx'
    simp only [valueOfD, hx, hx', Option.getD_some]

/-- **A control step of the data machine** from the control machine's: no data register the
state names is written by the event or by the local code in `[lo, hi]`, and each successor keeps
the state's data table. -/
theorem stepAt_lift {d : D} (h : (code p L g).StepAt d) (lo hi : Nat)
    (hB : regionB kernel lo hi (dataAt d) = true)
    (hS : (List.range (hi + 1 - lo)).all
      (fun i => !Assumptions.swExp2Sites.contains (lo + i)) = true)
    (hlo : lo ≤ d.site.pc) (hhi : d.site.pc + 1 ≤ hi)
    (hev : ∀ ins, kernel.code[d.site.pc]? = some ins →
      (dataAt d).all (fun r => !(eventWrites ins.op).contains r) = true)
    (hland : ∀ e d', succ p L g d e = some (some d') →
      valuesData p L g d' = valuesData p L g d ∧
      (liveD (livePc d')).all (fun r => ctl r ||
        ((dataAt d).contains r && ((valuesData p L g d').map Prod.fst).contains r)) = true) :
    (codeD p L g).StepAt d := by
  have hseg : ∀ pc, lo ≤ pc → pc ≤ hi → Assumption.SegFreePc Assumptions.all pc := by
    intro pc h1 h2
    have := Gen.segFree_range hS (pc - lo) (by omega)
    rwa [show lo + (pc - lo) = pc by omega] at this
  exact Code.StepAt.lift (F' := factsD p L g) Gen.rulesFrame h (fun _ h => factsD_mono h)
    (fun _ h => mem_factsD h) hB hseg hlo hhi hev
    (fun e d' hn S T hS hT hST => land_data (hland e d' hn).1 (hland e d' hn).2 hS hT hST)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
