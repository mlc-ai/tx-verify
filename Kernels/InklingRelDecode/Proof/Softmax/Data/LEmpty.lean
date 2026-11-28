-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.LInit

@[expose] public section

/-! # The running sum when the loop has no round

From the barrier of the entry or the last preload the thread runs to the epilogue's wait, with the
running sum register at the zero bits (the loop's tail from pc 1049 keeps it). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The facts a stop at the epilogue holds: the running sum is the zero bits. -/
def lEmptyF (d : D) : List (Nat × Value) :=
  if d.c.site = .epilogue then [(1915, b32 0)] else []

theorem lempty_conv {R : Nat → Option Value} {s : Site}
    (h : Holds R (phi lIniKeys (fun _ => false) lIniV lIniV s.pc)) {d : D} (hs : d.c.site = s) :
    Holds R (lEmptyF d) := by
  unfold lEmptyF
  by_cases hq : d.c.site = .epilogue
  · simp only [hq, ↓reduceIte]
    rw [hq] at hs
    subst hs
    have : R 1915 = some (lIniV 1915) :=
      holds_mem h (mem_factsFrom (val := lIniV) (by simp [lIniKeys, Site.pc]))
    exact ⟨this, trivial⟩
  · simp only [hq, ↓reduceIte]; trivial

/-- **The running sum after the barrier of the entry**, at the epilogue. -/
theorem l_bar0_empty {d : D} (hs : d.c.site = .bar0) : DataStep (codeS e L g) lEmptyF d := by
  refine @bar0_open e L g d hs lEmptyF fun t ev hat hpc hstops => ?_
  refine goal_tab (ivs := [(576, 423), (1049, 208), (2560, 5)]) (keys := lIniKeys)
    (post := fun _ => false) (spec := lIniSpec) (V1 := lIniV) (V2 := lIniV)
    (by decide +kernel) (hseg_ivs (by decide +kernel))
    (lini_spec (fun _ => by decide +kernel)) (u := PTX.next t)
    (by rw [hpc]; decide +kernel) ⟨hat.2.1.trans rfl, hat.2.2.1.trans rfl, ?_⟩ hstops
    (fun R h => lempty_conv h rfl)
  rw [hpc]; simp [phi, lIniKeys, factsFrom]

/-- **The running sum after the last preload**, at the epilogue. -/
theorem l_pre63_empty {d : D} (hs : d.c.site = .pre 63) : DataStep (codeS e L g) lEmptyF d := by
  refine @pre63_open e L g d hs lEmptyF fun t x bs v c' hat hv hc hpc => ?_
  subst hc
  intro hstops
  refine goal_tab (ivs := [(806, 193), (1049, 208), (2560, 5)]) (keys := lIniKeys)
    (post := fun _ => false) (spec := lIniSpec) (V1 := lIniV) (V2 := lIniV)
    (by decide +kernel) (hseg_ivs (by decide +kernel))
    (lini_spec (fun h => by revert h; decide +kernel)) (u := after806 t v)
    ?_ ⟨rfl, rfl, ?_⟩ hstops (fun R h => lempty_conv h rfl)
  · show (inIvs _ (t.pc + 1) || evAtB kernel (t.pc + 1)) = true
    rw [hpc]; decide +kernel
  · show Holds _ (phi lIniKeys (fun _ => false) lIniV lIniV (t.pc + 1))
    rw [hpc]; simp [phi, lIniKeys, factsFrom]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
