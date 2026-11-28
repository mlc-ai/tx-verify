-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

/-- Elections completed in the current iteration, including elections the lane lost. -/
def Site.elections : Site → Nat
  | .warpBar p | .elect p => p.val
  | .copy p _ => p.val + 1
  | .page true => 2
  | _ => 0

/-- The last election of the iteration crosses the loop back edge at the last copy
or, for a non-elected lane, directly at the election. -/
def completedPairs (p : Fin 4) : Nat := if p.val = 3 then 4 else 0

theorem elections_finishPair (d : D) (p : Fin 4) :
    completedPairs p + (finishPair d p).site.elections = p.val + 1 := by
  fin_cases p <;> try rfl
  change 4 + (if _ then Site.endBar else .poll).elections = 4
  split <;> rfl

theorem elections_after_elect {L : Launch} {g mk inst lead : Nat} (d : D) (p : Fin 4)
    (nextD : D) (hn : next L g { d with site := .elect p }
      ⟨(Site.elect p).pc, .elect mk inst lead⟩ = some (some nextD)) :
    (if laneOf L g ≠ lead then completedPairs p else 0) + nextD.site.elections = p.val + 1 := by
  by_cases hl : laneOf L g = lead
  · simp [next, hl] at hn
    subst nextD
    simp [hl, Site.elections]
  · simp [next, hl] at hn
    subst nextD
    simpa [hl] using elections_finishPair {d with site := .elect p} p

end PTX.Kernels.InklingRelDecode.Proof.Loader
