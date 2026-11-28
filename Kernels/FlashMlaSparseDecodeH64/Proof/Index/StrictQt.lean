-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexSites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexVal
public import Lemmas.Flow.HavocTyped

@[expose] public section

/-! # The tags of the index warp's data registers by program counter

The control machine states the control registers exactly (`ixFacts`); the data registers (the pair
words, the shuffle words, the coordinates and the validity bits: `ixData`) are not stated. The
strict index proof keeps them defined by an invariant of the concrete state, `QT ixQt`
(`Lemmas/Flow/HavocTyped.lean`): the live data registers at `pc` hold the tags `ixQt pc`.

* a predicate register (id below 139) holds a predicate, a register of id 3000 and above (the
  64-bit addresses) 64 bits, any other data register 32 bits;
* the page sizes `%r497` and `%r502` are divisors (`div.u32` at pcs 2432, 2435 and 2520, 2523):
  `%r497` is nonzero from its load (`Pre.pagePos`) while it is live, `%r502` from the extra
  branch at pc 2503, from pc 2504 (`Pre.extraPos`: the extra loop is reached only when the extra
  length, hence `extra_topk`, is positive; the branch's fall-through proves it from the state's
  facts, `SegQ.branchEx`). The jump at pc 2498 skips the first pair's load (pc 2501) and the
  states at pcs 2502 and 2503 may have no extra loop to come. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Flow PTX.Flow.Tagged

/-- The tag of a data register by its id. -/
def ixTag (r : Nat) : Tag :=
  if r < 139 then .pred else if 3000 ≤ r then .bits 64 else .bits 32

/-- The divisors' nonzero tags at `pc`: `%r497` while live from its load, `%r502` while live in the
extra loop. -/
noncomputable def ixNz (pc : Nat) : Env :=
  (if 2350 ≤ pc ∧ (Flow.live pc).contains 497 then [(497, .nz 32)] else []) ++
  (if 2504 ≤ pc ∧ (Flow.live pc).contains 502 then [(502, .nz 32)] else [])

/-- **The tags the index warp's registers hold before `pc`**: its live data registers, and the
divisors' nonzero tags. -/
noncomputable def ixQt (pc : Nat) : Env :=
  ((Flow.live pc).filter fun r => !ixCtl r).map (fun r => (r, ixTag r)) ++ ixNz pc

/-- At the warp's entry no data register is live. -/
theorem ixQt_entry : ixQt 2332 = [] := by
  decide +kernel

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
