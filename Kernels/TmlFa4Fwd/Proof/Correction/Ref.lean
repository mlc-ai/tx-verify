-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Places
public import Kernels.TmlFa4Fwd.Proof.Correction.Ledger
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' counts in closed form

The ledger's counts at every state of the correction machine are closed forms in the state's site
(its program counter), the number `r` of rescale rounds done and the number `ℓ` of LSE stores done
(`RefQ`). This file states them and proves the facts about places that the steps use; the steps
keep them (`RefStep.lean`).

* **Places.** A barrier class has its signal points: the program counters of the sites that fire
  its events (`ptsOf`; `sig` is the class a site's event belongs to, and `sig_pts` says the two
  agree). The points inside a rescale round (pc 8006 to 8446, `inRound`) are passed once per
  round. A state at site `s` with `r` rounds done has passed `passed pts s r` of them: those before
  `s` in the current pass (`before`: the points of the current round before `s`, the points
  outside the rounds before `s`, and for a lane without a tile only the points before the
  request's reads and those of the end), plus `r` times the points of a round.
* **Rounds.** A tile of `B` K/V blocks (`Bs`, the block count as the code compares it, a signed
  word) has `B - 1` rescale rounds, none when `B < 2`. In a round `r + 1 < B` and the counter
  `%r6218` is `r - B` (`loop`); from the final stage to the LSE stores all rounds are done
  (`tail`); before the rounds and on a lane without a tile `r = 0` (`pre`).
* **Stores.** The final stage stores eight elements per chunk (two four-word stores), 128 per
  stage, 256 in all (`finalStores`); the LSE stores follow, one or two or none (`ℓ ≤ lseB`).
* **Sub-steps.** A rescale load's implicit wait is at sub-step 1, the elements of a vector store at
  sub-steps 0 to 3, every other state at sub-step 0 (`kIn`).

The successors of a site are listed (`nexts`) and every move between listed sites is checked once
by evaluation (`moves_ok`): its places (`pmove`, or `rmove` at the end of a round), its regions
(`regOk`) and its stores (`stOk`, `lseOk`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 Scan)

noncomputable section

/-! ### Places -/

/-- **The count conjuncts** at state `d` with counts `n`, `r` rounds done and `ℓ` LSE stores
done. -/
structure RefQ (p : Params) (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) (r ℓ : Nat) : Prop where
  cnt : ∀ c, c ≠ .st → n c = passed (ptsOf c) d.site r
  st : n .st = finalStores d.site d.k + ℓ
  lse : ℓ ≤ lseB d.site
  sub : d.site.isFst = false → d.k = kIn d.site
  pre : preR d.site = true → r = 0
  loop : inRound d.site.pc = true → (r : Int) + 1 < Bs p L g d.v ∧ d.v.trip = i32 (r - Bs p L g d.v)
  tail : tailR d.site = true → (r : Int) + 1 = Bs p L g d.v ∨ (r = 0 ∧ Bs p L g d.v < 2)

/-- **The count conjuncts of the correction warps' reference invariant** at a counted state. -/
def RefCounts (p : Params) (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  ∃ r ℓ, RefQ p L g dn.1 dn.2 r ℓ

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
