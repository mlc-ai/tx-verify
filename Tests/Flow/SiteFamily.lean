-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Steps
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Shape

/-! # Family entries of `site_cases` and `site_shape`

A `families [.c i … => proof]` entry keeps the fields of the constructor `c` whole: the family is
one goal, its fields are named `i …`, and the proof may mention them. Checked on the tml-fa4
output warp, whose store sites `.store st b` (eight sites) and ready sites `.ready st` (two)
are closed by its family theorems. If an entry split its family, `st` and `b` would not be
names in scope and the proofs below would not elaborate. -/

namespace PTX.Tests.SiteFamily
open PTX PTX.Proof PTX.Flow PTX.Kernels.TmlFa4Fwd PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue

-- the sites outside the families are closed by `skip_by`; no segment, invariant or guard tactic
-- runs
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

example (hp : Pre p L m) (hg : g < L.threads) (d : D)
    (hs : d.site = .q0 ∨ (∃ st b, d.site = .store st b) ∨ ∃ st, d.site = .ready st) :
    (code p L g ent).StepAt d := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_cases s except [.q0 => stepAt_read hp hg _ (.inl rfl)]
    families [.store st b => stepAt_store hp hg _ ⟨st, b, rfl⟩,
      .ready st => stepAt_ready hp hg _ ⟨st, rfl⟩]
    skip_by (simp at hs) trans [] seg_by (skip) inv_by (skip) guard_by (skip)

example (hp : Pre p L m) (d : D) (hs : (∃ st b, d.site = .store st b) ∨ d.site = .q1) :
    (code p L g ent).ShapeAt (Ev p L g) d := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  site_shape s except [.q1 => shapeAt_read _ (.inr (.inr rfl))]
    families [.store st b => shapeAt_write hp _ (.inr (.inl ⟨st, b, rfl⟩))]
    skip_by (simp at hs) unfolding [] reg_vals [] addr_by (skip)

end PTX.Tests.SiteFamily
