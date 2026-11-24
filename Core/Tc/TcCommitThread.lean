-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tma

@[expose] public section

namespace PTX
noncomputable section

/-! ## THREAD-TC-COMMIT — full-completion commit issue
Statement: A `tcgen05.commit` produces one issue event that names its target mbarriers: without a
  multicast mask the addressed mbarrier, and with a mask the mbarrier at the same shared-memory
  offset in each selected CTA of the cluster. Each target receives its arrive-on when the
  asynchronous operations that the commit tracks complete.

Defs: tcCommitTmpl

Source:
- §9.7.18.12.1 (commit operands and multicast mask)

Direction: scope

Applies: Full-completion commit, either cta_group, shared::cluster address, optional 16-bit
  multicast mask

Premises: The issuing thread exists, the mbarrier address is aligned shared memory in its cluster,
  and all selected ranks exist.

Effect: Issue event. Each target's arrival is an independent asynchronous effect. OBJ-MBAR-ORIGIN
  relates each arrive-on to the completion of the operations that the commit tracks.
-/
/-- The event of `tcgen05.commit`: its target specification, from the mbarrier address and the
multicast mask, or with the addressed CTA's rank alone when there is no mask. -/
def tcCommitTmpl (L : Launch) (g : Nat) (t : TState) : Op → Tmpl
  | .tcCommit group base off mask => ofExec do
    unless g < L.threads do throw .badValue
    let m ← mbarClusterLoc L g t base off
    let bits ← match mask with
      | none => pure (BitVec.ofNat 16 (2 ^ L.rankOfCta m.cta))
      | some mk => do pure (BitVec.ofNat 16 (← readBits L g t 16 mk).toNat)
    let some s := TcCommit.resolve L group (g / L.block) m bits | throw .badValue
    pure (.tc (.commit s) (next t))
  | _ => .ub .noRule

end
end PTX
