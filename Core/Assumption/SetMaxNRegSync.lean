-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.PollAgree
public import Core.Thread.SetMaxNReg

@[expose] public section

/-!
# Assumption constructor `setMaxNRegSyncAt`

A kernel declares the setmaxnreg synchronization assumption with `Assumption.setMaxNRegSyncAt`,
naming exactly the `setmaxnreg` request sites whose request it does not require to follow the
previous request of its warpgroup in the base causality order. This file is not itself an
assumption.
-/

namespace PTX.Assumption

/-! ## ASM-SETMAXNREG-SYNC — a request at a named site need not follow a warpgroup synchronization
Statement: At the `setmaxnreg` request sites a kernel names, the model trusts that the request is
  legal although no synchronization of its warpgroup orders the previous requests of the warpgroup
  before it. The direction and count of the request, the containment of its warpgroup in the CTA
  and the agreement of the requests with one ordinal are still checked. A kernel that synchronizes
  its warpgroup between two `setmaxnreg` requests does not need this assumption.

Defs: Assumption.setMaxNRegSyncAt

Source:
- §9.7.21.5: "After executing a setmaxnreg instruction, all warps in the warpgroup must
    synchronize explicitly before executing subsequent setmaxnreg instructions."
- ERR-SETMAXNREG

Direction: trust

Effect: `setMaxNRegSyncAt name sites why` selects, at exactly the sites (`pc`) in `sites`, the hook
  `regSyncExempt` (ASM-INTERFACE). The fourth clause of `SetMaxNReg.UnsafeAt` (a thread of the
  previous request of the warpgroup is not ordered before the request by `baseCausality`) does not
  apply to a request at a selected site. Direction, count, warpgroup and ordinal agreement are
  checked as in `SetMaxNReg.Unsafe`. The constructor sets no `wf` and no `ub` and adds no ordering;
  with no site selected `SetMaxNReg.UnsafeAt` is `SetMaxNReg.Unsafe` (`unsafeAt_noExempt`). The
  statement is generated from the sites and lists every site it covers.

Review: A request whose count equals the count the warp already owns asks for no change, and the
  text states the synchronization requirement for subsequent requests without a case for that.
  Code generated for warp-specialized kernels can end a role by restoring the register count and
  branching back to a dispatch loop whose first instruction is another request of the same count,
  with no warpgroup synchronization in between. The generated code then violates the quoted
  sentence formally. Hardware accepts it; the text does not say what it does.
-/

/-- At exactly the `setmaxnreg` request sites `sites`, the request is not required to follow the
previous request of its warpgroup in the base causality order; `why` says why the kernel needs
it. -/
def setMaxNRegSyncAt (name : String) (sites : List Nat) (why : String) : Assumption where
  name := name
  statement := s!"A setmaxnreg request is legal although no synchronization of its warpgroup \
    orders the previous requests of the warpgroup before it, at exactly these sites: \
    {siteText sites}. {why}"
  regSyncExempt pc := sites.contains pc

end PTX.Assumption
