-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairHistory

namespace PTX.Tests.TmemPair
open Tmem Tmem.Pair

private def w (cta : Nat) (r : Tmem.Request) : WarpRequest :=
  ⟨cta, 0, fun _ => 0, 0, none, r⟩
private def rec (cta : Nat) (g : CtaGroup) (a : Tmem.Action) : Requests := ⟨w cta a.request, g, a⟩

-- Each CTA's allocator selects its own address for its half of a cta_group::2 allocation.
example : runRequests {} [rec 0 .two (.alloc 64 0)] =
    .done { previousColumns := some 64, nextLifetime := 1, live := [⟨0, 0, 64⟩] } := by decide
example : runRequests {} [rec 1 .two (.alloc 64 128)] =
    .done { previousColumns := some 64, nextLifetime := 1, live := [⟨0, 128, 64⟩] } := by decide

-- A new lifetime may reuse an address after its release.
example : runRequests {} [rec 0 .two (.alloc 64 0), rec 0 .two (.dealloc 0 64),
    rec 0 .two (.alloc 64 0)] =
    .done { previousColumns := some 64, nextLifetime := 2, live := [⟨1, 0, 64⟩] } := by decide

-- An occupied range blocks only the allocator that holds it.
example : runRequests {} [rec 1 .two (.alloc 64 128), rec 1 .two (.alloc 64 128)] = .blocked := by
  decide

-- Relinquishment affects the performing CTA's permit.
example : runRequests {} [rec 0 .two (.alloc 64 0), rec 0 .two .relinquish] =
    .done { permit := false, previousColumns := some 64, nextLifetime := 1, live := [⟨0, 0, 64⟩] }
    := by decide

-- The two requests of a cta_group::2 operation agree on kind and column count, not address.
example : compatible (.alloc 64) (.alloc 64) = true := rfl
example : compatible (.alloc 64) (.alloc 128) = false := rfl
example : compatible (.dealloc 0 64) (.dealloc 128 64) = true := rfl
example : compatible (.alloc 64) .relinquish = false := rfl

-- A cta_group::1 operation uses its CTA's allocator in the same way.
example : runRequests {} [rec 0 .one (.alloc 64 0), rec 0 .one (.alloc 32 64)] =
    .done { previousColumns := some 32, nextLifetime := 2, live := [⟨0, 0, 64⟩, ⟨1, 64, 32⟩] } := by
  decide
-- Growing requests and unmatched releases are faults of that allocator.
example : runRequests {} [rec 0 .one (.alloc 32 0), rec 0 .one (.alloc 64 32)] =
    .fault .increasingRequest := by decide
example : runRequests {} [rec 0 .one (.dealloc 0 32)] = .fault .unmatchedRelease := by decide

end PTX.Tests.TmemPair
