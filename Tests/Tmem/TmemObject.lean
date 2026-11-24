-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.TmemObject

/-! Resource/lifetime tests: multiple live allocations, reuse, size and permit checks.
These test object transitions; Tests.TmemPairHistory checks execution integration. -/
namespace PTX.Tests.TmemObject
open PTX.Tmem

def first : State := ⟨true, some 64, 1, [⟨0, 0, 64⟩]⟩
def second : State := ⟨true, some 32, 2, [⟨0, 0, 64⟩, ⟨1, 64, 32⟩]⟩
def released : State := ⟨true, some 32, 2, [⟨1, 64, 32⟩]⟩
def reused : State := ⟨true, some 32, 3, [⟨1, 64, 32⟩, ⟨2, 0, 32⟩]⟩

example : perform {} (.alloc 64 0) = .done first := rfl
example : perform first (.alloc 32 64) = .done second := rfl
example : perform second (.dealloc 0 64) = .done released := rfl
example : perform released (.alloc 32 0) = .done reused := rfl
example : (reused.live[1]?).map Region.lifetime = some 2 := rfl
example : (first.live[0]?).map Region.lifetime = some 0 := rfl
example : perform first (.alloc 32 32) = .blocked := rfl
example : perform first (.alloc 32 512) = .blocked := rfl
example : perform first (.alloc 128 64) = .fault .increasingRequest := rfl
example : perform first (.alloc 48 64) = .fault .invalidColumns := rfl
example : perform released (.dealloc 0 64) = .fault .unmatchedRelease := rfl
example : perform second (.dealloc 0 32) = .fault .unmatchedRelease := rfl
example : perform first .relinquish = .done { first with permit := false } := rfl
example : perform { first with permit := false } (.alloc 32 64) =
    .fault .relinquishedPermit := rfl
example : perform { first with permit := false } (.dealloc 0 64) =
    .done { first with permit := false, live := [] } := rfl

end PTX.Tests.TmemObject
