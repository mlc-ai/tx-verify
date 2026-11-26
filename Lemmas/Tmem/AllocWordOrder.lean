-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
import Core.Assembly.Dependency
public import Core.Memory.Order

@[expose] public section

/-! # The allocation word's store is ordered before a participant's read-back

`alloc_word_order`: a non-leader lane that made an allocation request with a shared result word
`dst` and later reads the word has, by the return dependency of its request
(`allocResult_witnessed`), the leader's store of the result (`Tmem.Pair.AllocResult`): a write of
the four bytes at `dst` by lane 0 of its warp at the request's pc. That store precedes the read in
model causality at every byte of the word the read covers
(`modelCausality.of_allocResultBefore`). -/

namespace PTX
open Tmem.Pair

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **The allocation result's store precedes the read-back** of a non-leader participant. -/
theorem alloc_word_order (hX : Consistent L K A mem0 X) {g k k' pc : Nat} {grp : CtaGroup}
    {dst : Loc} {n : Nat}
    (hall : X.get (g, k') = some ⟨pc, .tc (.resource grp (some dst) (.alloc n))⟩)
    (hkk : k' < k) (hk : k < (X.tr g).length) (hlane : laneOf L g ≠ 0) :
    ∃ s : EvId, SameWarp L s.1 g ∧ laneOf L s.1 = 0 ∧
      (∃ bs, X.get s = some ⟨pc, .wr { loc := dst, size := 4 } bs⟩) ∧
      ∀ {pc' : Nat} {a : Acc} {bs : List (Option Byte)} {l : Loc},
        X.get (g, k) = some ⟨pc', .rd a bs⟩ → a.Covers l → dst.InRange 4 l →
        modelCausality L X l (.thread s) (.thread (g, k)) := by
  have hret : Returned X (g, k') := by
    simp only [Returned, hall]
    show k' + 1 < (X.tr g).length
    omega
  obtain ⟨x, -, hx⟩ := hX.dependency.ready _ hret _ (allocResult_witnessed L X (g, k') hall hlane)
  cases x with
  | async => exact hx.elim
  | thread s =>
    obtain ⟨dst', hAR⟩ := hx
    have hAR' := hAR
    obtain ⟨hsw, hl0, -, -, j0, site, grp', nn, kk, bytes, -, -, hgi, -, -, hgs⟩ := hAR'
    rw [hall] at hgi
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq,
      Option.some.injEq] at hgi
    obtain ⟨rfl, rfl, rfl, -⟩ := hgi
    refine ⟨s, hsw, hl0, ⟨bytes, hgs⟩, fun {pc' a bs l} hrd hc hin => ?_⟩
    exact modelCausality.of_allocResultBefore L ⟨k', dst, a, bs, hAR, hkk, hin, ⟨pc', hrd⟩, hc⟩

end PTX
