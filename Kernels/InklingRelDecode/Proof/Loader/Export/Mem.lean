-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.NotBulk
import Lemmas.Flow.Final
import Lemmas.Flow.SharedSym

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow

private def pairLoad : MemAccess :=
  { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 32, vec := 2,
    addr := ⟨.sharedSym 0, 212992⟩, dsts := [some 1905, some 467], srcs := [] }

/-- The vector element tag identifies which word of the shared count pair was read. -/
theorem pairAddress {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g k : Nat} {ac : Acc} {bs : List (Option Byte)} (hp : Pre Q L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (_hf : Follow Q L X)
    (_hw : g % L.block / 32 = 6) (he : X.get (g,k) = some ⟨2345, .rd ac bs⟩) :
    ac.loc = ⟨.shared, g / L.block, L.sharedBase + 212992 + 4 * ac.elem⟩ ∧ ac.size = 4 := by
  obtain ⟨_, bad⟩ | ⟨t, ins, o, _, hc, fire⟩ := get_source hX he
  · contradiction
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2345)
  change Fires 2345 (eventTmpl Assumptions.all L g t (.mem pairLoad)) ⟨2345, .rd ac bs⟩ o at fire
  clear hc
  generalize Assumptions.all = A at fire
  cases o with
  | none =>
    have ht : Ends ⟨2345,.rd ac bs⟩ := by
      apply fires_none_ends (e := ⟨2345,.rd ac bs⟩) (pc := 2345)
        (m := eventTmpl A L g t (.mem pairLoad))
      assumption
    rcases ht with ⟨_, h⟩ | h <;> cases h
  | some u =>
    have hrange := hp.sharedRange
    change L.sharedBase + 213340 ≤ 2 ^ 18 at hrange
    have hh := fires_ldv_sharedSym (a := pairLoad) (L := L) (g := g)
      (A := A) (t := t) (e := ⟨2345,.rd ac bs⟩) (pc := 2345)
      (u := u) (o := 0) (off := 212992)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl (by omega)
    generalize eventTmpl A L g t (.mem pairLoad) = tmpl at hh fire
    obtain ⟨a, bytes, eq, hl, hs, hj⟩ := hh (by assumption)
    cases eq
    exact ⟨by simpa only [Nat.add_zero, hj] using hl, hs⟩

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
