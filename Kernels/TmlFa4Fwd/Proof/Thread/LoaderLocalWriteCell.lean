-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalAccess

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader (RingShape loaderVector)
open LocalAccessCode

noncomputable section

/-- A scalar write is exactly one of the two words of its decoded scratch array. -/
theorem localWriteCell {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {data : List Byte} (hWrite : X.Writes i a data)
    (hLocal : a.loc.space = .local) :
    ∃ site ∈ scalarSites, ∃ entry : Fin 2,
      X.get i = some ⟨site.accessPc, .wr a data⟩ ∧
      a = { loc := ⟨.local, i.1, l.localBase + kvLocalOffset site.array entry⟩
            size := site.word } := by
  obtain ⟨site, hs, he⟩ := localWriteSite hX hWrite hLocal
  obtain ⟨hLo, hHi, ins, ma, hCode, hOp, hSpace, hBase, hOff,
    hSem, hVec, hWidth, hVector, hMemKind⟩ := scalarLocation hs
  obtain ⟨t, o, entry, ht, hShape, hReg, hStep⟩ :=
    eventScalarAddress hp hX he hLo hHi site hs rfl
  obtain ⟨u, rfl⟩ : ∃ u, o = some u := by
    cases o with
    | none =>
      obtain ⟨_, _, hFire⟩ := hStep
      have hEnd := fires_none_ends hFire
      simp [Ends] at hEnd
    | some u => exact ⟨u, rfl⟩
  obtain ⟨actual, hActual, _, hFires⟩ := estep_event_source hStep
  rw [ht, hCode] at hActual
  obtain rfl := Option.some.inj hActual
  have hSub : t.sub = 0 := by
    by_contra! hn
    have hOne : t.sub = 1 := by have := hShape.1.1; omega
    obtain ⟨op, hc, hv, _⟩ := hShape.1.2 hOne
    rw [ht, hCode] at hc
    rw [congrArg Instr.op (Option.some.inj hc), hv] at hVector
    cases hVector
  rw [hOp, ht] at hFires
  have hStore : ma.kind = .store := by
    rcases hMemKind with hLoad | hStore
    · have hw := fires_write_op hFires rfl
      simp [writeOp, hLoad] at hw
    · exact hStore
  exact ⟨site, hs, entry, he, scalarFootprint hp entry hReg hSub hSpace hBase hOff hSem
    hVec hWidth (fires_localStoreAccess hSpace hStore hBase hFires)⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
