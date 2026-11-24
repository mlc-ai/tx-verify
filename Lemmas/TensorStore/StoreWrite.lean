-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

@[expose] public section

/-! # The writes of a finished tensor store

A proof tool for the output of a kernel. A one-byte footprint covers only its own location
(`Acc.loc_of_one`). In a complete execution every tensor store has finished, so it wrote each of
its in-bounds slots: the slot's write is the one-byte write of the store's recorded byte at the
slot's destination (`Complete.store_write`). -/

namespace PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A one-byte footprint covers only its own location. -/
theorem Acc.loc_of_one {a : Acc} {l : Loc} (hc : a.Covers l) (hn : a.size = 1) : a.loc = l := by
  obtain ⟨⟨sp, cta, addr⟩, size, acq, rel, scope, elem, relaxed⟩ := a
  obtain ⟨sp', cta', addr'⟩ := l
  obtain ⟨h1, h2, h3, h4⟩ := hc
  simp only at h1 h2 h3 h4 hn ⊢
  subst h1 h2 hn
  congr 1
  omega

/-- **A finished tensor store wrote each of its in-bounds slots**: in a complete execution, the
write of a slot with a destination is the one-byte write of the store's recorded byte there. -/
theorem Complete.store_write (hX : Consistent L K A mem0 X) (hd : Complete L X) {i : EvId}
    {a : Nat} {sp : TensorStore.Spec} (hi : X.TensorStoreIssue i a sp) {x y z : Nat} {l : Loc}
    (hl : TensorStore.writeLoc sp x y z = some l) :
    ∃ o b, X.tensorStores i = some o ∧ TensorStore.writeByte o x y z = some b ∧
      X.MemWrites (.async i (.write (.store x y z))) ⟨l, 1, false, false, .cta, 0, false⟩ [b] := by
  obtain ⟨o, ho, hfull⟩ := ((asyncDrained_iff X).mp hd.2.1).2.2.2.2.2.1 i a sp hi
  obtain ⟨⟨addr, hissue⟩, -, hok⟩ := hX.store i o ho
  obtain ⟨pc, he⟩ := hi
  obtain ⟨pc', he'⟩ := hissue
  rw [he] at he'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorStore.injEq] at he'
  obtain ⟨-, -, hsp⟩ := he'
  subst hsp
  unfold TensorStore.writeLoc at hl
  obtain ⟨slot, hslot, hdest⟩ := Option.bind_eq_some_iff.mp hl
  obtain ⟨b, hb⟩ := (hok.complete hfull).2 slot l hdest
  have hwb : TensorStore.writeByte o x y z = some b := by
    unfold TensorStore.writeByte
    rw [hslot]
    exact hb
  exact ⟨o, b, ho, hwb, o, a, b, ho, ⟨pc, he⟩, hl, hwb, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

end PTX
