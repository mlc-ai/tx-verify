-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface

@[expose] public section

/-! # Every output byte has one writer

Byte `z` of element `(i, j)` of `D` is slot `(x, y, z)` of slice `s` of the rows of warp group `q`
of rank `r` of the tile of task `t` (`output_cover`). Some consumer's TMA store writes that slot
(`OutputCover`); a complete execution finished it, so it wrote every in-bounds slot (`store_write`).
Every other write of the byte is a tensor store's slot (`GlobalWrites`), which only that store's
slot writes (`OutputUnique`): `output_writes`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX

noncomputable section

namespace Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A one-byte footprint covers only its own location. -/
theorem loc_of_one {a : Acc} {l : Loc} (hc : a.Covers l) (hn : a.size = 1) : a.loc = l := by
  obtain ⟨⟨sp, cta, addr⟩, size, acq, rel, scope⟩ := a
  obtain ⟨sp', cta', addr'⟩ := l
  obtain ⟨h1, h2, h3, h4⟩ := hc
  simp only at h1 h2 h3 h4 hn ⊢
  subst h1 h2 hn
  congr 1
  omega

/-- **A finished tensor store wrote each of its in-bounds slots**: the write of the slot is one
byte, the store's recorded write. -/
theorem store_write (hX : Consistent L kernel Prod mem0 X) (hd : Complete L X) {i : EvId}
    {a : Nat} {sp : TensorStore.Spec} (hi : X.TensorStoreIssue i a sp) {x y z : Nat} {l : Loc}
    (hl : TensorStore.writeLoc sp x y z = some l) :
    ∃ o b, X.tensorStores i = some o ∧ TensorStore.writeByte o x y z = some b ∧
      X.MemWrites (.async i (.write (.store x y z))) ⟨l, 1, false, false, .cta, 0, false⟩ [b] := by
  obtain ⟨o, ho, hfull⟩ := ((asyncDrained_iff X).mp hd.2.1).2.2.2.2.2.1 i a sp hi
  obtain ⟨⟨addr, pc', he'⟩, -, hok⟩ := hX.store i o ho
  obtain ⟨pc, he⟩ := hi
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

/-- **The output bytes' writers**, from the write structure: the tiles' stores, their distinct
slots and the global writes. -/
theorem output_writes (hX : Consistent L kernel Prod mem0 X) (hd : Complete L X)
    (hc : OutputCover P L X) (hu : OutputUnique X) (hw : GlobalWrites P X) :
    OutputWrites P L X := by
  intro i hi j hj z hz
  obtain ⟨t, r, q, y, s, x, ht, hr, hq, hy, hs, hx, hrow, hcol⟩ := output_cover hi hj
  obtain ⟨g, k, pc, a, sp, c, he, hσ, hsite, hm, hn, hrk, hgq, hloc⟩ := hc t ht r hr q hq ⟨s, hs⟩
  have hl := hloc x y z hx hy hz
  rw [hrow, hcol] at hl
  have hi' : X.TensorStoreIssue (g, k) a sp := ⟨pc, he⟩
  obtain ⟨o, b, ho, hwb, hmw⟩ := store_write hX hd hi' hl
  refine ⟨g, k, pc, a, sp, c, ⟨s, hs⟩, x, y, o, b, he, hσ, hsite, hx, hy, ?_, ?_, ho, hwb, hmw,
    fun w a' bs hm' hc' => ?_⟩
  · simp only [Consumer.outRow, hm, hrk, hgq, hrow]
  · simp only [Consumer.outCol, hn, hcol]
  · obtain ⟨hsz, -, -, -, i', x', y', z', rfl⟩ := hw w a' bs hm' (hc'.1.symm.trans rfl)
    obtain ⟨o', addr', b', -, hi'', hl', -⟩ := hm'
    rw [loc_of_one hc' hsz] at hl'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hu i' (g, k) addr' a o'.spec sp x' y' z' x y z _ hi'' hi' hl' hl
    rfl

end Result

end

end PTX.Kernels.Fp16Gemm8192.Proof
