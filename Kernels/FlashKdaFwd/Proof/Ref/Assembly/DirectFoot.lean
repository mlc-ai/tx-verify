-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.DirectMem

@[expose] public section

/-!
# The memory operations of an execution, in three classes

`DirectMem.lean` classifies the events of a thread (`MemEv`). This file classifies the memory
operations of an execution: the intents `X.Intent r a w` ("the operation `r`, a thread event or
a stage of an asynchronous operation, has the footprint `a`, and writes when `w`"), pending or
performed. `intent_class` puts every intent into one of three classes:

1. the footprint lies in the *window* of the issuing thread (`InWin`: the first 98304 bytes of
   the shared memory of its own block);
2. the operation is a read of *launch input bytes* of global memory (`Input`);
3. the operation is a *global write* (`GWrite`): an element store of a partial last tile (a
   thread write at a state of the Store phase), the write of one byte of a tensor store of a
   full tile (Store phase), or the write of one byte of a tensor store of the final state
   (epilogue).

`no_nc` adds that no event of the kernel is an `nc` read, so the intents are all the memory
operations (`Execution.MemTouches`).

For a global write, `GWrite.frame` says that every byte it covers is a byte of the output of a
token of the batch or a byte of the final state, and `GWrite.unique` that two global writes
that cover one byte are one operation. The identification behind the second:

* a covered byte of the output array determines the sequence and the head, hence the thread
  block and its store leader (`outTag_inj`), the token (hence the tile and the row), the
  feature and the byte;
* a tile is stored either by tensor stores (a full tile) or by element stores (the partial
  last tile), never both;
* the position of the Store phase determines the count of the thread's earlier tensor stores
  (earlier global writes), so two events at one position are one event (`same_count`);
* a byte of the final state determines the thread block, the store (eight key features each)
  and the slot (`Epilogue.ts_state`), and the trace index of store `i` is the epilogue's entry
  index plus `3 + i`; a thread enters the epilogue once (`entered_unique`);
* the output array and the final state do not overlap (`Pre.outputApartFinal`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Direct
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (storeLeader blockOf)

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Small facts -/

/-- A byte covered by a footprint is in the footprint's memory space. -/
theorem covers_space {a : Acc} {l : Loc} (h : a.Covers l) : l.space = a.loc.space := h.1

/-- Two events of one class at positions with the same count of earlier events of the class
are one event. -/
theorem same_count {c : Event → Bool} {k k' : Nat} {e e' : Event} (he : X.get (g, k) = some e)
    (he' : X.get (g, k') = some e') (hc : c e = true) (hc' : c e' = true)
    (h : ((X.tr g).take k).countP c = ((X.tr g).take k').countP c) : k = k' :=
  Nat.le_antisymm (Store.lt_of_count rfl he' hc' h.symm) (Store.lt_of_count rfl he hc h)

/-- The output array and the final state do not overlap. -/
theorem not_output_state (hpre : Pre P L mem0) {l : Loc} (ho : P.OutputByte l)
    (hs : P.StateByte l) : False := by
  obtain ⟨k, hk, rfl⟩ := Top.outputByte_range ho
  obtain ⟨k', hk', he⟩ := Top.stateByte_range hs
  have hap := hpre.outputApartFinal
  simp only [Loc.mk.injEq, true_and] at he
  unfold Apart at hap
  omega

/-! ### The Store phase: a tensor store, an element store -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **A tensor store at a state of the Store phase** is store `i` of a full tile `t` by the
store leader of the block, with `16 t + i` earlier tensor stores of the thread. -/
theorem tile_at {k pc al : Nat} {sp : TensorStore.Spec} {s : D}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) (hσ : At (code L) X g k s)
    (hI : Store.Inv P X g k s) :
    ∃ t, ∃ i : Fin 16, sp = Store.tileSpec P g t i.val ∧
      16 * t + 16 ≤ P.length (seqOf P g) ∧ g = storeLeader L (g / L.block) ∧
      ((X.tr g).take k).countP Store.isTStore = 16 * t + i.val := by
  obtain ⟨pos, hr, hl, hev, -⟩ := Store.store_good hpre hX hg he hσ hI
  obtain ⟨t, i, rfl, -, rfl⟩ := Store.ev_ts_inv hev
  exact ⟨t, i, rfl, hr.pos.2.1, Store.leader_at hpre hr (by intro h; cases h),
    congrArg Store.Led.tstores hl⟩

/-- **A write event at a state of the Store phase** is element store `j` of chunk `c` of row
`row` of the partial last tile `t`, by the store leader of the block, with
`8 (16 row + c) + j` earlier global writes of the thread. -/
theorem elem_at {k pc : Nat} {a : Acc} {bs : List Byte} {s : D}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hσ : At (code L) X g k s)
    (hI : Store.Inv P X g k s) :
    ∃ t row c, ∃ j : Fin 8, a = Store.wrAcc P g t row c j.val ∧
      P.length (seqOf P g) < 16 * t + 16 ∧ row < P.length (seqOf P g) - 16 * t ∧ c < 16 ∧
      g = storeLeader L (g / L.block) ∧
      ((X.tr g).take k).countP Store.isGWrite = 8 * (16 * row + c) + j.val := by
  obtain ⟨pos, hr, hl, hev, -⟩ := Store.store_good hpre hX hg he hσ hI
  obtain ⟨t, row, c, j, rfl, -, rfl, -⟩ := Store.ev_wr_inv hev
  obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
  exact ⟨t, row, c, j, rfl, hpart, hrow, hc, Store.leader_at hpre hr (by intro h; cases h),
    congrArg Store.Led.gstores hl⟩

/-- A byte that a tensor store of the Store phase reads is in the thread's window. -/
theorem tile_read_win {k pc al x y z : Nat} {sp : TensorStore.Spec} {s : D} {l : Loc}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) (hσ : At (code L) X g k s)
    (hI : Store.Inv P X g k s) (hl : TensorStore.readLoc sp x y z = some l) :
    InWin P L g l 1 := by
  obtain ⟨t, i, rfl, -, -, -⟩ := tile_at hpre hX hg he hσ hI
  obtain ⟨h1, h2, h3, h4⟩ := readLoc_range hl
  have h256 : mapBytes 10 = 256 := rfl
  rw [h256] at h4
  have h2' : t % 2 < 2 := Nat.mod_lt _ (by decide)
  have hi := i.isLt
  exact ⟨h1, by rw [h2, block_div hpre], by omega, by omega⟩

/-- A byte that a tensor store of the epilogue reads is in the thread's window. -/
theorem final_read_win {k pc al x y z j0 : Nat} {sp : TensorStore.Spec} {l : Loc}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) (hE : Epilogue.Entered P L X g j0)
    (hj : j0 ≤ k) (hl : TensorStore.readLoc sp x y z = some l) : InWin P L g l 1 := by
  obtain ⟨-, -, h1, h2, h3, h4⟩ := Epilogue.ts_final hpre hX hg hE hj he hl
  have hb := hpre.sharedBase
  exact ⟨h1, h2, by omega, by omega⟩

/-- A tensor store of the Store phase is no reduction. -/
theorem tile_reduce {k pc al : Nat} {sp : TensorStore.Spec} {s : D}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) (hσ : At (code L) X g k s)
    (hI : Store.Inv P X g k s) : sp.reduce = none := by
  obtain ⟨t, i, rfl, -⟩ := tile_at hpre hX hg he hσ hI
  rfl

/-- A tensor store of the epilogue is no reduction. -/
theorem final_reduce {k pc al j0 : Nat} {sp : TensorStore.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) (hE : Epilogue.Entered P L X g j0)
    (hj : j0 ≤ k) : sp.reduce = none := by
  obtain ⟨i, -, -, -, -, rfl, -⟩ := Epilogue.ts_in hpre hX hg hE hj he
  rfl

/-- **A thread enters the epilogue once**: two entry positions before one event are equal. -/
theorem entered_unique {j0 j1 k : Nat} (hE0 : Epilogue.Entered P L X g j0)
    (hE1 : Epilogue.Entered P L X g j1) (h0 : j0 ≤ k) (h1 : j1 ≤ k)
    (hk : k ≤ (X.tr g).length) : j0 = j1 := by
  have key : ∀ {a b : Nat}, Epilogue.Entered P L X g a → Epilogue.Entered P L X g b → a ≤ b →
      b ≤ (X.tr g).length → b = a := by
    intro a b ⟨sa, ha, hina⟩ ⟨sb, hb, hinb⟩ hab hbl
    obtain ⟨pos, hr, -, hord, -⟩ := Epilogue.epilogue_weak hpre hX hg ha hina hab hbl hb
    have hs := hr.site.symm.trans hinb.1.site
    cases pos with
    | bar7 => simpa [Epilogue.ord] using hord
    | bar8 =>
      have := Site.bar.inj hs
      exact absurd this (by decide)
    | bar9 =>
      have := Site.bar.inj hs
      exact absurd this (by decide)
    | _ => simp [Epilogue.Pos.site] at hs
  rcases Nat.le_total j0 j1 with h | h
  · exact (key hE0 hE1 h (by omega)).symm
  · exact key hE1 hE0 h (by omega)

end

/-! ### Global writes -/

/-- **A write of global memory by the kernel**: the reference `r` with the footprint `a` is an
element store, the write of a byte of a tensor store of a tile, or the write of a byte of a
tensor store of the final state. -/
inductive GWrite (P : Params) (L : Launch) (X : Execution) (r : AsyncCopy.Ref) (a : Acc) :
    Prop where
  /-- An element store: a thread write at a state of the Store phase. -/
  | elem {g k pc : Nat} {bs : List Byte} {s : D} (hr : r = .thread (g, k))
      (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hσ : At (code L) X g k s)
      (hI : Store.Inv P X g k s)
  /-- The write of slot `(x, y, z)` of a tensor store at a state of the Store phase. -/
  | tile {g k pc al x y z : Nat} {sp : TensorStore.Spec} {s : D}
      (hr : r = .async (g, k) (.write (.store x y z)))
      (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
      (hw : TensorStore.writeLoc sp x y z = some a.loc) (hs : a.size = 1)
      (hσ : At (code L) X g k s) (hI : Store.Inv P X g k s)
  /-- The write of slot `(x, y, z)` of a tensor store of a thread in the epilogue. -/
  | final {g k pc al x y z j0 : Nat} {sp : TensorStore.Spec}
      (hr : r = .async (g, k) (.write (.store x y z)))
      (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
      (hw : TensorStore.writeLoc sp x y z = some a.loc) (hs : a.size = 1)
      (hE : Epilogue.Entered P L X g j0) (hj : j0 ≤ k)

/-- **What a write of the output array determines**: the byte `l` is byte `z` of the output of
token `tok` (of the sequence of thread `g`) and feature `v`, and `g` is the store leader of its
block. -/
structure OutTag (P : Params) (L : Launch) (g : Nat) (l : Loc) (tok : Nat) (v : Fin 128)
    (z : Nat) : Prop where
  lt : tok < P.length (seqOf P g)
  byte : z < 2
  eq : l = (P.outLoc (seqOf P g) (headOf P g) tok v).at z
  lead : g = storeLeader L (g / L.block)

/-- **The byte determines the writer's thread, the token, the feature and the byte index.** -/
theorem outTag_inj (hpre : Pre P L mem0) {g g' tok tok' z z' : Nat} {v v' : Fin 128} {l : Loc}
    (hg : g < L.threads) (hg' : g' < L.threads) (h : OutTag P L g l tok v z)
    (h' : OutTag P L g' l tok' v' z') : g = g' ∧ tok = tok' ∧ v = v' ∧ z = z' := by
  obtain ⟨hs, hh, ht, hv, hz⟩ := Protocol.outLoc_at_inj (headOf_lt hpre hg)
    (headOf_lt hpre hg') h.lt h'.lt h.byte h'.byte (h.eq.symm.trans h'.eq)
  refine ⟨?_, ht, hv, hz⟩
  have h1 := h.lead
  have h2 := h'.lead
  rw [← Store.blockOf_cta hpre g] at h1
  rw [← Store.blockOf_cta hpre g'] at h2
  rw [h1, h2, hs, hh]

/-- An output byte with a tag is a byte of the output of a token of the batch. -/
theorem OutTag.output (hpre : Pre P L mem0) (hg : g < L.threads) {l : Loc} {tok z : Nat}
    {v : Fin 128} (h : OutTag P L g l tok v z) : P.OutputByte l :=
  ⟨_, seqOf_lt hpre g, _, headOf_lt hpre hg, tok, h.lt, v, z, h.byte, h.eq⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **The tag of an element store**, for a byte it covers. -/
theorem elem_tag {k pc : Nat} {a : Acc} {bs : List Byte} {s : D} {l : Loc}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hσ : At (code L) X g k s)
    (hI : Store.Inv P X g k s) (hc : a.Covers l) :
    ∃ t row c, ∃ j : Fin 8, ∃ z, ∃ hv : 8 * c + j.val < 128,
      OutTag P L g l (16 * t + row) ⟨8 * c + j.val, hv⟩ z ∧ row < 16 ∧
      P.length (seqOf P g) < 16 * t + 16 ∧
      ((X.tr g).take k).countP Store.isGWrite = 8 * (16 * row + c) + j.val := by
  obtain ⟨t, row, c, j, rfl, hpart, hrow, hc16, hlead, hcnt⟩ := elem_at hpre hX hg he hσ hI
  have hj := j.isLt
  obtain ⟨h1, h2, h3, h4⟩ := hc
  simp only [Store.wrAcc] at h1 h2 h3 h4
  refine ⟨t, row, c, j, l.addr - (P.outputBase + 256 * ((firstToken P.length (seqOf P g) +
    (16 * t + row)) * P.heads + headOf P g) + 2 * (8 * c + j.val)), by omega,
    ⟨by omega, by omega, ?_, hlead⟩, by omega, hpart, hcnt⟩
  obtain ⟨sp, ct, ad⟩ := l
  simp only at h1 h2 h3 h4
  subst h1 h2
  simp only [Params.outLoc, Loc.at, Loc.mk.injEq, true_and]
  omega

/-- **The tag of a slot of a tensor store of a tile.** -/
theorem tile_tag {k pc al x y z : Nat} {sp : TensorStore.Spec} {s : D} {l : Loc}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) (hσ : At (code L) X g k s)
    (hI : Store.Inv P X g k s) (hw : TensorStore.writeLoc sp x y z = some l) :
    ∃ t, ∃ i : Fin 16, ∃ hv : 8 * i.val + x < 128,
      OutTag P L g l (16 * t + y) ⟨8 * i.val + x, hv⟩ z ∧ x < 8 ∧ y < 16 ∧
      16 * t + 16 ≤ P.length (seqOf P g) ∧
      ((X.tr g).take k).countP Store.isTStore = 16 * t + i.val := by
  obtain ⟨t, i, rfl, hfull, hlead, hcnt⟩ := tile_at hpre hX hg he hσ hI
  obtain ⟨hx, hy, hz⟩ := Store.tileSpec_lt (.inl hw)
  have hi := i.isLt
  rw [(Store.tileSpec_slot hpre hg hi hfull hx hy hz).1] at hw
  exact ⟨t, i, by omega, ⟨by omega, hz, (Option.some.inj hw).symm, hlead⟩, hx, hy, hfull, hcnt⟩

omit hg in
/-- **Every byte a global write covers is an output byte or a byte of the final state.** -/
theorem GWrite.frame {r : AsyncCopy.Ref} {a : Acc} {l : Loc} (h : GWrite P L X r a)
    (hc : a.Covers l) : P.OutputByte l ∨ P.StateByte l := by
  cases h with
  | elem hr he hσ hI =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨t, row, c, j, z, hv, htag, -⟩ := elem_tag hpre hX hg he hσ hI hc
    exact .inl (htag.output hpre hg)
  | tile hr he hw hs hσ hI =>
    have hg := Frame.lt_of_get hX he
    rw [Protocol.covers_one hs hc] at hw
    obtain ⟨t, i, hv, htag, -⟩ := tile_tag hpre hX hg he hσ hI hw
    exact .inl (htag.output hpre hg)
  | final hr he hw hs hE hj =>
    have hg := Frame.lt_of_get hX he
    rw [Protocol.covers_one hs hc] at hw
    exact .inr (Epilogue.ts_writes_state hpre hX hg hE hj he hw)

omit hg in
/-- A global write is to global memory. -/
theorem GWrite.global {r : AsyncCopy.Ref} {a : Acc} (h : GWrite P L X r a) :
    a.loc.space = .global := by
  cases h with
  | elem hr he hσ hI =>
    obtain ⟨t, row, c, j, rfl, -⟩ := elem_at hpre hX (Frame.lt_of_get hX he) he hσ hI
    rfl
  | tile hr he hw hs hσ hI => exact Execution.store_writeLoc_global hw
  | final hr he hw hs hE hj => exact Execution.store_writeLoc_global hw

omit hg in
/-- **Two global writes that cover one byte are one operation.** -/
theorem GWrite.unique {r r' : AsyncCopy.Ref} {a b : Acc} {l : Loc} (h : GWrite P L X r a)
    (h' : GWrite P L X r' b) (hc : a.Covers l) (hc' : b.Covers l) : r = r' := by
  cases h with
  | elem hr he hσ hI =>
    have hg := Frame.lt_of_get hX he
    obtain ⟨t, row, c, j, z, hv, htag, hrow, hpart, hcnt⟩ := elem_tag hpre hX hg he hσ hI hc
    cases h' with
    | elem hr' he' hσ' hI' =>
      have hg' := Frame.lt_of_get hX he'
      obtain ⟨t', row', c', j', z', hv', htag', hrow', hpart', hcnt'⟩ :=
        elem_tag hpre hX hg' he' hσ' hI' hc'
      obtain ⟨rfl, htok, hfe, -⟩ := outTag_inj hpre hg hg' htag htag'
      have hfe' : 8 * c + j.val = 8 * c' + j'.val := congrArg Fin.val hfe
      have hj := j.isLt
      have hj' := j'.isLt
      have hk := same_count he he' (c := Store.isGWrite)
        (decide_eq_true ((GWrite.elem rfl he hσ hI).global hpre hX))
        (decide_eq_true ((GWrite.elem rfl he' hσ' hI').global hpre hX))
        (by rw [hcnt, hcnt']; omega)
      rw [hr, hr', hk]
    | tile hr' he' hw' hs' hσ' hI' =>
      have hg' := Frame.lt_of_get hX he'
      rw [Protocol.covers_one hs' hc'] at hw'
      obtain ⟨t', i', hv', htag', hx', hy', hfull', -⟩ := tile_tag hpre hX hg' he' hσ' hI' hw'
      obtain ⟨rfl, htok, -, -⟩ := outTag_inj hpre hg hg' htag htag'
      omega
    | final hr' he' hw' hs' hE' hj' =>
      have hg' := Frame.lt_of_get hX he'
      rw [Protocol.covers_one hs' hc'] at hw'
      exact (not_output_state hpre (htag.output hpre hg)
        (Epilogue.ts_writes_state hpre hX hg' hE' hj' he' hw')).elim
  | tile hr he hw hs hσ hI =>
    have hg := Frame.lt_of_get hX he
    rw [Protocol.covers_one hs hc] at hw
    obtain ⟨t, i, hv, htag, hx, hy, hfull, hcnt⟩ := tile_tag hpre hX hg he hσ hI hw
    cases h' with
    | elem hr' he' hσ' hI' =>
      have hg' := Frame.lt_of_get hX he'
      obtain ⟨t', row', c', j', z', hv', htag', hrow', hpart', -⟩ :=
        elem_tag hpre hX hg' he' hσ' hI' hc'
      obtain ⟨rfl, htok, -, -⟩ := outTag_inj hpre hg hg' htag htag'
      omega
    | tile hr' he' hw' hs' hσ' hI' =>
      have hg' := Frame.lt_of_get hX he'
      rw [Protocol.covers_one hs' hc'] at hw'
      obtain ⟨t', i', hv', htag', hx', hy', hfull', hcnt'⟩ :=
        tile_tag hpre hX hg' he' hσ' hI' hw'
      obtain ⟨rfl, htok, hfe, rfl⟩ := outTag_inj hpre hg hg' htag htag'
      have hfe' : 8 * i.val + _ = 8 * i'.val + _ := congrArg Fin.val hfe
      have hk := same_count he he' (c := Store.isTStore) rfl rfl
        (by rw [hcnt, hcnt']; omega)
      obtain rfl : _ = _ := show _ = _ from (by omega : _ = _)
      rw [hr, hr', hk]
      congr 3 <;> omega
    | final hr' he' hw' hs' hE' hj' =>
      have hg' := Frame.lt_of_get hX he'
      rw [Protocol.covers_one hs' hc'] at hw'
      exact (not_output_state hpre (htag.output hpre hg)
        (Epilogue.ts_writes_state hpre hX hg' hE' hj' he' hw')).elim
  | @final g k pc al x y z j0 sp hr he hw hs hE hj =>
    have hg := Frame.lt_of_get hX he
    rw [Protocol.covers_one hs hc] at hw
    have hst := Epilogue.ts_writes_state hpre hX hg hE hj he hw
    cases h' with
    | elem hr' he' hσ' hI' =>
      have hg' := Frame.lt_of_get hX he'
      obtain ⟨t', row', c', j', z', hv', htag', -⟩ := elem_tag hpre hX hg' he' hσ' hI' hc'
      exact (not_output_state hpre (htag'.output hpre hg') hst).elim
    | tile hr' he' hw' hs' hσ' hI' =>
      have hg' := Frame.lt_of_get hX he'
      rw [Protocol.covers_one hs' hc'] at hw'
      obtain ⟨t', i', hv', htag', -⟩ := tile_tag hpre hX hg' he' hσ' hI' hw'
      exact (not_output_state hpre (htag'.output hpre hg') hst).elim
    | @final g' k' pc' al' x' y' z' j1 sp' hr' he' hw' hs' hE' hj' =>
      have hg' := Frame.lt_of_get hX he'
      rw [Protocol.covers_one hs' hc'] at hw'
      obtain ⟨sq, hsq, hd, hhd, v, kk, bb, hbb, hl⟩ := hst
      rw [hl] at hw hw'
      obtain ⟨hlead, -, -, -, i, hsp, hx, hy, hkk, hz⟩ :=
        Epilogue.ts_state hpre hX hg hE hj hhd hbb he hw
      obtain ⟨hlead', -, -, -, i', hsp', hx', hy', hkk', hz'⟩ :=
        Epilogue.ts_state hpre hX hg' hE' hj' hhd hbb he' hw'
      obtain rfl : g = g' := hlead.trans hlead'.symm
      obtain ⟨i1, -, hk1, -, -, hsp1, -⟩ := Epilogue.ts_in hpre hX hg hE hj he
      obtain ⟨i2, -, hk2, -, -, hsp2, -⟩ := Epilogue.ts_in hpre hX hg hE' hj' he'
      have hinj : ∀ {u w : Nat}, Epilogue.finalSpec P L g u = Epilogue.finalSpec P L g w →
          u = w := by
        intro u w huw
        have := congrArg (fun sp : TensorStore.Spec => sp.sharedBase.addr) huw
        simp only [Epilogue.finalSpec] at this
        omega
      have e1 : i.val = i1.val := hinj (hsp.symm.trans hsp1)
      have e2 : i'.val = i2.val := hinj (hsp'.symm.trans hsp2)
      have hkl : k ≤ (X.tr g).length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1
      have hkl' : k' ≤ (X.tr g).length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp he').1
      have hii : i.val = i'.val := by omega
      have hent : j0 = j1 := by
        rcases Nat.le_total k k' with hle | hle
        · exact entered_unique hpre hX hg hE hE' (hj.trans hle) hj' hkl'
        · exact entered_unique hpre hX hg hE hE' hj (hj'.trans hle) hkl
      obtain rfl : k = k' := by omega
      obtain rfl : x = x' := by omega
      obtain rfl : y = y' := by omega
      obtain rfl : z = z' := by omega
      rw [hr, hr']

end

/-! ### The classes of an intent -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **No event of the kernel is an `nc` read.** -/
theorem no_nc {i : EvId} {a : Acc} {bs : List (Option Byte)} (h : X.NcReads i a bs) : False := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := h
  have hm := memEv hpre hX he (fun f h => by cases h)
  cases hm with
  | quiet h => exact h.1 a rfl

/-- **The three classes of a memory operation**: its footprint is in the window of the issuing
thread; or it is a read of launch input bytes of global memory; or it is a global write. -/
theorem intent_class {r : AsyncCopy.Ref} {a : Acc} {w : Bool} (hi : X.Intent r a w) :
    InWin P L r.issuer.1 a.loc a.size ∨
      (a.loc.space = .global ∧ w = false ∧ ∀ l, a.Covers l → Input P mem0 l) ∨
      (w = true ∧ GWrite P L X r a) := by
  rcases r with ⟨g, k⟩ | ⟨⟨g, k⟩, p⟩
  · -- a thread access
    rcases intent_thread hi with ⟨pc, bs, he, rfl⟩ | ⟨pc, bs, he, rfl⟩ | ⟨pc, old, new, he⟩
    · have hm := memEv hpre hX he (fun f h => by cases h)
      cases hm with
      | quiet h => exact absurd rfl (h.1 a)
      | rdWin h => exact .inl h
      | rdIn hs h => exact .inr (.inl ⟨hs, rfl, h⟩)
    · have hm := memEv hpre hX he (fun f h => by cases h)
      cases hm with
      | quiet h => exact absurd rfl (h.1 a)
      | wrWin h => exact .inl h
      | wrElem hσ hI hs => exact .inr (.inr ⟨rfl, .elem rfl he hσ hI⟩)
    · have hm := memEv hpre hX he (fun f h => by cases h)
      cases hm with
      | quiet h => exact absurd rfl (h.1 a)
  · -- a stage of an asynchronous operation
    obtain ⟨hw, hf⟩ := hi
    have hg : ∀ {e : Event}, X.get (g, k) = some e → g < L.threads :=
      fun he => Frame.lt_of_get hX he
    rcases footprint_cases hf with
      ⟨pc, al, sp, x, y, z, he, hs, hp⟩ | ⟨pc, al, sp, x, y, z, he, hs, hp⟩ | ⟨e, he, h1, h2⟩
    · have hm := memEv hpre hX he (fun f h => by cases h)
      cases hm with
      | quiet h => exact absurd rfl (h.2.2.1 al sp)
      | load hsh hrd hwr =>
        rcases hp with ⟨rfl, hl⟩ | ⟨rfl, hl⟩
        · refine .inr (.inl ⟨Execution.tensor_readLoc_global hl, hw, fun l hc => ?_⟩)
          obtain rfl := Protocol.covers_one hs hc
          exact hrd x y z _ hl
        · exact .inl (hs ▸ hwr x y z _ hl)
    · have hm := memEv hpre hX he (fun f h => by cases h)
      cases hm with
      | quiet h => exact absurd rfl (h.2.2.2 al sp)
      | tile hσ hI =>
        rcases hp with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hred⟩
        · exact .inl (hs ▸ tile_read_win hpre hX (hg he) he hσ hI hl)
        · exact .inr (.inr ⟨hw, .tile rfl he hl hs hσ hI⟩)
        · rw [tile_reduce hpre hX (hg he) he hσ hI] at hred
          cases hred
      | final hE hj =>
        rcases hp with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hred⟩
        · exact .inl (hs ▸ final_read_win hpre hX (hg he) he hE hj hl)
        · exact .inr (.inr ⟨hw, .final rfl he hl hs hE hj⟩)
        · rw [final_reduce hpre hX (hg he) he hE hj] at hred
          cases hred
    · obtain ⟨e', he', ha'⟩ := asyncFootprint_asyncOf hf
      obtain rfl : e' = e := Option.some.inj (he'.symm.trans he)
      have hne : ∀ f, e'.kind ≠ .ub f := by
        intro f hk
        obtain ⟨pc, kd⟩ := e'
        simp only at hk
        subst hk
        exact ha'.elim
      have hm := memEv hpre hX he hne
      cases hm with
      | quiet h => exact absurd ha' (h.2.1 a)
      | rdWin h => exact ha'.elim
      | rdIn hs h => exact ha'.elim
      | wrWin h => exact ha'.elim
      | wrElem hσ hI hs => exact ha'.elim
      | load hsh hrd hwr => exact absurd rfl (h1 _ _)
      | tile hσ hI => exact absurd rfl (h2 _ _)
      | final hE hj => exact absurd rfl (h2 _ _)

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Direct
