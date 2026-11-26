-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Direct
public import Kernels.FlashKdaFwd.Proof.Values.Ends.Contract

@[expose] public section

/-! # Exports of the Store phase: the value layer's contracts for the partial last tile

The store path of a partial last tile: per live row, sixteen chunks of eight features; per
chunk, one vector load `ld.shared.v4.b32` (instruction 3020: four read events, the sites
`load 177`, `loadEl1 0`, `loadEl2 0`, `loadEl3 0`) and eight `st.global.b16` (instructions 3025
to 3032, the sites `store 10` to `store 17`). The value layer follows the data through the
registers of the store leader and takes from this phase, in `Proof/Values/Ends/Contract.lean`,
the structures `StoreRef` (where the events of a chunk are, and their addresses) and the field
`elem` of `StoreCtl` (the control half of the eight stores). This file proves their shares for
a followed state that satisfies the phase invariant:

* `storeRef_elem` (`StoreRef.elem`): a write is the `(4 + i)`-th event after a state at the
  vector load;
* `storeRef_chunk` (`StoreRef.chunk`): the twelve events after a state at the vector load
  (`chunk_at`: for a given chunk);
* `storeCtl_elem` (`StoreCtl.elem`): a state at store `i` comes `4 + i` events after a state
  at the vector load; if the source register converts to 16 bits, the event is the write of
  its bytes;
* `rd_event`: the event of a state at one of the four read sites is the read of its element
  (control only), with the footprint `rdAcc` (`rdAcc_loc`: in the value layer's terms).

Words: `Values.seqOf P L g`, `Values.headOf P L g` are the value layer's names of the sequence
and the head of the thread's block (`seqOf P g`, `headOf P g` of `Ref/Common.lean` under the
precondition); `Values.Ends.storeFullBar L g t` is `Bar.storeFull` of stage `t % 2` of the
thread's block; `Values.Ends.elemReg i` is the source register `gstSrc i` of store `i`.

**For the assembly of the value-ends contracts** (`Ref/Assembly/ValuesEndsRef.lean:
ValuesEnds.StoreOwes`, proved in `ValuesOwes.lean` from the theorems here), in that structure's
statements: `storeCtl_elem` (field `elem`); `owes_chunk` (field `chunk`: `StoreRef.chunk` for a
state at the vector load of which only the register facts are known, the invariant with its
ledger being available when no undefined-behaviour event precedes the position; there may be no
event at the position); `owes_reads` (field `reads`: a state at the `m`-th element read, `rdIdx`,
with an event, is `m` events after a state at the vector load, and the events from there up to
it are reads); `owes_acc_free` (no access of the phase covers a byte of the bfloat16 state copy
`state_acc`, window offsets below 32768); `owes_ts_out` (no tensor store of the phase writes a
byte of the final state: it writes output bytes, which `Pre.outputApartFinal` keeps apart).

The data conditions are not here: that the bytes of each read rebuild to a value and that the
four loaded words unpack into pairs of 16-bit halves (the machine's run after the fourth read,
`across (Run.r3021_cond …)`), and that the source of a store converts to 16 bits, are the value
layer's. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses storeLeader bar0Before stageOf)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The value layer's sequence and head of a thread's block are those of `Ref/Common.lean`. -/
theorem seqOf_values (hpre : Pre P L mem0) (g : Nat) : Values.seqOf P L g = seqOf P g := by
  simp only [Values.seqOf, seqOf, hpre.block]

theorem headOf_values (hpre : Pre P L mem0) (g : Nat) : Values.headOf P L g = headOf P g := by
  simp only [Values.headOf, headOf, hpre.block]

/-- The source register of store `i` in the value layer's table. -/
theorem elemReg_eq (i : Nat) : Values.Ends.elemReg i = gstSrc i := rfl

/-- The instruction of global store `i`. -/
theorem store_pc (i : Fin 8) : (Site.store ⟨10 + i.val, by omega⟩).pc = 3025 + i.val := by
  fin_cases i <;> rfl

/-- One position is at one place of one chunk. -/
theorem InChunk.inj {t row c n t' row' c' n' : Nat} {pos : Pos} (h : InChunk t row c n pos)
    (h' : InChunk t' row' c' n' pos) : t = t' ∧ row = row' ∧ c = c' ∧ n = n' := by
  cases pos <;> first
    | exact False.elim h
    | (obtain ⟨rfl, rfl, rfl, rfl⟩ := h
       obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
       exact ⟨rfl, rfl, rfl, rfl⟩)

/-- A position at the vector-load site is the first position of a chunk. -/
theorem pos_of_load {pos : Pos} (h : pos.site = .load 177) : ∃ t row c, pos = .ld0 t row c := by
  cases pos <;> first
    | exact ⟨_, _, _, rfl⟩
    | exact absurd h (by simp [Pos.site])

/-- A position at the site of global store `i` is that store of a chunk. -/
theorem pos_of_store {pos : Pos} {i : Fin 8} (h : pos.site = .store ⟨10 + i.val, by omega⟩) :
    ∃ t row c, pos = .gst t row c i := by
  cases pos with
  | gst t row c j =>
    simp only [Pos.site, Site.store.injEq, Fin.mk.injEq] at h
    obtain rfl : j = i := Fin.ext (by omega)
    exact ⟨_, _, _, rfl⟩
  | _ => exact absurd h (by simp [Pos.site])

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **A state at global store `i` comes `4 + i` events after a state at the vector load** of
its chunk. -/
theorem store_back {k0 k : Nat} {d : D} {t row c : Nat} {i : Fin 8} (hen : Entered P L X g k0)
    (hk0 : k0 ≤ k) (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hr : RefAt P g (.gst t row c i) d)
    (hl : ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) (.gst t row c i)) :
    ∃ k1 d0, k = k1 + 4 + i.val ∧ Frame.stateAt (code L) X g k1 = some (some d0) ∧
      d0.site = .load 177 := by
  obtain ⟨h1, -, d0, h3, h4, -⟩ := chunk_back hpre hX hg hen hk0 hk hσ hr hl
    (t := t) (row := row) (c := c) (n := 4 + i.val) ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨k - (4 + i.val), d0, by omega, h3, h4.site⟩

/-- **`StoreRef.elem`**: a write event at a state of the phase is the `(4 + i)`-th event after
a state at the vector load (the site `load 177`), for the index `i` of its store. -/
theorem storeRef_elem {k0 k pc : Nat} {a : Acc} {bs : List Byte} {s : D}
    (hen : Entered P L X g k0) (hk0 : k0 ≤ k) (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    ∃ k1 d0, ∃ i : Fin 8, k = k1 + 4 + i.val ∧
      Frame.stateAt (code L) X g k1 = some (some d0) ∧ d0.site = .load 177 := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨t, row, c, j, rfl, -⟩ := ev_wr_inv hev
  obtain ⟨k1, d0, h1, h2, h3⟩ := store_back hpre hX hg hen hk0
    (List.getElem?_eq_some_iff.mp he).1 hσ hr hl
  exact ⟨k1, d0, j, h1, h2, h3⟩

/-- **`StoreCtl.elem`**: a followed state of the phase at the site of global store `i`, with an
event: the state is `4 + i` positions after a state at the vector load; and if the source
register converts to 16 bits, the event is the write of exactly those bytes (the address is an
even output address, so nothing but the value can make the event undefined behaviour). -/
theorem storeCtl_elem {k0 k : Nat} {d : D} {e : Event} (i : Fin 8) (hen : Entered P L X g k0)
    (hk0 : k0 ≤ k) (hσ : Frame.stateAt (code L) X g k = some (some d)) (hI : Inv P X g k d)
    (hs : d.site = .store ⟨10 + i.val, by omega⟩) (he : X.get (g, k) = some e) :
    (∃ k1 d0, k = k1 + 4 + i.val ∧ Frame.stateAt (code L) X g k1 = some (some d0) ∧
      d0.site = .load 177) ∧
    ∀ v', storeValue 16 (d.x (Values.Ends.elemReg i.val)) = .ok v' →
      ∃ a, e = ⟨d.site.pc, .wr a v'.toBytes⟩ := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨t, row, c, rfl⟩ := pos_of_store (hr.site.symm.trans hs)
  refine ⟨store_back hpre hX hg hen hk0 (List.getElem?_eq_some_iff.mp he).1 hσ hr hl,
    fun v' hv' => ?_⟩
  rw [hs, store_pc i]
  rw [elemReg_eq] at hv'
  rcases hev with ⟨v, hv, rfl⟩ | ⟨f, hf, -⟩
  · rw [hv'] at hv
    cases hv
    exact ⟨_, rfl⟩
  · rw [hv'] at hf
    cases hf

/-- **The event of a state at a read site** (control only): at a state of the phase at one of
the four sites of the vector load, the event is the read of four bytes of element `m` of a
chunk `(t, row, c)` of a live row of the output stage of the partial tile `t`. -/
theorem rd_event {k : Nat} {d : D} {e : Event} {t row c m : Nat} {pos : Pos}
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hr : RefAt P g pos d)
    (hc : InChunk t row c m pos) (hm : m < 4) (he : X.get (g, k) = some e) :
    ∃ bs, bs.length = 4 ∧ e = ⟨3020, .rd (rdAcc P g t row c m) bs⟩ := by
  have hev := event_shape hpre hX hg he hσ hr
  cases pos <;> first
    | exact False.elim hc
    | (obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
       first | exact hev | (exfalso; omega))

omit hX hg in
/-- The footprint of an element read in the terms of the value layer. -/
theorem rdAcc_loc (t row c m : Nat) :
    (rdAcc P g t row c m).size = 4 ∧
      (rdAcc P g t row c m).loc = ⟨.shared, g / L.block,
        L.sharedBase + (86912 + 4096 * (t % 2) + (16 * row + 256 * c + 4 * m))⟩ := by
  refine ⟨rfl, ?_⟩
  simp only [rdAcc, hpre.sharedBase, block_div hpre, Loc.mk.injEq, true_and]
  omega

/-- **The twelve events after a state at the vector load of the chunk `(t, row, c)`**: the
next four events, where they are reads, are the four 4-byte elements of the 16 bytes at offset
`16 row + 256 c` of output stage `t % 2`, each after `t / 2 + 1` successful polls of the
stage's "full" mbarrier; the eight events after them, where they are writes, are the 2-byte
stores of the outputs of the channels `8 c` to `8 c + 7` of token `16 t + row`. -/
theorem chunk_at {k : Nat} {d : D} {t row c : Nat}
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hr : RefAt P g (.ld0 t row c) d)
    (hl : ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) (.ld0 t row c)) :
    (∀ m < 4, ∀ pc a bs, X.get (g, k + m) = some ⟨pc, .rd a bs⟩ → a.size = 4 ∧
      a.loc = ⟨.shared, g / L.block,
        L.sharedBase + (86912 + 4096 * (t % 2) + (16 * row + 256 * c + 4 * m))⟩ ∧
      okPolls (Values.Ends.storeFullBar L g t) ((X.tr g).take (k + m)) = t / 2 + 1) ∧
    ∀ i : Fin 8, ∀ pc a bs, X.get (g, k + 4 + i.val) = some ⟨pc, .wr a bs⟩ → a.size = 2 ∧
      ∃ v : Fin 128, v.val = 8 * c + i.val ∧
        a.loc = P.outLoc (Values.seqOf P L g) (Values.headOf P L g) (16 * t + row) v := by
  have hch : InChunk t row c 0 (.ld0 t row c) := ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
  rw [seqOf_values hpre, headOf_values hpre]
  refine ⟨?_, ?_⟩
  · intro m hm pc a bs he
    obtain ⟨s', pos', hσ', hr', hl', hc'⟩ := chunk_fwd hpre hX hg hσ hr hl hch m (by omega) he
      (fun _ _ h => by cases h)
    obtain ⟨bs', -, heq⟩ := rd_event hpre hX hg hσ' hr' hc' hm he
    cases heq
    obtain ⟨-, -, hcnt⟩ := counts_at hpre (L := L) hc'.ne_entry hl'
    have hpoll := (hcnt (stageOf t)).1
    have htile : pos'.tile = t := by
      cases pos' <;> first | exact False.elim hc' | exact hc'.1
    have hpd : pos'.polled = 1 := by
      cases pos' <;> first | exact False.elim hc' | rfl
    rw [htile, hpd] at hpoll
    refine ⟨rfl, (rdAcc_loc hpre t row c m).2, ?_⟩
    show okPolls ((Bar.storeFull (stageOf t)).loc L (g / L.block)) _ = _
    rw [hpoll]
    simp only [uses, stageOf_val]
    omega
  · intro i pc a bs he
    rw [Nat.add_assoc] at he
    obtain ⟨s', pos', hσ', hr', hl', hc'⟩ := chunk_fwd hpre hX hg hσ hr hl hch (4 + i.val)
      (by have := i.isLt; omega) he (fun _ _ h => by cases h)
    obtain rfl := hc'.gst
    have hev := event_shape hpre hX hg he hσ' hr'
    obtain ⟨t2, r2, c2, j2, hpos, -, rfl, -⟩ := ev_wr_inv hev
    cases hpos
    exact ⟨rfl, ⟨8 * c + i.val, by have := i.isLt; omega⟩, rfl, rfl⟩

/-- **`StoreRef.chunk`**: at a state of the phase at the vector load, the thread is the store
leader of its block and there are a tile `t`, a live row `row` of it and a chunk `c` such that
the next four events, where they are reads, are the four 4-byte elements of the 16 bytes at
offset `16 row + 256 c` of output stage `t % 2`, each after `t / 2 + 1` successful polls of the
stage's "full" mbarrier, and the eight events after them, where they are writes, are the 2-byte
stores of the outputs of the channels `8 c` to `8 c + 7` of token `16 t + row`. -/
theorem storeRef_chunk {k : Nat} {d : D} (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hI : Inv P X g k d) (hs : d.site = .load 177) :
    g = storeLeader L (g / L.block) ∧
    ∃ t row c, row < 16 ∧ c < 16 ∧ 16 * t + row < P.length (Values.seqOf P L g) ∧
      (∀ m < 4, ∀ pc a bs, X.get (g, k + m) = some ⟨pc, .rd a bs⟩ → a.size = 4 ∧
        a.loc = ⟨.shared, g / L.block,
          L.sharedBase + (86912 + 4096 * (t % 2) + (16 * row + 256 * c + 4 * m))⟩ ∧
        okPolls (Values.Ends.storeFullBar L g t) ((X.tr g).take (k + m)) = t / 2 + 1) ∧
      ∀ i : Fin 8, ∀ pc a bs, X.get (g, k + 4 + i.val) = some ⟨pc, .wr a bs⟩ → a.size = 2 ∧
        ∃ v : Fin 128, v.val = 8 * c + i.val ∧
          a.loc = P.outLoc (Values.seqOf P L g) (Values.headOf P L g) (16 * t + row) v := by
  obtain ⟨pos, hr, hl⟩ := hI
  obtain ⟨t, row, c, rfl⟩ := pos_of_load (hr.site.symm.trans hs)
  have hp : Pos.ld0 t row c ≠ .entry := by intro h; cases h
  obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
  obtain ⟨h1, h2⟩ := chunk_at hpre hX hg hσ hr hl
  refine ⟨leader_at hpre hr hp, t, row, c, by omega, hc, ?_, h1, h2⟩
  rw [seqOf_values hpre]
  omega

end

/-! ### For the assembly of the value-ends contracts -/

/-- **The index of an element read of the vector load**, by site: 0 at the load site 177, and
1, 2, 3 at its three continuation sites, which carry the values already read; none at every
other site. (The same function as `Ref/Assembly/ValuesEndsRef.lean: ValuesEnds.readIdx`.) -/
def rdIdx : Site → Option Nat
  | .load j => if j.val = 177 then some 0 else none
  | .loadEl1 _ _ => some 1
  | .loadEl2 _ _ _ => some 2
  | .loadEl3 _ _ _ _ => some 3
  | _ => none

/-- A position whose site is the `m`-th element read is the `m`-th position of a chunk. -/
theorem inChunk_of_rdIdx {pos : Pos} {m : Nat} (h : rdIdx pos.site = some m) :
    ∃ t row c, InChunk t row c m pos ∧ m < 4 := by
  cases pos with
  | ld0 t row c =>
    have h0 : rdIdx (Pos.ld0 t row c).site = some 0 := rfl
    obtain rfl : 0 = m := Option.some.inj (h0.symm.trans h)
    exact ⟨t, row, c, ⟨rfl, rfl, rfl, rfl⟩, by decide⟩
  | ld1 t row c v0 =>
    obtain rfl : 1 = m := Option.some.inj h
    exact ⟨t, row, c, ⟨rfl, rfl, rfl, rfl⟩, by decide⟩
  | ld2 t row c v0 v1 =>
    obtain rfl : 2 = m := Option.some.inj h
    exact ⟨t, row, c, ⟨rfl, rfl, rfl, rfl⟩, by decide⟩
  | ld3 t row c v0 v1 v2 =>
    obtain rfl : 3 = m := Option.some.inj h
    exact ⟨t, row, c, ⟨rfl, rfl, rfl, rfl⟩, by decide⟩
  | _ => cases h

/-- A state determines the chunk of its vector load: the tile, the row and the chunk are read
off the registers `%r1806`, `%r1809`, `%r1811`. -/
theorem ld0_inj (hpre : Pre P L mem0) {t row c t' row' c' : Nat} {d : D}
    (h : RefAt P g (.ld0 t row c) d) (h' : RefAt P g (.ld0 t' row' c') d) :
    t = t' ∧ row = row' ∧ c = c' := by
  have e1 := tile_reg hpre h (by intro h; cases h)
  have e2 := tile_reg hpre h' (by intro h; cases h)
  simp only [Pos.tile] at e1 e2
  obtain ⟨hpart, hrow, hc, k2115, -, k2117, -⟩ := h.pos.2
  obtain ⟨hpart', hrow', hc', k2115', -, k2117', -⟩ := h'.pos.2
  have r1 := congrArg BitVec.toNat (k2115.symm.trans k2115')
  have r2 := congrArg BitVec.toNat (k2117.symm.trans k2117')
  rw [toNat_W (by omega), toNat_W (by omega)] at r1 r2
  refine ⟨e1.symm.trans e2, r1, by omega⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **Field `chunk` of `ValuesEnds.StoreOwes`** (`StoreRef.chunk`, verbatim): for a followed
state at the vector load of which the weak invariant is known (it is at a position of the phase
with the position's register facts, or it is the exit state), and the invariant when no
undefined-behaviour event precedes the position. No event at the position is assumed. -/
theorem owes_chunk {k0 k : Nat} {s : D} (hen : Entered P L X g k0) (hk0 : k0 ≤ k)
    (hk : k ≤ (X.tr g).length) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hw : (∃ pos, RefAt P g pos s) ∨ Exit P g s)
    (hinv : (∀ i < k, ∀ pc f, X.get (g, i) ≠ some ⟨pc, .ub f⟩) → Inv P X g k s)
    (hs : s.site = .load 177) :
    g = storeLeader L (g / L.block) ∧
    ∃ t row c, row < 16 ∧ c < 16 ∧ 16 * t + row < P.length (Values.seqOf P L g) ∧
      (∀ m < 4, ∀ pc a bs, X.get (g, k + m) = some ⟨pc, .rd a bs⟩ → a.size = 4 ∧
        a.loc = ⟨.shared, g / L.block,
          L.sharedBase + (86912 + 4096 * (t % 2) + (16 * row + 256 * c + 4 * m))⟩ ∧
        okPolls (Values.Ends.storeFullBar L g t) ((X.tr g).take (k + m)) = t / 2 + 1) ∧
      ∀ i : Fin 8, ∀ pc a bs, X.get (g, k + 4 + i.val) = some ⟨pc, .wr a bs⟩ → a.size = 2 ∧
        ∃ v : Fin 128, v.val = 8 * c + i.val ∧
          a.loc = P.outLoc (Values.seqOf P L g) (Values.headOf P L g) (16 * t + row) v := by
  obtain ⟨pos, hr⟩ : ∃ pos, RefAt P g pos s := by
    rcases hw with h | h
    · exact h
    · rw [h.site] at hs
      cases hs
  obtain ⟨t, row, c, rfl⟩ := pos_of_load (hr.site.symm.trans hs)
  have hp : Pos.ld0 t row c ≠ .entry := by intro h; cases h
  obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
  -- with an event at or after the position, the invariant holds at the position
  have hled : ∀ {j : Nat} {e : Event}, k ≤ j → X.get (g, j) = some e →
      ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) (.ld0 t row c) := by
    intro j e hkj he
    obtain ⟨pos', hr', hl'⟩ := hinv fun i hi pc f h => by
      have := ub_last hX h he
      omega
    obtain ⟨t', row', c', rfl⟩ := pos_of_load (hr'.site.symm.trans hs)
    obtain ⟨rfl, rfl, rfl⟩ := ld0_inj hpre hr hr'
    exact hl'
  refine ⟨leader_at hpre hr hp, t, row, c, by omega, hc, ?_, ?_, ?_⟩
  · rw [seqOf_values hpre]
    omega
  · intro m hm pc a bs he
    exact (chunk_at hpre hX hg hσ hr (hled (Nat.le_add_right k m) he)).1 m hm pc a bs he
  · intro i pc a bs he
    exact (chunk_at hpre hX hg hσ hr (hled (by omega) he)).2 i pc a bs he

/-- **Field `reads` of `ValuesEnds.StoreOwes`**: a state of the phase at the `m`-th element
read of the vector load, with an event, is `m` events after a followed state at the first one
(the site `load 177`), and the events from there up to this one are reads. -/
theorem owes_reads {k0 k m : Nat} {s : D} {e : Event} (hen : Entered P L X g k0)
    (hk0 : k0 ≤ k) (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (hm : rdIdx s.site = some m) (he : X.get (g, k) = some e) :
    m ≤ k ∧ (∃ d0, Frame.stateAt (code L) X g (k - m) = some (some d0) ∧ d0.site = .load 177) ∧
      ∀ n ≤ m, ∃ pc a bs, X.get (g, k - m + n) = some ⟨pc, .rd a bs⟩ := by
  obtain ⟨pos, hr, hl⟩ := hI
  rw [hr.site] at hm
  obtain ⟨t, row, c, hc, hm4⟩ := inChunk_of_rdIdx hm
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨h1, -, d0, hσ0, hr0, hl0⟩ := chunk_back hpre hX hg hen hk0 hk hσ hr hl hc
  -- the event at the position is the read of element `m`
  obtain ⟨bs, -, rfl⟩ := rd_event hpre hX hg hσ hr hc hm4 he
  refine ⟨h1, ⟨d0, hσ0, hr0.site⟩, fun n hn => ?_⟩
  rcases Nat.eq_or_lt_of_le hn with rfl | hlt
  · rw [Nat.sub_add_cancel h1]
    exact ⟨_, _, _, he⟩
  · obtain ⟨en, hen'⟩ : ∃ en, X.get (g, k - m + n) = some en :=
      ⟨_, List.getElem?_eq_getElem (show k - m + n < (X.tr g).length by omega)⟩
    have hub : ∀ pc f, en ≠ ⟨pc, .ub f⟩ := by
      rintro pc f rfl
      have := ub_last hX hen' he
      omega
    obtain ⟨s', pos', hσ', hr', -, hc'⟩ := chunk_fwd hpre hX hg hσ0 hr0 hl0
      (t := t) (row := row) (c := c) ⟨rfl, rfl, rfl, rfl⟩ n (by omega) hen' hub
    obtain ⟨bs', -, rfl⟩ := rd_event hpre hX hg hσ' hr' hc' (by omega) hen'
    exact ⟨_, _, _, hen'⟩

/-- **Field `acc_free` of `ValuesEnds.StoreOwes`**: no access of the phase covers a byte of the
bfloat16 state copy `state_acc` (window offsets below 32768): the element reads are in the
output buffers (from offset 86912), the element stores in global memory. -/
theorem owes_acc_free {k c : Nat} {s : D} {a : Acc} {w : Bool} {l : Loc}
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (hacc : X.Access (g, k) a w) (hcov : a.Covers l) : ¬ Protocol.InStateAcc L c l := by
  intro hin
  obtain ⟨e, he, ha⟩ := Frame.intent_issuer (ref := .thread (g, k)) hacc
  have ht := touch_store hpre hX hg he hσ hI ha
  have hsh : a.loc.space = .shared := hcov.1.symm.trans hin.1
  obtain ⟨-, h2, -⟩ := shared_touch hpre (L := L) ht hsh
  have h3 := hcov.2.2.1
  have h4 := hin.2.2.2
  have hsb := hpre.sharedBase
  omega

/-- **Field `ts_out` of `ValuesEnds.StoreOwes`**: no tensor store of the phase writes a byte of
the final state: it writes bytes of the output array, which the precondition keeps apart from
the final-state array. -/
theorem owes_ts_out {k pc al x y z : Nat} {sp : TensorStore.Spec} {l : Loc} {s : D}
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hwl : TensorStore.writeLoc sp x y z = some l) : ¬ P.StateByte l := by
  intro hst
  have ht : Touch P g { loc := l, size := 1 } := by
    refine touch_store hpre hX hg he hσ hI (.inr ?_)
    exact ⟨rfl, x, y, z, .inr hwl⟩
  obtain ⟨tok, htok, v, zz, hz, hl⟩ := global_touch hpre hg ht ⟨rfl, rfl, Nat.le_refl _,
    Nat.lt_succ_self _⟩ (Execution.store_writeLoc_global hwl)
  have ho : P.OutputByte l :=
    ⟨seqOf P g, seqOf_lt hpre g, headOf P g, headOf_lt hpre hg, tok, htok, v, zz, hz, hl⟩
  obtain ⟨k1, hk1, e1⟩ := Top.outputByte_range ho
  obtain ⟨k2, hk2, e2⟩ := Top.stateByte_range hst
  have hap := hpre.outputApartFinal
  rw [e1] at e2
  simp only [Loc.mk.injEq, true_and] at e2
  unfold Apart at hap
  omega

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
