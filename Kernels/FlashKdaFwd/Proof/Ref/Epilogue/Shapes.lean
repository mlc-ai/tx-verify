-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Arith
public import Kernels.FlashKdaFwd.Proof.Ref.TensorStore
public import Kernels.FlashKdaFwd.Proof.Ref.ParamBridge
public import Kernels.FlashKdaFwd.Flow.Code
public import Lemmas.Flow.Step.ShapeClasses

@[expose] public section

/-! # Epilogue phase: the events, in closed form

What a thread fires at each position of the epilogue, from the reference invariant at the
position (`RefAt`), the concrete state (`Code.AtD`: the registers hold the values of the
machine's file) and the firing fact of the site's instruction.

* `EvX P L g pos x e`: **the exact event of a position** for a state with the opaque slots `x`.
  For every position but a store it is `Ev` (`Inv.lean`), which has no undefined-behaviour
  alternative: the barriers, the fence, the commit, the wait and `ret` have no operand, and a
  tensor store is the issue of `finalSpec` by `Ref/TensorStore.lean: tensorStore_event` (the map
  is the launch's map of the final state, the source address a multiple of 128, the box
  aligned). For store `j` it says what is written: with `v = x (stSrc j)` the value of the
  carry register, the event is the write of the four bytes of `storeValue 32 v` at `stAddr`, or
  the undefined-behaviour event with the fault of `storeValue 32 v` when the value cannot be
  stored in 32 bits (a value of fewer than four bytes, or a wider one without a bit pattern).
  This is the only data condition of the phase; the value layer discharges it (the carry
  registers hold FP32 payloads).
* `EvX.ev`: an exact event that is not undefined behaviour is the closed-form event `Ev`;
  `EvX.noUb`: an exact event is not undefined behaviour when the stored value is storable.
* The generic lemmas of the two families, which the generated file `Sites.lean` instantiates per
  site: `ev_st` (a store, with the address register and the source register of the site) and
  `ev_ts` (a tensor store, with its source and first-coordinate registers); and `ev_plain` for
  the seven other positions.

How a store is evaluated (`ev_store`): the instruction is a weak `st.b32` with generic
addressing; its address register holds a generic pointer into the thread's own window (the
invariant), which Core resolves to the byte of that window (`accessLoc`, a launched thread of a
block of the grid); the address is a multiple of 4 (`stAddr_bounds`), so the footprint is the
four bytes there (`st_acc`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {site : Site}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-! ### The exact event -/

/-- The footprint of store `j` of compute thread `g`: four bytes at `stAddr`. -/
abbrev stAcc (P : Params) (L : Launch) (g j : Nat) : Acc :=
  { loc := ⟨.shared, g / L.block, stAddr P g j⟩, size := 4 }

/-- **The exact event of a position**, given the opaque slots of the state. -/
def EvX (P : Params) (L : Launch) (g : Nat) (pos : Pos) (x : Nat → Value) (e : Event) : Prop :=
  match pos with
  | .st j =>
    (∃ v, storeValue 32 (x (stSrc j.val)) = .ok v ∧
      e = ⟨(Pos.st j).site.pc, .wr (stAcc P L g j.val) v.toBytes⟩) ∨
    ∃ f, storeValue 32 (x (stSrc j.val)) = .error f ∧ e = ⟨(Pos.st j).site.pc, .ub f⟩
  | pos => Ev P L g pos e

/-- An exact event that is not undefined behaviour is the closed-form event. -/
theorem EvX.ev {pos : Pos} (h : EvX P L g pos x e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    Ev P L g pos e := by
  cases pos with
  | st j =>
    rcases h with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩
    · exact ⟨_, rfl⟩
    · exact absurd rfl (hub _ f)
  | _ => exact h

/-- **No closed-form event of the phase is undefined behaviour.** -/
theorem Ev.noUb {pos : Pos} (h : Ev P L g pos e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  rintro pc f rfl
  cases pos <;>
    simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
      false_and] at h

/-- **The event of a position is not undefined behaviour** when, at a store, the carry
register holds a value that a 32-bit store can write. -/
theorem EvX.noUb {pos : Pos} (h : EvX P L g pos x e)
    (hv : ∀ j, pos = .st j → ∃ v, storeValue 32 (x (stSrc j.val)) = .ok v) :
    ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  cases pos with
  | st j =>
    obtain ⟨v, hv⟩ := hv j rfl
    rcases h with ⟨v', -, rfl⟩ | ⟨f, hf, -⟩
    · intro pc f h'
      cases h'
    · rw [hv] at hf
      cases hf
  | _ =>
    simp only [EvX] at h
    exact Ev.noUb h

/-! ### A store through a generic pointer into the thread's own window -/

/-- The memory access of a store of the epilogue: `st.b32 [r], src` with generic addressing. -/
def stAccess (r src : Nat) : MemAccess :=
  { kind := .store, space := none, sem := .weak, scope := none, elem := .int .b 32, vec := 1,
    ext := .same, nc := false, noftz := false,
    hints := { cop := none, l1 := none, l2 := none, prefetch := none, policy := none },
    addr := { base := .reg r 64, off := 0 }, dsts := [], srcs := [.reg src], mmio := false }

/-- An opaque register that is live at a state's site holds its slot. -/
theorem reg_x {d : D} (hat : (code L g).AtD d t) {r : Nat}
    (hr : r ∈ Flow.live d.site.pc) (hk : isOpaque r = true) : t.regs r = some (d.x r) := by
  have h := regs_of_factsFrom hat.2.2.2.2 hr
  rw [h, valueOf_opaque hk]

/-- **The footprint of a store** whose address register holds the generic pointer to byte `a`
of the thread's own window, `a` a multiple of 4: the four bytes at `a`. -/
theorem st_acc (hpre : Pre P L mem0) (hg : g < L.threads) {r src a : Nat}
    (hr : t.regs r = some (.ptr 64 true (.shared (g / L.block) (g / L.block)) (W a)))
    (ha : a < 2 ^ 32) (ha4 : a % 4 = 0) (hsub : t.sub = 0) :
    accessAcc L g t (stAccess r src) = .ok { loc := ⟨.shared, g / L.block, a⟩, size := 4 } := by
  have hc : g / L.block < L.grid := by
    rw [block_div hpre, hpre.grid]
    exact cta_lt hpre hg
  have hn : (W a).toNat = a := toNat_W (by omega)
  have ha' : a < 4294967296 := ha
  simp [accessAcc, accessLoc, stAccess, readReg, hr, readSharedAddress, readValue, bind,
    Except.bind, pure, Except.pure, hg, hc, hn, ha', elemAcc, ha4, hsub, MemAccess.strongLocOk,
    MemAccess.semAcc, DType.width, Loc.at, Functor.map, Except.map]

/-- **The exact event of a store** through the generic pointer to byte `a` of the block's own
window, from the value `v` of the source register: the write of the four bytes of the value as
a 32-bit store writes it, or undefined behaviour when the value cannot be stored in 32 bits. -/
theorem ev_store (hpre : Pre P L mem0) (hg : g < L.threads) {pc r src a : Nat} {v : Value}
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.mem (stAccess r src))) e o)
    (hr : t.regs r = some (.ptr 64 true (.shared (g / L.block) (g / L.block)) (W a)))
    (hv : t.regs src = some v) (ha : a < 2 ^ 32) (ha4 : a % 4 = 0) (hsub : t.sub = 0) :
    (∃ v', storeValue 32 v = .ok v' ∧
      e = ⟨pc, .wr { loc := ⟨.shared, g / L.block, a⟩, size := 4 } v'.toBytes⟩) ∨
    ∃ f, storeValue 32 v = .error f ∧ e = ⟨pc, .ub f⟩ := by
  have hacc := st_acc hpre hg (src := src) hr ha ha4 hsub
  have hE : eventTmpl Assumptions.all L g t (.mem (stAccess r src)) =
      accessTmpl Assumptions.all L g t (stAccess r src) := rfl
  rw [hE] at hf
  have hrv : readValue L g t 32 (.reg src) = .ok v := by
    simp [readValue, readReg, hv, pure, Except.pure]
  have hsrc : (stAccess r src).srcs[t.sub]? = some (.reg src) := by rw [hsub]; rfl
  simp only [accessTmpl, show (stAccess r src).kind = .store from rfl, hacc, hsrc,
    show (stAccess r src).elem.width = 32 from rfl, hrv, bind, Except.bind] at hf
  cases hsv : storeValue 32 v with
  | error f =>
    rw [hsv] at hf
    exact .inr ⟨f, rfl, hf.1⟩
  | ok v' =>
    rw [hsv] at hf
    exact .inl ⟨v', rfl, hf.1⟩

/-- **The event of store `j`**, at its site: `r` and `src` are the address register and the
source register of the site's instruction (`stPtr j`, `stSrc j`). -/
theorem ev_st (hpre : Pre P L mem0) (hg : g < L.threads) {j : Fin 128} {r src : Nat}
    (hf : Fires (Pos.st j).site.pc (eventTmpl Assumptions.all L g t (.mem (stAccess r src))) e o)
    (hat : (code L g).AtD ⟨site, w, p, x⟩ t) (hr : r ∈ Flow.live site.pc)
    (hs : src ∈ Flow.live site.pc) (er : stPtr j.val = r) (es : stSrc j.val = src)
    (h : RefAt P g (.st j) ⟨site, w, p, x⟩) : EvX P L g (.st j) x e := by
  subst er es
  obtain ⟨hsite, ht, -, -, hp⟩ := h
  dsimp only at hsite
  subst hsite
  have hb := stAddr_bounds hpre ht j
  have hs' := shared_lt hpre
  have r1 := reg_x hat hr (stPtr_opaque j)
  have r2 := reg_x hat hs (stSrc_opaque j)
  dsimp only at r1 r2 hp
  rw [hp, ownPtr, ← block_div hpre] at r1
  exact ev_store hpre hg hf r1 r2 (by omega) hb.1 hat.2.1

/-! ### A tensor store of the final state -/

/-- The specification of the `i`-th tensor store is `storeSpec` of `Ref/TensorStore.lean`. -/
theorem finalSpec_eq (P : Params) (L : Launch) (g i : Nat) :
    finalSpec P L g i = storeSpec P (g / L.block) 9
      [8 * i, 0, P.heads * seqOf P g + headOf P g] (P.sharedBase + (32768 + 4096 * i)) := rfl

/-- **The event of tensor store `i`**, at its site: `src` and `rc` are the registers of the
shared source address and of the first coordinate of the site's instruction. It is the issue of
`finalSpec`, never undefined behaviour. -/
theorem ev_ts (hpre : Pre P L mem0) (hg : g < L.threads) {i : Fin 16} {pc src rc : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensorStore (.reg 3410) [.reg rc, .reg 2055, .reg 2056] src 0 none .tile none)) e o)
    (hat : (code L g).AtD ⟨site, w, p, x⟩ t) (h3410 : 3410 ∈ Flow.live site.pc)
    (hsrc : src ∈ Flow.live site.pc) (hrc : rc ∈ Flow.live site.pc)
    (h2055 : 2055 ∈ Flow.live site.pc) (h2056 : 2056 ∈ Flow.live site.pc)
    (ks : kind src = .word 32) (kc : kind rc = .word 32)
    (es : tsSrc i.val = src) (ec : tsCoord i.val = rc)
    (h : RefAt P g (.ts i) ⟨site, w, p, x⟩) :
    e = ⟨pc, .tensorStore (P.objectBase 9) (finalSpec P L g i.val)⟩ := by
  subst es ec
  obtain ⟨-, -, -, h0, hpl, hs, hc⟩ := h
  have hsh := shared_lt hpre
  have ha := hpre.sharedAlignment
  have hp := plane_lt hpre hg
  have hr := hpre.planesRange
  have hi := i.isLt
  have rm := reg_g hat (r := 3410) h3410 (i := 9) rfl
  have r1 := reg_w hat hsrc (n := 32) ks
  have r2 := reg_w hat hrc (n := 32) kc
  have r3 := reg_w hat (r := 2055) h2055 (n := 32) rfl
  have r4 := reg_w hat (r := 2056) h2056 (n := 32) rfl
  dsimp only at r1 r2 r3 r4 h0 hpl hs hc
  rw [hs] at r1
  rw [hc] at r2
  rw [h0] at r3
  rw [hpl] at r4
  rw [finalSpec_eq]
  exact (tensorStore_event hpre (i := 9) paramName_9 (rs := [tsCoord i.val, 2055, 2056])
    (vs := [8 * i.val, 0, P.heads * seqOf P g + headOf P g]) hf rm r1 (by omega) (by omega)
    (.cons ⟨r2, by omega⟩ (.cons ⟨r3, by omega⟩ (.cons ⟨r4, by omega⟩ .nil))) rfl
    (show 8 * i.val * 4 % 16 = 0 by omega)).1

/-! ### The positions without a table -/

/-- No assumption of the kernel changes a proxy fence. -/
theorem ev_fence (hf : Fires 3774 (eventTmpl Assumptions.all L g t
      (.fence (.proxy (.async (some (.shared .cta))) none none))) e o) :
    e = ⟨3774, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  simp only [eventTmpl, fenceTmpl, Fires] at hf
  exact hf.1

/-- **The event at a position that is neither a store nor a tensor store.** -/
theorem ev_plain (pos : Pos) (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : ∀ j, pos ≠ .st j) (hts : ∀ i, pos ≠ .ts i) : Ev P L g pos e := by
  cases pos with
  | st j => exact absurd rfl (hs j)
  | ts i => exact absurd rfl (hts i)
  | bar7 =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_barSync (P := fun e => e = ⟨_, .bar 0 none .sync⟩) hf (by decide) rfl
  | bar8 =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_barSync (P := fun e => e = ⟨_, .bar 0 none .sync⟩) hf (by decide) rfl
  | bar9 =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_barSync (P := fun e => e = ⟨_, .bar 0 none .sync⟩) hf (by decide) rfl
  | fence =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact ev_fence hf
  | commit =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_bulkCommit (L := L) (g := g) (P := fun e => e = ⟨_, .bulkCommit⟩) hf rfl
  | bwait =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_bulkWait (L := L) (g := g) (P := fun e => e = ⟨_, .bulkWait .read 0⟩) hf rfl
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_exit (P := fun e => e = ⟨_, .exit⟩) hf rfl

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
