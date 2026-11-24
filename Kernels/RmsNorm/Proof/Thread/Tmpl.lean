-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Sites
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.Events
public import Lemmas.Flow.Vector
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # The event of each site

At a concrete state of an abstract state, the instruction of its site performs: element `sub` of
a vector access (four bytes at `4 * sub` from the vector's aligned address), a scalar shared
access, a shuffle of the operand register with the round's lane offset, a barrier of the whole
CTA, or the exit. The addresses come from the register facts and the launch's bounds. A store
element writes its source's own bytes, truncates a wider source to them, and faults on a
narrower one (`storeValue`). -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}

/-- The shared location `a` of the thread's CTA. -/
abbrev sh (g a : Nat) : Loc := ⟨.shared, g / 256, a⟩

/-- The value of register `r` of a state with the facts of `d` at `pc`, when `r` is live there. -/
theorem reg_of {pc r : Nat} (h : Holds t.regs (factsAt P g pc d)) (hr : r ∈ Flow.live pc) :
    t.regs r = some (valueOf P g d r) :=
  holds_mem h (mem_factsFrom hr)

theorem row_bound {i : Nat} (hi : row g i < P.Bt) :
    off g i + 4096 + 16 ≤ 8192 * P.Bt := by
  have := Nat.mod_lt g (show 0 < 256 by decide)
  unfold off row at *
  omega

theorem tid_lt (g : Nat) : g % 256 < 256 := Nat.mod_lt _ (by decide)

/-- An input element of a row: tile 0 at `0`, tile 1 at `4096` bytes further. -/
theorem tmpl_ldx (hpre : Pre P L mem0) {base k d0 d1 d2 d3 : Nat}
    (hk : k = 0 ∨ k = 4096) (hi : row g d.i < P.Bt) (hr : t.regs base = some
      (b64 (P.I + off g d.i + k))) :
    eventTmpl Prod L g t (.mem
      { kind := .load, space := some .global, sem := .weak,
        elem := .int .b 32, vec := 4, addr := ⟨.reg base 64, 0⟩,
        dsts := [some d0, some d1, some d2, some d3] }) =
      .read { loc := gl (P.I + off g d.i + k + 4 * t.sub), size := 4, elem := t.sub }
        (afterLoad t [d0, d1, d2, d3]) := by
  have hb := row_bound hi
  have he := hpre.hyp.inEnd
  have ha := hpre.hyp.inAlign
  rw [eventTmpl, memTmpl_load (sp := .global) (base := base) (w := 64) (by rfl) (by rfl) (by rfl)
    (by rfl) (by simp)]
  change loadTmpl Prod L g t .global false 32 [d0, d1, d2, d3] base 0 = _
  rw [loadTmpl_v4 (Proof.effAddr_global hr (by omega)) (by simp only; unfold off at *; omega) rfl]
  rfl

/-- A weight element: tile 0 at `0`, tile 1 at `4096` bytes further. -/
theorem tmpl_ldw (hpre : Pre P L mem0) {base k d0 d1 d2 d3 : Nat}
    (hk : k = 0 ∨ k = 4096) (hr : t.regs base = some (b64 (P.W + 16 * (g % 256) + k))) :
    eventTmpl Prod L g t (.mem
      { kind := .load, space := some .global, sem := .weak,
        elem := .int .b 32, vec := 4, addr := ⟨.reg base 64, 0⟩,
        dsts := [some d0, some d1, some d2, some d3] }) =
      .read { loc := gl (P.W + 16 * (g % 256) + k + 4 * t.sub), size := 4, elem := t.sub }
        (afterLoad t [d0, d1, d2, d3]) := by
  have he := hpre.hyp.wEnd
  have ha := hpre.hyp.wAlign
  have := tid_lt g
  rw [eventTmpl, memTmpl_load (sp := .global) (base := base) (w := 64) (by rfl) (by rfl) (by rfl)
    (by rfl) (by simp)]
  change loadTmpl Prod L g t .global false 32 [d0, d1, d2, d3] base 0 = _
  rw [loadTmpl_v4 (Proof.effAddr_global hr (by omega)) (by simp only; omega) rfl]
  rfl

/-- A staged input element of the thread's shared slot. -/
theorem tmpl_lds (hpre : Pre P L mem0) {base k d0 d1 d2 d3 : Nat}
    (hk : k = 0 ∨ k = 16 ∨ k = 8192 ∨ k = 8208) (hr : t.regs base = some
      (b32 (P.S + 32 * (g % 256) + k))) :
    eventTmpl Prod L g t (.mem
      { kind := .load, space := some (.shared .cta), sem := .weak,
        elem := .float .f32, vec := 4, addr := ⟨.reg base 32, 0⟩,
        dsts := [some d0, some d1, some d2, some d3] }) =
      .read { loc := sh g (P.S + 32 * (g % 256) + k + 4 * t.sub), size := 4, elem := t.sub }
        (afterLoad t [d0, d1, d2, d3]) := by
  have he := hpre.hyp.sharedEnd
  have ha := hpre.hyp.sharedAlign
  have hB := hpre.hyp.block
  have := tid_lt g
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := base) (w := 32) (by rfl) (by rfl) (by rfl)
    (by rfl) (by simp)]
  change loadTmpl Prod L g t .shared false 32 [d0, d1, d2, d3] base 0 = _
  rw [loadTmpl_v4 (effAddr_b32 hr (by omega)) (by simp only; omega) rfl]
  simp [Loc.at, hB]

/-- A store element of the thread's shared slot. -/
theorem tmpl_sts (hpre : Pre P L mem0) {base k r : Nat} {srcs : List Opnd} {v : Value}
    (hsrc : srcs.length = 4) (hk : k = 0 ∨ k = 16 ∨ k = 8192 ∨ k = 8208)
    (hr : t.regs base = some (b32 (P.S + 32 * (g % 256) + k))) (hs : srcs[t.sub]? = some (.reg r))
    (hv : t.regs r = some v) :
    eventTmpl Prod L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak,
        elem := .float .f32, vec := 4, addr := ⟨.reg base 32, 0⟩, srcs  }) =
      match storeValue 32 v with
      | .error f => .ub f
      | .ok v' =>
        .write { loc := sh g (P.S + 32 * (g % 256) + k + 4 * t.sub), size := 4, elem := t.sub }
          v'.toBytes (afterStore t srcs) := by
  have he := hpre.hyp.sharedEnd
  have ha := hpre.hyp.sharedAlign
  have hB := hpre.hyp.block
  have := tid_lt g
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32)
    (by simp [MemAccess.rule, memTypeOk, DType.width, hsrc])
    (by rfl) (by rfl) (by rfl) (by simp)]
  change storeTmpl L g t .shared 32 base 0 srcs = _
  rw [storeTmpl_v4 (effAddr_b32 hr (by omega)) (by simp only; omega) hsrc hs hv]
  cases storeValue 32 v <;> simp [Loc.at, hB]

/-- An output element of a row: tile 0 at `0`, tile 1 at `4096` bytes further. -/
theorem tmpl_sto (hpre : Pre P L mem0) {base k r : Nat} {srcs : List Opnd} {v : Value}
    (hsrc : srcs.length = 4) (hk : k = 0 ∨ k = 4096) (hi : row g d.i < P.Bt)
    (hr : t.regs base = some (b64 (P.O + off g d.i + k))) (hs : srcs[t.sub]? = some (.reg r))
    (hv : t.regs r = some v) :
    eventTmpl Prod L g t (.mem
      { kind := .store, space := some .global, sem := .weak,
        elem := .int .b 32, vec := 4, addr := ⟨.reg base 64, 0⟩, srcs  }) =
      match storeValue 32 v with
      | .error f => .ub f
      | .ok v' =>
        .write { loc := gl (P.O + off g d.i + k + 4 * t.sub), size := 4, elem := t.sub }
          v'.toBytes (afterStore t srcs) := by
  have hb := row_bound hi
  have he := hpre.hyp.outEnd
  have ha := hpre.hyp.outAlign
  rw [eventTmpl, memTmpl_store (sp := .global) (base := base) (w := 64)
    (by simp [MemAccess.rule, memTypeOk, DType.width, hsrc])
    (by rfl) (by rfl) (by rfl) (by simp)]
  change storeTmpl L g t .global 32 base 0 srcs = _
  rw [storeTmpl_v4 (Proof.effAddr_global hr (by omega))
    (by simp only; unfold off at *; omega) hsrc hs hv]
  cases storeValue 32 v <;> rfl

/-- A scalar shared load. -/
theorem tmpl_ld1 (hpre : Pre P L mem0) {base a dst : Nat} (hs : t.sub = 0)
    (ha : a + 4 ≤ P.S + 16416)
    (hal : a % 4 = 0) (hr : t.regs base = some (b32 a)) :
    eventTmpl Prod L g t (.mem
      { kind := .load, space := some (.shared .cta), sem := .weak,
        elem := .float .f32, addr := ⟨.reg base 32, 0⟩, dsts := [some dst]  }) =
      .read { loc := sh g a, size := 4 } (afterLoad t [dst]) := by
  have he := hpre.hyp.sharedEnd
  have hB := hpre.hyp.block
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := base) (w := 32) (by rfl) (by rfl) (by rfl)
    (by rfl) (by simp)]
  change loadTmpl Prod L g t .shared false 32 [dst] base 0 = _
  unfold loadTmpl
  rw [effAddr_b32 hr (by omega)]
  simp only [bind, Except.bind, List.length_singleton, hs]
  rw [elemAcc_ok (by decide) (by simpa using hal)]
  simp [Loc.at, hB]

/-- A scalar shared store. -/
theorem tmpl_st1 (hpre : Pre P L mem0) {base a src : Nat} {v : Value} (hs : t.sub = 0)
    (ha : a + 4 ≤ P.S + 16416) (hal : a % 4 = 0) (hr : t.regs base = some (b32 a))
    (hv : t.regs src = some v) :
    eventTmpl Prod L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak,
        elem := .float .f32, addr := ⟨.reg base 32, 0⟩, srcs := [.reg src]  }) =
      match storeValue 32 v with
      | .error f => .ub f
      | .ok v' => .write { loc := sh g a, size := 4 } v'.toBytes (afterStore t [.reg src]) := by
  have he := hpre.hyp.sharedEnd
  have hB := hpre.hyp.block
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) (by rfl) (by rfl) (by rfl)
    (by rfl) (by simp)]
  change storeTmpl L g t .shared 32 base 0 [.reg src] = _
  unfold storeTmpl
  rw [effAddr_b32 hr (by omega)]
  simp only [bind, Except.bind, List.length_singleton, hs]
  rw [elemAcc_ok (by decide) (by simpa using hal)]
  simp only [Loc.at, readValue, readReg, hv, pure, Except.pure, sh, hB,
    List.getElem?_cons_zero]
  cases storeValue 32 v <;> rfl

/-- A full-mask shuffle of a four-byte operand with the lane operand `b` and clamp `31`. -/
theorem tmpl_shfl (hpre : Pre P L mem0) {dst a rb rc rm b : Nat}
    {va : Value} (ha : t.regs a = some va) (hva : va.bytes = 4)
    (hb : t.regs rb = some (b32 b)) (hb32 : b < 2 ^ 32) (hc : t.regs rc = some (b32 31))
    (hm : t.regs rm = some (b32 4294967295)) :
    eventTmpl Prod L g t (.warp
      { kind := .shfl .bfly, ty := some (.int .b 32), dsts := [some dst],
        srcs := [.reg a, .reg rb, .reg rc], mask := some (.reg rm)  }) =
      .shfl .bfly va b 31 (fun recv _ => PTX.next (setReg t dst recv)) := by
  have hB : L.block % 32 = 0 := by rw [hpre.hyp.block]
  have hb' : (truncBits 32 (BitVec.ofNat 64 b)).toNat = b := by
    rw [truncBits_ofNat hb32 (by decide), toNat_ofNat_lt (by omega)]
  simp only [eventTmpl, warpTmpl, WarpInstr.rule, shflTmpl, List.head?_nil, Option.join,
    readBits, readValue, readReg, ha, hb, hc, hm, b32, hva, hB, pure, Except.pure, bind,
    Except.bind, hb']
  rw [ite_eq_left (by decide), ite_eq_left trivial]
  rfl

/-- The warp index shuffle. -/
theorem tmpl_shfl0 (hpre : Pre P L mem0) (ha : t.regs 43 = some (b32 (g % 256 / 32))) :
    eventTmpl Prod L g t (.warp
      { kind := .shfl .idx, ty := some (.int .b 32),
        dsts := [some 46, some 1], srcs := [.reg 43, .imm 0, .imm 31],
        mask := some (.imm (-1)) }) =
      .shfl .idx (b32 (g % 256 / 32)) 0 31 (fun recv ok =>
        PTX.next (setReg (setReg t 46 recv) 1 (.pred ok))) := by
  have hB : L.block % 32 = 0 := by rw [hpre.hyp.block]
  simp only [eventTmpl, warpTmpl, WarpInstr.rule, shflTmpl, List.head?_cons, Option.join,
    readBits, readValue, readReg, ha, b32, Value.bytes, hB, pure, Except.pure]
  rw [ite_eq_left (by decide), ite_eq_left trivial,
    show (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 by decide,
    show (truncBits 32 (BitVec.ofInt 64 31)).toNat = 31 by decide]
  rfl

/-- A barrier of the whole CTA. -/
theorem tmpl_bar (hpre : Pre P L mem0) {ra rb id : Nat} (hid : id < 16)
    (ha : t.regs ra = some (b32 id)) (hb : t.regs rb = some (b32 256)) :
    eventTmpl Prod L g t (.barSyncN (.reg ra) (.reg rb) true) = .bar id (PTX.next t) none := by
  have hB := hpre.hyp.block
  have hid' : (truncBits 32 (BitVec.ofNat 64 id)).toNat = id := by
    rw [truncBits_ofNat (by omega) (by decide), toNat_ofNat_lt (by omega)]
  simp only [eventTmpl, barTmpl, readBits, readReg, ha, hb, b32, pure, Except.pure, bind,
    Except.bind, hid', hB]
  rw [show (truncBits 32 (BitVec.ofNat 64 256)).toNat = 256 by decide]
  simp [show ¬ 16 ≤ id by omega]

theorem tmpl_exit : eventTmpl Prod L g t .ret = .exit := rfl

end
end PTX.Kernels.RmsNorm.Proof
