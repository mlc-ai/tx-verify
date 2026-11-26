-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Next
public import Lemmas.Flow.Regs
public import Lemmas.Flow.TcTmpl

@[expose] public section

/-! # Warp matrix instructions in one thread: templates and fired events

A proof tool. `ldmatrix`, `stmatrix`, `movmatrix` and `mma.sync` (`Op.matrix`, Core's
`matrixTmpl`) seen from one lane of the warp, in the vocabulary a site machine uses.

Events a lane performs, in a CTA whose size is a multiple of 32 (otherwise `ub noRule`):

* `mma.sync` and `movmatrix`: one event `.matrix op own recv`. `own` are the bytes of the lane's
  source registers in operand order (`mmaOwn`, `regBytes`); the received bytes are rebuilt into
  the destination registers (`afterMatrix`) and the thread continues at the next instruction.
* `ldmatrix`, for a lane that supplies a row address (`laneOf L g < m.num * m.rows`: every lane
  of `.x4.m8n8`): first, at sub-step 0, a read `.rd ⟨row, 16⟩ bs` of its 16-byte row
  (`matrixRowLoc`), after which the thread stays at the instruction with `sub = 1` and
  `acc = rowVals bs`; then the event `.matrix (.move m) own recv` whose `own` are the row's
  bytes, continuing as `afterMatrix` (registers written, `sub = 0`, `acc = []`, next pc).
* `stmatrix`: first, at sub-step 0, the event `.matrix (.move m) own recv` with the bytes of its
  source registers, after which a supplying lane stays at the instruction with `sub = 1` and
  `acc = rowVals recv`; then a write `.wr ⟨row, 16⟩ bytes` of the received bytes at its row,
  continuing at the next instruction with `sub = 0` and `acc = []`.

Faults (a pending fault: the thread's next event is undefined behaviour): a row with an unknown
byte (`uninitialized`); received bytes of another length than the destinations need, or, for
`stmatrix`, other than 16 known bytes (`typeMismatch`); received bytes that do not rebuild
(`matrixVals`).

Contents: `matrixVals` (the destination values of received bytes) with `afterMatrix_eq`;
`rowVals` (the accumulator between the two events); `ownBytes`, `regBytes_ok`, `regBytes_regs`,
`regBytes_srcs`, `mmaOwn_ok`, `mmaOwn_regs`, `mmaOwn_srcs` (the contributed bytes from register
facts); `matrixRowLoc_bits`, `matrixRowLoc_b32` (the row of a 32-bit shared address register);
the template equations `matrixTmpl_*`, `matrixMoveTmpl_*`; and the inversion lemmas `fires_mma`,
`fires_movmatrix` (`fires_matrix_recv` for both), `fires_ldmatrix_rd`, `fires_ldmatrix_mx`,
`fires_stmatrix_mx`, `fires_stmatrix_wr`.

The model's side conditions, as they appear here: the CTA size is a multiple of 32 and the
instruction has a rule (`fires_matrix_rule`; hypotheses `hblk`, `hrule` of the shape lemmas);
a row address lies in the thread's own `.shared` window and is a multiple of 16
(`matrixRowLoc`); every source register holds a value of the register's width (`regBytes`).
`Fires` itself does not bound the received bytes: what a lane receives is the execution's
matter (`Consistent.matrix`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {pc : Nat} {e : Event}

/-! ## Received bytes and destination values -/

/-- The values that `k` destination registers of `w` bits receive from the bytes `recv` of a
matrix event: register `r` is rebuilt from bytes `r * (w / 8)` to `(r + 1) * (w / 8) - 1`
(`afterMatrix`). Bytes of another total length are a `typeMismatch`; a group that does not
rebuild gives `rebuild`'s fault. -/
def matrixVals (w k : Nat) (recv : List (Option Byte)) : Exec (List Value) :=
  if recv.length = k * (w / 8) then
    ((List.range k).map fun r => (recv.drop (r * (w / 8))).take (w / 8)).mapM (rebuild 3)
  else throw .typeMismatch

/-- The state after a matrix event, by the values its bytes rebuild into: the destinations are
written, the sub-step and accumulator are cleared and the thread is at the next instruction; or
the fault is pending. -/
theorem afterMatrix_eq (t : TState) (w : Nat) (ds : List Nat) (recv : List (Option Byte)) :
    afterMatrix t w ds recv = match matrixVals w ds.length recv with
      | .ok vs => next (setRegs { t with sub := 0, acc := [] } ds vs)
      | .error f => { t with fault := some f } := by
  unfold afterMatrix matrixVals
  dsimp only
  split
  · split <;> simp_all
  · rfl

/-- Received bytes that rebuild into `vs`: the thread continues at the next instruction with the
destinations holding `vs`. -/
theorem afterMatrix_ok {w : Nat} {ds : List Nat} {recv : List (Option Byte)} {vs : List Value}
    (h : matrixVals w ds.length recv = .ok vs) :
    afterMatrix t w ds recv = next (setRegs { t with sub := 0, acc := [] } ds vs) := by
  rw [afterMatrix_eq, h]

/-- Received bytes that do not rebuild leave the thread with a pending fault. -/
theorem afterMatrix_fault {w : Nat} {ds : List Nat} {recv : List (Option Byte)} {f : Fault}
    (h : matrixVals w ds.length recv = .error f) :
    afterMatrix t w ds recv = { t with fault := some f } := by
  rw [afterMatrix_eq, h]

/-- A list of fallible computations succeeds with `vs` exactly when each element succeeds with
the element of `vs` at its position. -/
theorem mapM_ok_iff {α β : Type} {f : α → Exec β} : ∀ {l : List α} {vs : List β},
    l.mapM f = .ok vs ↔ List.Forall₂ (fun a v => f a = .ok v) l vs
  | [], vs => by
    rw [List.mapM_nil]
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; rfl
  | a :: l, vs => by
    rw [List.mapM_cons]
    cases ha : f a with
    | error f' =>
      constructor
      · intro h; cases h
      · intro h; cases h with | cons h1 _ => rw [ha] at h1; cases h1
    | ok b =>
      cases hl : l.mapM f with
      | error f' =>
        constructor
        · intro h; cases h
        · intro h
          cases h with
          | cons h1 h2 => rw [mapM_ok_iff.mpr h2] at hl; cases hl
      | ok bs =>
        constructor
        · intro h
          cases h
          exact .cons ha (mapM_ok_iff.mp hl)
        · intro h
          cases h with
          | cons h1 h2 =>
            rw [ha] at h1; cases h1
            rw [mapM_ok_iff.mpr h2] at hl; cases hl
            rfl

/-- Received bytes that rebuild give one value per destination, from `k * (w / 8)` bytes. -/
theorem matrixVals_length {w k : Nat} {recv : List (Option Byte)} {vs : List Value}
    (h : matrixVals w k recv = .ok vs) : vs.length = k ∧ recv.length = k * (w / 8) := by
  unfold matrixVals at h
  split at h
  · rename_i hl
    have := (mapM_ok_iff.mp h).length_eq
    simp at this
    exact ⟨this.symm, hl⟩
  · cases h

/-- The value of destination `r` is `rebuild` of its own `w / 8` received bytes. -/
theorem matrixVals_get {w k : Nat} {recv : List (Option Byte)} {vs : List Value}
    (h : matrixVals w k recv = .ok vs) {r : Nat} {v : Value} (hv : vs[r]? = some v) :
    rebuild 3 ((recv.drop (r * (w / 8))).take (w / 8)) = .ok v := by
  unfold matrixVals at h
  split at h
  · have h2 := mapM_ok_iff.mp h
    have hr : r < vs.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hv
      cases hv
    have hk : r < k := by
      have := h2.length_eq
      simp at this
      omega
    have h3 := (List.forall₂_iff_get.mp h2).2 r (by simpa using hk) hr
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at h3
    rw [List.getElem?_eq_getElem hr] at hv
    cases hv
    exact h3
  · cases h

/-- Four 32-bit destinations (`ldmatrix.x4`, `mma.m16n8k16` with `.f32` accumulators): 16
received bytes, each register rebuilt from its own 4 bytes. -/
theorem matrixVals_x4 {recv : List (Option Byte)} {vs : List Value} :
    matrixVals 32 4 recv = .ok vs ↔ recv.length = 16 ∧ ∃ v0 v1 v2 v3, vs = [v0, v1, v2, v3] ∧
      rebuild 3 (recv.take 4) = .ok v0 ∧ rebuild 3 ((recv.drop 4).take 4) = .ok v1 ∧
      rebuild 3 ((recv.drop 8).take 4) = .ok v2 ∧ rebuild 3 ((recv.drop 12).take 4) = .ok v3 := by
  unfold matrixVals
  split
  · rename_i hl
    rw [mapM_ok_iff]
    simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil,
      Nat.reduceDiv, Nat.reduceMul, List.drop_zero]
    constructor
    · intro h
      rcases h with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩⟩
      exact ⟨hl, _, _, _, _, rfl, h0, h1, h2, h3⟩
    · rintro ⟨-, v0, v1, v2, v3, rfl, h0, h1, h2, h3⟩
      exact .cons h0 (.cons h1 (.cons h2 (.cons h3 .nil)))
  · rename_i hl
    constructor
    · intro h; cases h
    · rintro ⟨h, -⟩; exact absurd h hl

/-- One 32-bit destination (`movmatrix`): 4 received bytes, rebuilt into the register. -/
theorem matrixVals_x1 {recv : List (Option Byte)} {vs : List Value} :
    matrixVals 32 1 recv = .ok vs ↔ recv.length = 4 ∧ ∃ v, vs = [v] ∧ rebuild 3 recv = .ok v := by
  unfold matrixVals
  split
  · rename_i hl
    rw [mapM_ok_iff]
    simp only [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil,
      Nat.reduceDiv, Nat.reduceMul, List.drop_zero]
    have ht : recv.take 4 = recv := List.take_of_length_le (by omega)
    rw [ht]
    constructor
    · intro h
      rcases h with _ | ⟨h0, _ | _⟩
      exact ⟨by omega, _, rfl, h0⟩
    · rintro ⟨-, v, rfl, h0⟩
      exact .cons h0 .nil
  · rename_i hl
    constructor
    · intro h; cases h
    · rintro ⟨h, -⟩; exact absurd (by omega) hl

/-! ## The accumulator between the two events of `ldmatrix` and `stmatrix` -/

/-- The accumulator a thread keeps between the two events of `ldmatrix` or `stmatrix`: each known
byte of the row as its one-byte value (`byteValue`). -/
def rowVals (bs : List (Option Byte)) : List Value := bs.filterMap fun b => b.map byteValue

/-- The byte of a byte's value is the byte. -/
theorem valueByte_byteValue (b : Byte) : valueByte (byteValue b) = some b := rfl

/-- The bytes read back from the accumulator are the known bytes of the row. -/
theorem rowVals_bytes (bs : List (Option Byte)) :
    (rowVals bs).filterMap valueByte = bs.reduceOption := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | none => simpa [rowVals, List.reduceOption] using ih
    | some b =>
      simp only [rowVals, List.reduceOption, List.filterMap_cons, Option.map_some,
        valueByte_byteValue, id_eq] at ih ⊢
      rw [ih]

/-- A list of known bytes is the list of its bytes. -/
theorem reduceOption_all {α : Type} {bs : List (Option α)} (h : bs.all Option.isSome = true) :
    bs.reduceOption.map some = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | none => simp at h
    | some b =>
      simp only [List.all_cons, Option.isSome_some, Bool.true_and] at h
      simp only [List.reduceOption, List.filterMap_cons, id_eq, List.map_cons] at ih ⊢
      rw [ih h]

/-- The bytes an `ldmatrix` lane contributes at its matrix event are the bytes it read, when all
of them are known (which the read's continuation checks). -/
theorem rowVals_own {bs : List (Option Byte)} (h : bs.all Option.isSome = true) :
    ((rowVals bs).filterMap valueByte).map some = bs := by
  rw [rowVals_bytes, reduceOption_all h]

/-- A lane of a matrix load or store of 32 rows (`.x4.m8n8`) supplies a row address. -/
theorem laneOf_lt_rows {m : MatrixMove} (h : m.num * m.rows = 32) :
    laneOf L g < m.num * m.rows := by
  rw [h]
  exact Nat.mod_lt _ (by decide)

/-! ## The bytes a lane contributes, from register facts -/

/-- The bytes of the values `vs`, in order: what a lane whose source registers hold `vs`
contributes to a matrix event. -/
def ownBytes (vs : List Value) : List (Option Byte) := (vs.flatMap Value.toBytes).map some

/-- The bytes of two groups of registers are those of the first followed by those of the
second. -/
theorem ownBytes_append (xs ys : List Value) :
    ownBytes (xs ++ ys) = ownBytes xs ++ ownBytes ys := by
  simp [ownBytes]

/-- One step of `regBytes`. -/
private def regStep (L : Launch) (g : Nat) (t : TState) (w : Nat) (acc : List (Option Byte))
    (o : Opnd) : Exec (List (Option Byte)) := do
  let v ← readValue L g t w o
  unless v.bytes = w / 8 do throw .typeMismatch
  pure (acc ++ v.toBytes.map some)

private theorem regStep_ok {w : Nat} {acc : List (Option Byte)} {o : Opnd} {v : Value}
    (h1 : readValue L g t w o = .ok v) (h2 : v.bytes = w / 8) :
    regStep L g t w acc o = .ok (acc ++ v.toBytes.map some) := by
  simp [regStep, h1, h2, bind, Except.bind, pure, Except.pure]

private theorem regBytes_fold {w : Nat} : ∀ {os : List Opnd} {vs : List Value}
    (acc0 : List (Option Byte)),
    List.Forall₂ (fun o v => readValue L g t w o = .ok v ∧ v.bytes = w / 8) os vs →
    os.foldlM (regStep L g t w) acc0 = Except.ok (acc0 ++ ownBytes vs)
  | [], _, acc0, h => by
    cases h
    simp [ownBytes, pure, Except.pure]
  | o :: os, _, acc0, h => by
    cases h with
    | cons h1 h2 =>
      rename_i v vs
      rw [List.foldlM_cons, regStep_ok h1.1 h1.2]
      refine (regBytes_fold (acc0 ++ v.toBytes.map some) h2).trans ?_
      simp [ownBytes, List.append_assoc]

/-- Source operands that read as the values `vs`, each of `w / 8` bytes, contribute the bytes of
`vs` in operand order. -/
theorem regBytes_ok {w : Nat} {os : List Opnd} {vs : List Value}
    (h : List.Forall₂ (fun o v => readValue L g t w o = .ok v ∧ v.bytes = w / 8) os vs) :
    regBytes L g t w os = .ok (ownBytes vs) := by
  have := regBytes_fold (L := L) (g := g) (t := t) [] h
  rw [List.nil_append] at this
  exact this

/-- Registers `rs` that hold the values a table `val` gives them read as those values. -/
theorem forall₂_regs {w : Nat} {rs : List Nat} {val : Nat → Value}
    (hreg : ∀ r ∈ rs, t.regs r = some (val r)) (hb : ∀ r ∈ rs, (val r).bytes = w / 8) :
    List.Forall₂ (fun o v => readValue L g t w o = .ok v ∧ v.bytes = w / 8)
      (rs.map Opnd.reg) (rs.map val) := by
  induction rs with
  | nil => exact .nil
  | cons r rs ih =>
    refine .cons ⟨?_, hb r (by simp)⟩
      (ih (fun r hr => hreg r (by simp [hr])) (fun r hr => hb r (by simp [hr])))
    simp [readValue, readReg, hreg r (by simp), pure, Except.pure]

/-- Source registers `rs` that hold the values of a table `val`, each of `w / 8` bytes,
contribute the bytes of those values. -/
theorem regBytes_regs {w : Nat} {rs : List Nat} {val : Nat → Value}
    (hreg : ∀ r ∈ rs, t.regs r = some (val r)) (hb : ∀ r ∈ rs, (val r).bytes = w / 8) :
    regBytes L g t w (rs.map Opnd.reg) = .ok (ownBytes (rs.map val)) :=
  regBytes_ok (forall₂_regs hreg hb)

/-- `regBytes_regs` with the registers read off the operands (`opndRegs`): sources that are all
registers (`hsrcs`, by `rfl` for a literal instruction) holding the values of a table `val`. -/
theorem regBytes_srcs {w : Nat} {srcs : List Opnd} {val : Nat → Value}
    (hsrcs : srcs = (srcs.flatMap opndRegs).map Opnd.reg)
    (hreg : ∀ r ∈ srcs.flatMap opndRegs, t.regs r = some (val r))
    (hb : ∀ r ∈ srcs.flatMap opndRegs, (val r).bytes = w / 8) :
    regBytes L g t w srcs = .ok (ownBytes ((srcs.flatMap opndRegs).map val)) := by
  have h := regBytes_regs (L := L) (g := g) (w := w) hreg hb
  rwa [← hsrcs] at h

private theorem take_drop3 {α : Type} (n m : Nat) (l : List α) :
    l.take n ++ (l.drop n).take m ++ l.drop (n + m) = l := by
  rw [← List.drop_drop, List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- An MMA whose A, B and C registers are 32 bits wide (every type but `.f64`) and whose sources
read as the 4-byte values `vs` contributes the bytes of `vs` in operand order (A, B, C, then the
metadata of `mma.sp`). -/
theorem mmaOwn_ok {s : MmaSpec} {srcs : List Opnd} {vs : List Value}
    (ha : MmaSpec.regBits s.types.a = 32) (hc : MmaSpec.regBits s.types.c = 32)
    (h : List.Forall₂ (fun o v => readValue L g t 32 o = .ok v ∧ v.bytes = 32 / 8) srcs vs) :
    mmaOwn L g t s srcs = .ok (ownBytes vs) := by
  unfold mmaOwn
  simp only [ha, hc]
  obtain ⟨ra, rb, rc, rd⟩ := s.regs
  simp only
  rw [regBytes_ok (List.forall₂_take (ra + rb) h),
    regBytes_ok (List.forall₂_take rc (List.forall₂_drop (ra + rb) h)),
    regBytes_ok (List.forall₂_drop (ra + rb + rc) h)]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [← ownBytes_append, ← ownBytes_append, take_drop3]

/-- `mmaOwn_ok` for source registers `rs` that hold the 4-byte values of a table `val`. -/
theorem mmaOwn_regs {s : MmaSpec} {rs : List Nat} {val : Nat → Value}
    (ha : MmaSpec.regBits s.types.a = 32) (hc : MmaSpec.regBits s.types.c = 32)
    (hreg : ∀ r ∈ rs, t.regs r = some (val r)) (hb : ∀ r ∈ rs, (val r).bytes = 4) :
    mmaOwn L g t s (rs.map Opnd.reg) = .ok (ownBytes (rs.map val)) :=
  mmaOwn_ok ha hc (forall₂_regs hreg hb)

/-- `mmaOwn_regs` with the registers read off the operands (`opndRegs`): sources that are all
registers (`hsrcs`, by `rfl` for a literal instruction) holding the 4-byte values of a table
`val`. -/
theorem mmaOwn_srcs {s : MmaSpec} {srcs : List Opnd} {val : Nat → Value}
    (hsrcs : srcs = (srcs.flatMap opndRegs).map Opnd.reg)
    (ha : MmaSpec.regBits s.types.a = 32) (hc : MmaSpec.regBits s.types.c = 32)
    (hreg : ∀ r ∈ srcs.flatMap opndRegs, t.regs r = some (val r))
    (hb : ∀ r ∈ srcs.flatMap opndRegs, (val r).bytes = 4) :
    mmaOwn L g t s srcs = .ok (ownBytes ((srcs.flatMap opndRegs).map val)) := by
  have h := mmaOwn_regs (L := L) (g := g) (s := s) ha hc hreg hb
  rwa [← hsrcs] at h

/-! ## The row of a matrix load or store -/

/-- The row of an `ldmatrix`/`stmatrix` whose address is a 32-bit register holding the number
`a` (a `.shared` address of the thread's CTA) plus `off`: the location in the thread's own
shared window when the address is a multiple of 16, the fault `misaligned` otherwise. -/
theorem matrixRowLoc_bits {i : MatrixInstr} {win : SharedWindow} {r : Nat} {off : Int} {a : Nat}
    (hsp : i.space = some (.shared win)) (had : i.addr = some ⟨.reg r 32, off⟩)
    (hr : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) :
    matrixRowLoc L g t i =
      if wrapAddr 32 (BitVec.ofNat 64 a) off % 16 = 0 then
        .ok ⟨.shared, g / L.block, wrapAddr 32 (BitVec.ofNat 64 a) off⟩
      else .error .misaligned := by
  have h64 : a < 2 ^ 64 := by omega
  have hb : readBits L g t 32 (.reg r) = .ok (BitVec.ofNat 64 a) := readBits_b32 hr ha
  have hrr : readReg t r = .ok (.bits 32 (BitVec.ofNat 64 a)) := by
    simp [readReg, hr, b32, pure, Except.pure]
  simp only [matrixRowLoc, had, hsp, accessLoc, hrr, hb, toNat_ofNat_lt h64, ha, bind,
    Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, and_self, ↓reduceIte]

/-- A 32-bit address with offset 0 is the address. -/
theorem wrapAddr_zero {a : Nat} (ha : a < 2 ^ 32) : wrapAddr 32 (BitVec.ofNat 64 a) 0 = a := by
  have h64 : a < 18446744073709551616 := by omega
  have h32 : a < 4294967296 := ha
  simp [wrapAddr, truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32]

/-- The row of an `ldmatrix`/`stmatrix` at `[r]`, where the 32-bit register `r` holds the
16-byte aligned shared address `a`: location `a` of the thread's own shared window. -/
theorem matrixRowLoc_b32 {i : MatrixInstr} {win : SharedWindow} {r : Nat} {a : Nat}
    (hsp : i.space = some (.shared win)) (had : i.addr = some ⟨.reg r 32, 0⟩)
    (hr : t.regs r = some (b32 a)) (ha : a < 2 ^ 32) (hal : a % 16 = 0) :
    matrixRowLoc L g t i = .ok ⟨.shared, g / L.block, a⟩ := by
  rw [matrixRowLoc_bits (L := L) (g := g) hsp had hr ha, wrapAddr_zero ha]
  simp only [hal, ↓reduceIte]

/-! ## The template of each form -/

/-- A matrix instruction that fires a continuing event runs in a CTA whose size is a multiple of
32 and has the rule of its operation (`MatrixInstr.rule`): THREAD-MMA-SYNC for an MMA,
THREAD-MATRIX otherwise. -/
theorem fires_matrix_rule {i : MatrixInstr} (hf : Fires pc (matrixTmpl L g t i) e (some u)) :
    L.block % 32 = 0 ∧ i.rule = some (match i.op with
      | .mma _ => .threadMma
      | _ => .threadMatrix) := by
  unfold matrixTmpl at hf
  split at hf
  · rename_i hb
    split at hf
    all_goals first
      | exact absurd hf.2 (by simp)
      | (refine ⟨hb, ?_⟩; simp only [*])
  · exact absurd hf.2 (by simp)

/-- The template of a matrix load or store with a rule is `matrixMoveTmpl`. -/
theorem matrixTmpl_move {i : MatrixInstr} {m : MatrixMove} (hb : L.block % 32 = 0)
    (hr : i.rule = some .threadMatrix) (hop : i.op = .move m) :
    matrixTmpl L g t i = matrixMoveTmpl L g t i m := by
  obtain ⟨op, sp, ad, ds, srcs⟩ := i
  dsimp only at hop
  subst hop
  simp only [matrixTmpl, hb, ↓reduceIte, hr]

/-- The template of `movmatrix d, a`: the matrix event with the bytes of `a`, which continues by
writing `d`; a source that does not read as a 4-byte value is undefined behaviour. -/
theorem matrixTmpl_transpose {i : MatrixInstr} {d : Nat} {a : Opnd} (hb : L.block % 32 = 0)
    (hop : i.op = .transpose) (hd : i.dsts = [d]) (hs : i.srcs = [a]) :
    matrixTmpl L g t i = match regBytes L g t 32 [a] with
      | .error f => .ub f
      | .ok own => .matrix .transpose own (afterMatrix t 32 [d]) := by
  obtain ⟨op, sp, ad, ds, srcs⟩ := i
  dsimp only at hop hd hs
  subst hop hd hs
  simp only [matrixTmpl, hb, ↓reduceIte, MatrixInstr.rule]
  rfl

/-- The template of an MMA with a rule: the matrix event with the bytes of its A, B and C
registers (`mmaOwn`), which continues by writing its D registers; sources that do not read as
values of their widths are undefined behaviour. -/
theorem matrixTmpl_mma {i : MatrixInstr} {s : MmaSpec} (hb : L.block % 32 = 0)
    (hr : i.rule = some .threadMma) (hop : i.op = .mma s) :
    matrixTmpl L g t i = match mmaOwn L g t s i.srcs with
      | .error f => .ub f
      | .ok own => .matrix (.mma s) own (afterMatrix t (MmaSpec.regBits s.types.d) i.dsts) := by
  obtain ⟨op, sp, ad, ds, srcs⟩ := i
  dsimp only at hop
  subst hop
  simp only [matrixTmpl, hb, ↓reduceIte, hr]
  rfl

/-- `ldmatrix`, first event of a lane that supplies a row (sub-step 0): the read of its 16-byte
row, after which the thread stays at the instruction with the row in its accumulator; an unknown
byte is a pending `uninitialized` fault, a bad row address undefined behaviour. -/
theorem matrixMoveTmpl_load_rd {i : MatrixInstr} {m : MatrixMove} (hst : m.store = false)
    (hsup : laneOf L g < m.num * m.rows) (hs : t.sub = 0) :
    matrixMoveTmpl L g t i m = match matrixRowLoc L g t i with
      | .error f => .ub f
      | .ok loc => .read { loc := loc, size := 16 } fun bs =>
          if bs.length = 16 ∧ bs.all Option.isSome then { t with sub := 1, acc := rowVals bs }
          else { t with fault := some .uninitialized } := by
  simp only [matrixMoveTmpl, hst, hsup, hs, Bool.false_eq_true, ↓reduceIte, and_self]
  rfl

/-- `ldmatrix`, the matrix event (a supplying lane after its read, or a lane that supplies no
row): the lane contributes the bytes in its accumulator and continues as `afterMatrix`. -/
theorem matrixMoveTmpl_load_mx {i : MatrixInstr} {m : MatrixMove} (hst : m.store = false)
    (hs : ¬ (laneOf L g < m.num * m.rows ∧ t.sub = 0)) :
    matrixMoveTmpl L g t i m = .matrix (.move m)
      (if laneOf L g < m.num * m.rows then (t.acc.filterMap valueByte).map some else [])
      (afterMatrix t 32 i.dsts) := by
  simp only [matrixMoveTmpl, hst, hs, Bool.false_eq_true, ↓reduceIte]

/-- `stmatrix`, first event (sub-step 0): the matrix event with the bytes of the source
registers. A supplying lane then stays at the instruction with the 16 received bytes in its
accumulator (other bytes are a pending `typeMismatch` fault); another lane continues at the next
instruction. -/
theorem matrixMoveTmpl_store_mx {i : MatrixInstr} {m : MatrixMove} (hst : m.store = true)
    (hs : t.sub = 0) :
    matrixMoveTmpl L g t i m = match regBytes L g t 32 i.srcs with
      | .error f => .ub f
      | .ok own => .matrix (.move m) own fun recv =>
          if laneOf L g < m.num * m.rows then
            if recv.length = 16 ∧ recv.all Option.isSome then
              { t with sub := 1, acc := rowVals recv }
            else { t with fault := some .typeMismatch }
          else next t := by
  simp only [matrixMoveTmpl, hst, hs, ↓reduceIte]
  rfl

/-- `stmatrix`, second event (sub-step 1): the write of the accumulated bytes to the 16-byte
row, after which the thread continues at the next instruction with the sub-step and accumulator
cleared. -/
theorem matrixMoveTmpl_store_wr {i : MatrixInstr} {m : MatrixMove} (hst : m.store = true)
    (hs : t.sub ≠ 0) :
    matrixMoveTmpl L g t i m = match matrixRowLoc L g t i with
      | .error f => .ub f
      | .ok loc => .write { loc := loc, size := 16 } (t.acc.filterMap valueByte)
          (next { t with sub := 0, acc := [] }) := by
  simp only [matrixMoveTmpl, hst, hs, ↓reduceIte]
  rfl

/-! ## Inversion of fired events -/

/-- A continuing event of a matrix load or store is one of `matrixMoveTmpl`. -/
theorem fires_matrix_move {i : MatrixInstr} {m : MatrixMove} (hop : i.op = .move m)
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e (some u)) :
    Fires pc (matrixMoveTmpl L g t i m) e (some u) := by
  have hf' : Fires pc (matrixTmpl L g t i) e (some u) := hf
  obtain ⟨hb, hr⟩ := fires_matrix_rule hf'
  rw [hop] at hr
  rwa [matrixTmpl_move hb hr hop] at hf'

/-- `mma.sync`: one event `.matrix (.mma s) own recv` with the bytes `own` of the A, B and C
registers; the thread continues as `afterMatrix`, its D registers rebuilt from `recv`. -/
theorem fires_mma {i : MatrixInstr} {s : MmaSpec} (hop : i.op = .mma s)
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e (some u)) :
    ∃ own recv, mmaOwn L g t s i.srcs = .ok own ∧ e = ⟨pc, .matrix (.mma s) own recv⟩ ∧
      u = afterMatrix t (MmaSpec.regBits s.types.d) i.dsts recv := by
  have hf' : Fires pc (matrixTmpl L g t i) e (some u) := hf
  obtain ⟨hb, hr⟩ := fires_matrix_rule hf'
  rw [hop] at hr
  rw [matrixTmpl_mma hb hr hop] at hf'
  cases hown : mmaOwn L g t s i.srcs with
  | error f => rw [hown] at hf'; exact absurd hf'.2 (by simp)
  | ok own =>
    rw [hown] at hf'
    obtain ⟨recv, rfl, hu⟩ := hf'
    exact ⟨own, recv, rfl, rfl, Option.some.inj hu⟩

/-- `fires_mma` for source registers `rs` that hold the 4-byte values of a table `val` (A, B
and C registers of 32 bits): the lane contributes the bytes of those values. -/
theorem fires_mma_regs {i : MatrixInstr} {s : MmaSpec} {rs : List Nat} {val : Nat → Value}
    (hop : i.op = .mma s) (hsrcs : i.srcs = rs.map Opnd.reg)
    (ha : MmaSpec.regBits s.types.a = 32) (hc : MmaSpec.regBits s.types.c = 32)
    (hreg : ∀ r ∈ rs, t.regs r = some (val r)) (hb : ∀ r ∈ rs, (val r).bytes = 4)
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e (some u)) :
    ∃ recv, e = ⟨pc, .matrix (.mma s) (ownBytes (rs.map val)) recv⟩ ∧
      u = afterMatrix t (MmaSpec.regBits s.types.d) i.dsts recv := by
  obtain ⟨own, recv, hown, rfl, rfl⟩ := fires_mma hop hf
  rw [hsrcs, mmaOwn_regs ha hc hreg hb] at hown
  cases hown
  exact ⟨recv, rfl, rfl⟩

/-- `movmatrix d, a`: one event `.matrix .transpose own recv` with the bytes `own` of `a`; the
thread continues as `afterMatrix`, `d` rebuilt from the 4 bytes `recv`. -/
theorem fires_movmatrix {i : MatrixInstr} {d : Nat} {a : Opnd} (hop : i.op = .transpose)
    (hd : i.dsts = [d]) (hs : i.srcs = [a])
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e (some u)) :
    ∃ own recv, regBytes L g t 32 [a] = .ok own ∧ e = ⟨pc, .matrix .transpose own recv⟩ ∧
      u = afterMatrix t 32 [d] recv := by
  have hf' : Fires pc (matrixTmpl L g t i) e (some u) := hf
  obtain ⟨hb, -⟩ := fires_matrix_rule hf'
  rw [matrixTmpl_transpose hb hop hd hs] at hf'
  cases hown : regBytes L g t 32 [a] with
  | error f => rw [hown] at hf'; exact absurd hf'.2 (by simp)
  | ok own =>
    rw [hown] at hf'
    obtain ⟨recv, rfl, hu⟩ := hf'
    exact ⟨own, recv, rfl, rfl, Option.some.inj hu⟩

/-- `fires_movmatrix` for a source register that holds the 4-byte value `v`: the lane
contributes the bytes of `v`. -/
theorem fires_movmatrix_reg {i : MatrixInstr} {d r : Nat} {v : Value} (hop : i.op = .transpose)
    (hd : i.dsts = [d]) (hs : i.srcs = [.reg r]) (hr : t.regs r = some v) (hb : v.bytes = 4)
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e (some u)) :
    ∃ recv, e = ⟨pc, .matrix .transpose (ownBytes [v]) recv⟩ ∧ u = afterMatrix t 32 [d] recv := by
  obtain ⟨own, recv, hown, rfl, rfl⟩ := fires_movmatrix hop hd hs hf
  have h := regBytes_regs (L := L) (g := g) (t := t) (w := 32) (rs := [r]) (val := fun _ => v)
    (fun _ _ => by simp_all) (fun _ _ => hb)
  rw [show [r].map Opnd.reg = [Opnd.reg r] from rfl, hown] at h
  cases h
  exact ⟨recv, rfl, rfl⟩

/-- The width of the registers that a matrix instruction's event writes: the D registers of an
MMA (64 bits for `.f64`), 32 bits for `movmatrix` and `ldmatrix`. -/
def matrixDstBits : MatrixOp → Nat
  | .mma s => MmaSpec.regBits s.types.d
  | _ => 32

/-- A matrix instruction other than a load or store that fires a continuing event fires the
matrix event of its operation and continues as `afterMatrix` on its destinations. -/
theorem fires_matrix_recv {i : MatrixInstr} (hop : ∀ m, i.op ≠ .move m)
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e (some u)) :
    ∃ own recv, e = ⟨pc, .matrix i.op own recv⟩ ∧
      u = afterMatrix t (matrixDstBits i.op) i.dsts recv := by
  cases hi : i.op with
  | move m => exact absurd hi (hop m)
  | mma s =>
    obtain ⟨own, recv, -, he, hu⟩ := fires_mma hi hf
    exact ⟨own, recv, he, hu⟩
  | transpose =>
    have hr := (fires_matrix_rule (L := L) (g := g) (t := t) (pc := pc) (e := e) (u := u) hf).2
    rw [hi] at hr
    obtain ⟨d, a, hd, hs⟩ : ∃ d a, i.dsts = [d] ∧ i.srcs = [a] := by
      have hr' : i.rule = some .threadMatrix := hr
      simp only [MatrixInstr.rule, hi] at hr'
      split at hr'
      · exact ⟨_, _, ‹_›, ‹_›⟩
      · cases hr'
    obtain ⟨own, recv, -, he, hu⟩ := fires_movmatrix hi hd hs hf
    exact ⟨own, recv, he, by rw [hu, hd]; rfl⟩

/-- `ldmatrix`, first event of a supplying lane (sub-step 0): the read `.rd ⟨row, 16⟩ bs` of its
row. With all 16 bytes known the thread stays at the instruction with `sub = 1` and
`acc = rowVals bs`; otherwise it has a pending `uninitialized` fault. -/
theorem fires_ldmatrix_rd {i : MatrixInstr} {m : MatrixMove} (hop : i.op = .move m)
    (hst : m.store = false) (hsup : laneOf L g < m.num * m.rows) (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e (some u)) :
    ∃ loc bs, matrixRowLoc L g t i = .ok loc ∧ bs.length = 16 ∧
      e = ⟨pc, .rd { loc := loc, size := 16 } bs⟩ ∧
      u = if bs.all Option.isSome = true then { t with sub := 1, acc := rowVals bs }
        else { t with fault := some .uninitialized } := by
  have hf' := fires_matrix_move hop hf
  rw [matrixMoveTmpl_load_rd hst hsup hs] at hf'
  cases hloc : matrixRowLoc L g t i with
  | error f => rw [hloc] at hf'; exact absurd hf'.2 (by simp)
  | ok loc =>
    rw [hloc] at hf'
    obtain ⟨bs, hl, rfl, hu⟩ := hf'
    refine ⟨loc, bs, rfl, hl, rfl, ?_⟩
    have hl' : bs.length = 16 := hl
    rw [Option.some.inj hu]
    simp only [hl', true_and]

/-- `ldmatrix`, the matrix event (sub-step 1 of a supplying lane, or a lane that supplies no
row): `.matrix (.move m) own recv` with the bytes of the accumulator; the thread continues as
`afterMatrix`, its destinations rebuilt from `recv`. -/
theorem fires_ldmatrix_mx {i : MatrixInstr} {m : MatrixMove} (hop : i.op = .move m)
    (hst : m.store = false) (hs : ¬ (laneOf L g < m.num * m.rows ∧ t.sub = 0))
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e (some u)) :
    ∃ recv, e = ⟨pc, .matrix (.move m)
        (if laneOf L g < m.num * m.rows then (t.acc.filterMap valueByte).map some else [])
        recv⟩ ∧
      u = afterMatrix t 32 i.dsts recv := by
  have hf' := fires_matrix_move hop hf
  rw [matrixMoveTmpl_load_mx hst hs] at hf'
  obtain ⟨recv, rfl, hu⟩ := hf'
  exact ⟨recv, rfl, Option.some.inj hu⟩

/-- `stmatrix`, first event (sub-step 0): `.matrix (.move m) own recv` with the bytes `own` of
the source registers. A supplying lane that receives 16 known bytes stays at the instruction
with `sub = 1` and `acc = rowVals recv` (other bytes: a pending `typeMismatch` fault); a lane
that supplies no row continues at the next instruction. -/
theorem fires_stmatrix_mx {i : MatrixInstr} {m : MatrixMove} (hop : i.op = .move m)
    (hst : m.store = true) (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e (some u)) :
    ∃ own recv, regBytes L g t 32 i.srcs = .ok own ∧ e = ⟨pc, .matrix (.move m) own recv⟩ ∧
      u = if laneOf L g < m.num * m.rows then
          if recv.length = 16 ∧ recv.all Option.isSome = true then
            { t with sub := 1, acc := rowVals recv }
          else { t with fault := some .typeMismatch }
        else next t := by
  have hf' := fires_matrix_move hop hf
  rw [matrixMoveTmpl_store_mx hst hs] at hf'
  cases hown : regBytes L g t 32 i.srcs with
  | error f => rw [hown] at hf'; exact absurd hf'.2 (by simp)
  | ok own =>
    rw [hown] at hf'
    obtain ⟨recv, rfl, hu⟩ := hf'
    exact ⟨own, recv, rfl, rfl, Option.some.inj hu⟩

/-- `stmatrix`, second event (sub-step 1): the write `.wr ⟨row, 16⟩ bytes` of the accumulated
bytes at the lane's row; the thread continues at the next instruction with `sub = 0` and
`acc = []`. -/
theorem fires_stmatrix_wr {i : MatrixInstr} {m : MatrixMove} (hop : i.op = .move m)
    (hst : m.store = true) (hs : t.sub ≠ 0)
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e (some u)) :
    ∃ loc, matrixRowLoc L g t i = .ok loc ∧
      e = ⟨pc, .wr { loc := loc, size := 16 } (t.acc.filterMap valueByte)⟩ ∧
      u = next { t with sub := 0, acc := [] } := by
  have hf' := fires_matrix_move hop hf
  rw [matrixMoveTmpl_store_wr hst hs] at hf'
  cases hloc : matrixRowLoc L g t i with
  | error f => rw [hloc] at hf'; exact absurd hf'.2 (by simp)
  | ok loc =>
    rw [hloc] at hf'
    obtain ⟨rfl, hu⟩ := hf'
    exact ⟨loc, rfl, rfl, Option.some.inj hu⟩

end
end PTX.Flow
