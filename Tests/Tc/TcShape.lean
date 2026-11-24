-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode
public import Lemmas.Tmem.TmemStore
public import Lemmas.Order.OrderBaseCausality

/-! The access shapes of `tcgen05.ld` and `tcgen05.st` (THREAD-TC-DATA-ADDRESS, EXT-TCFIG,
EXT-TMEM-LANE-FIELD): decoding of every shape in both operand orders, the cells of each shape's
fragment (both half-warps of `.16x32bx2` with the half-split offset), a store followed by a load
of the same shape returning the stored distinct values, and rejections: a lane field that leaves
the warp's chunk, a half-split offset that carries, columns outside the allocation, lanes that
disagree on the half-split offset, and a lane that exits before the collective. -/
namespace PTX.Tests.TcShape
open TcMma
noncomputable section

/-! ## Decoding -/

private def env : Decode.Env := { classes := [⟨"r".toList, 8, 32⟩], labels := [], params := [] }
-- Every shape, as a load and as a store; `.num` repetitions of the shape's registers.
example : Decode.op env "tcgen05.ld.sync.aligned.32x32b.x2.b32"
    [.vector [.register "r1", .register "r2"], .address [.register "r0"]] =
    .ok (.tcLd [1, 2] 0 .s32x32b) := rfl
example : Decode.op env "tcgen05.ld.sync.aligned.16x64b.x2.b32"
    [.vector [.register "r1", .register "r2"], .address [.register "r0"]] =
    .ok (.tcLd [1, 2] 0 .s16x64b) := rfl
example : Decode.op env "tcgen05.ld.sync.aligned.16x128b.x1.b32"
    [.vector [.register "r1", .register "r2"], .address [.register "r0"]] =
    .ok (.tcLd [1, 2] 0 .s16x128b) := rfl
example : Decode.op env "tcgen05.ld.sync.aligned.16x256b.x1.b32"
    [.vector [.register "r1", .register "r2", .register "r3", .register "r4"],
      .address [.register "r0"]] =
    .ok (.tcLd [1, 2, 3, 4] 0 .s16x256b) := rfl
example : Decode.op env "tcgen05.ld.sync.aligned.16x32bx2.x2.b32"
    [.vector [.register "r1", .register "r2"], .address [.register "r0"], .literal "64"] =
    .ok (.tcLd [1, 2] 0 (.s16x32bx2 64)) := rfl
example : Decode.op env "tcgen05.st.sync.aligned.32x32b.x2.b32"
    [.address [.register "r0"], .vector [.register "r1", .register "r2"]] =
    .ok (.tcSt 0 [.reg 1, .reg 2] .s32x32b) := rfl
example : Decode.op env "tcgen05.st.sync.aligned.16x64b.x2.b32"
    [.address [.register "r0"], .vector [.register "r1", .register "r2"]] =
    .ok (.tcSt 0 [.reg 1, .reg 2] .s16x64b) := rfl
example : Decode.op env "tcgen05.st.sync.aligned.16x128b.x1.b32"
    [.address [.register "r0"], .vector [.register "r1", .register "r2"]] =
    .ok (.tcSt 0 [.reg 1, .reg 2] .s16x128b) := rfl
example : Decode.op env "tcgen05.st.sync.aligned.16x256b.x1.b32"
    [.address [.register "r0"],
      .vector [.register "r1", .register "r2", .register "r3", .register "r4"]] =
    .ok (.tcSt 0 [.reg 1, .reg 2, .reg 3, .reg 4] .s16x256b) := rfl
example : Decode.op env "tcgen05.st.sync.aligned.16x32bx2.x2.b32"
    [.address [.register "r0"], .literal "0x40", .vector [.register "r1", .register "r2"]] =
    .ok (.tcSt 0 [.reg 1, .reg 2] (.s16x32bx2 64)) := rfl
-- `[taddr+0]` is the address `[taddr]`; another offset is not decoded.
example : Decode.op env "tcgen05.ld.sync.aligned.16x32bx2.x1.b32"
    [.vector [.register "r1"], .address [.offset "+" (.register "r0") (.literal "0")],
      .literal "32"] = .ok (.tcLd [1] 0 (.s16x32bx2 32)) := rfl
example : (Decode.op env "tcgen05.ld.sync.aligned.32x32b.x1.b32"
    [.vector [.register "r1"], .address [.offset "+" (.register "r0") (.literal "4")]]).toOption =
    none := rfl
-- The vector must be `.num` repetitions of the shape (Table 59), and not an NA entry: 64
-- repetitions of `.16x256b` would be 256 registers.
example : (Decode.op env "tcgen05.ld.sync.aligned.16x128b.x1.b32"
    [.vector [.register "r1"], .address [.register "r0"]]).toOption = none := rfl
example : (Decode.op env "tcgen05.ld.sync.aligned.16x256b.x2.b32"
    [.vector [.register "r1", .register "r2", .register "r3", .register "r4"],
      .address [.register "r0"]]).toOption = none := rfl
example : (Decode.tcVector .s16x256b 64 256).toOption = none := rfl
example : (Decode.tcVector .s16x128b 64 128).toOption = some () := rfl
example : TcShape.countOk .s16x256b 256 = false := rfl
-- `.16x32bx2` needs its immediate, an integer constant that is not negative.
example : (Decode.op env "tcgen05.ld.sync.aligned.16x32bx2.x1.b32"
    [.vector [.register "r1"], .address [.register "r0"]]).toOption = none := rfl
example : (Decode.op env "tcgen05.ld.sync.aligned.16x32bx2.x1.b32"
    [.vector [.register "r1"], .address [.register "r0"], .register "r2"]).toOption = none := rfl
example : (Decode.op env "tcgen05.ld.sync.aligned.16x32bx2.x1.b32"
    [.vector [.register "r1"], .address [.register "r0"], .literal "-1"]).toOption = none := rfl
-- A `.shape1` takes no immediate, unknown shapes are rejected, and packing and unpacking of an
-- aligned shape decode to the packed shape (THREAD-TC-PACK16).
example : (Decode.op env "tcgen05.ld.sync.aligned.16x64b.x1.b32"
    [.vector [.register "r1"], .address [.register "r0"], .literal "1"]).toOption = none := rfl
example : Decode.op env "tcgen05.ld.sync.aligned.32x32b.x2.pack::16b.b32"
    [.vector [.register "r1", .register "r2"], .address [.register "r0"]] =
    .ok (.tcLd [1, 2] 0 (.packed16 .s32x32b) none) := rfl
example : Decode.op env "tcgen05.st.sync.aligned.16x64b.x2.unpack::16b.b32"
    [.address [.register "r0"], .vector [.register "r1", .register "r2"]] =
    .ok (.tcSt 0 [.reg 1, .reg 2] (.packed16 .s16x64b)) := rfl
example : (Decode.op env "tcgen05.ld.sync.aligned.16x32b.x1.b32"
    [.vector [.register "r1"], .address [.register "r0"]]).toOption = none := rfl

/-! ## The cells of each fragment

A CTA of four warps. `cell g s a j` is register `j` of thread `g` (CTA thread index) for a load
or store of shape `s` at address `a`; a cell is (CTA, lane, column). -/

private def L4 : Launch := { grid := 1, block := 128, params := fun _ => none, clusterSize := 1 }
private abbrev cell (g : Nat) (s : TcShape) (a j : Nat) : Cell := tcDataCell L4 g s a j

-- `.32x32b` (Figure 186): thread lane `l` is lane `l` of the warp's chunk, register `j` column
-- `j`; warp 1's lane field may be 0 (relative) or 32 (absolute).
example : cell 40 .s32x32b 8 3 = ⟨0, 40, 11⟩ := rfl
example : cell 40 .s32x32b (32 * 2 ^ 16 + 8) 3 = ⟨0, 40, 11⟩ := rfl
-- `.16x64b` (Figure 187): lane `l / 4 + 8 (l % 2)`, column `2 j + (l / 2) % 2`.
example : cell 0 .s16x64b 0 0 = ⟨0, 0, 0⟩ := rfl
example : cell 1 .s16x64b 0 0 = ⟨0, 8, 0⟩ := rfl
example : cell 2 .s16x64b 0 0 = ⟨0, 0, 1⟩ := rfl
example : cell 31 .s16x64b 0 1 = ⟨0, 15, 3⟩ := rfl
-- `.16x128b` (Figure 188): lane `l / 4 + 8 (j % 2)`, column `4 (j / 2) + l % 4`.
example : cell 5 .s16x128b 0 0 = ⟨0, 1, 1⟩ := rfl
example : cell 5 .s16x128b 0 1 = ⟨0, 9, 1⟩ := rfl
example : cell 5 .s16x128b 0 2 = ⟨0, 1, 5⟩ := rfl
-- `.16x256b` (Figure 189): lane `l / 4 + 8 ((j % 4) / 2)`, column `8 (j / 4) + 2 (l % 4) + j % 2`.
example : cell 6 .s16x256b 0 1 = ⟨0, 1, 5⟩ := rfl
example : cell 6 .s16x256b 0 3 = ⟨0, 9, 5⟩ := rfl
example : cell 6 .s16x256b 0 4 = ⟨0, 1, 12⟩ := rfl
-- A 16-lane access of warp 1 at lane field 16 (relative) or 48 (absolute) covers lanes 48–63.
example : cell 33 .s16x64b (16 * 2 ^ 16) 0 = ⟨0, 56, 0⟩ := rfl
example : cell 33 .s16x64b (48 * 2 ^ 16) 0 = ⟨0, 56, 0⟩ := rfl
-- `.16x32bx2` with `immHalfSplitoff = 64` at column 8 (Figure 190): threads 0–15 access the
-- first 16-lane access at column 8, threads 16–31 the second, at column 8 + 64, on the same
-- lanes; thread `16 + i` is lane `i` of the second access.
example : cell 3 (.s16x32bx2 64) 8 0 = ⟨0, 3, 8⟩ := rfl
example : cell 3 (.s16x32bx2 64) 8 1 = ⟨0, 3, 9⟩ := rfl
example : cell 19 (.s16x32bx2 64) 8 0 = ⟨0, 3, 72⟩ := rfl
example : cell 19 (.s16x32bx2 64) 8 1 = ⟨0, 3, 73⟩ := rfl
-- In warp 1 with lane field 16 the halves are lanes 48–63.
example : cell 51 (.s16x32bx2 64) (16 * 2 ^ 16 + 8) 1 = ⟨0, 51, 73⟩ := rfl
example : cell 35 (.s16x32bx2 64) (16 * 2 ^ 16 + 8) 1 = ⟨0, 51, 9⟩ := rfl

-- Every shape: a thread's distinct registers are distinct cells.
example (g a : Nat) (s : TcShape) (j j' : Nat) (h : j ≠ j') : cell g s a j ≠ cell g s a j' :=
  fun he => h (tcDataCell_inj he)

/-! ## Issue: supported addresses and counts -/

-- Warp 1: a 16-lane access may start at relative lane 16 or absolute lane 48; at lane field 17
-- it would cross into warp 2's lanes.
example : tcDataAddressOk L4 40 .s16x64b (16 * 2 ^ 16) = true := rfl
example : tcDataAddressOk L4 40 .s16x64b (48 * 2 ^ 16) = true := rfl
example : tcDataAddressOk L4 40 .s16x64b (17 * 2 ^ 16) = false := rfl
example : tcDataAddressOk L4 40 (.s16x32bx2 64) (17 * 2 ^ 16) = false := rfl
-- A 32-lane access cannot start at lane 16 of the chunk.
example : tcDataAddressOk L4 40 .s32x32b (16 * 2 ^ 16) = false := rfl
-- The half-split offset must stay in the column field: no carry into the lane field, and no lane
-- displacement.
example : tcDataAddressOk L4 0 (.s16x32bx2 64) 0xFFC0 = false := rfl
example : tcDataAddressOk L4 0 (.s16x32bx2 64) 0xFF80 = true := rfl
example : tcDataAddressOk L4 0 (.s16x32bx2 (16 * 2 ^ 16)) 0 = false := rfl

private def ts (a : Nat) : TState := { regs := fun
  | 0 => some (.bits 32 (BitVec.ofNat 64 a))
  | 1 => some (.bits 32 (BitVec.ofNat 64 7))
  | 2 => some (.bits 32 (BitVec.ofNat 64 9))
  | _ => none }

-- The event records the shape and the half-split offset.
example : tcTmpl L4 19 (ts 8) (.tcSt 0 [.reg 1, .reg 2] (.s16x32bx2 64)) =
    .tc (.st 8 [.bits 32 (BitVec.ofNat 64 7), .bits 32 (BitVec.ofNat 64 9)] (.s16x32bx2 64))
      (next (ts 8)) := rfl
-- A lane field that leaves the warp's chunk, a carrying offset or a count that is not a
-- repetition of the shape has no rule.
example : tcTmpl L4 40 (ts (17 * 2 ^ 16)) (.tcSt 0 [.reg 1, .reg 2] .s16x64b) = .ub .noRule :=
  rfl
example : tcTmpl L4 0 (ts 0xFFC0) (.tcSt 0 [.reg 1, .reg 2] (.s16x32bx2 64)) = .ub .noRule :=
  rfl
example : tcTmpl L4 0 (ts 0) (.tcSt 0 [.reg 1, .reg 2] .s16x256b) = .ub .noRule := rfl
example : tcTmpl L4 0 (ts 0) (.tcLd [3] 0 .s16x128b) = .ub .noRule := rfl

/-! ## Store, then load: the load returns the stored values

Thread 0 (warp 0, lane 0) allocates 512 columns, stores `vs` with shape `s` at address `a`, waits
with `wait::st` and loads with the same shape and address. Each register slot of the load reads
the cell the store wrote in the same slot, so a load that satisfies `LoadReadOk` returns the
stored words. -/

private def L1 : Launch := { grid := 1, block := 32, params := fun _ => none, clusterSize := 1 }
private def own : Tmem.Pair.WarpRequest := ⟨0, 0, fun _ => 0, 0, some ⟨.shared, 0, 0⟩, .alloc 512⟩
private def rec : Tmem.Pair.Requests := ⟨own, .one, .alloc 512 0⟩

def X (s : TcShape) (a : Nat) (vs ws : List Value) : Execution where
  tr g := if g = 0 then
      [⟨0, .tc (.resource .one own.dst own.request)⟩, ⟨1, .tc (.st a vs s)⟩, ⟨2, .tc .waitSt⟩,
        ⟨3, .tc (.ld a ws s)⟩]
    else []
  rf _ _ := none
  tmemHistory cta := if cta = 0 then [rec] else []

section Roundtrip
variable {s : TcShape} {a : Nat} {vs ws : List Value}

private theorem get0 (i : Nat) : (X s a vs ws).get (0, i) =
    [⟨0, .tc (.resource .one own.dst own.request)⟩, ⟨1, .tc (.st a vs s)⟩, ⟨2, .tc .waitSt⟩,
      ⟨(3 : Nat), .tc (.ld a ws s)⟩][i]? := by
  simp [Execution.get, X]

private theorem baseCausalityAt {i j : Nat} (hij : i < j) (hj : j < 4) (hna : j ≠ 1) :
    baseCausality L1 (X s a vs ws) (0, i) (0, j) := by
  refine .single (.inl (po_of_not_access rfl hij (by simp [X]; omega) ?_))
  rw [get0]
  rcases j with _ | _ | _ | _ | j
  · omega
  · omega
  · simp [Event.acc]
  · simp [Event.acc]
  · omega

private theorem baseCausalitySt : baseCausality L1 (X s a vs ws) (0, 0) (0, 1) := by
  refine .single (.inl ⟨rfl, by decide, by simp [X], fun h => ?_⟩)
  have := h.1
  rw [get0] at this
  simp [Event.acc] at this

/-- The store is the only Tensor Memory write. -/
private theorem only_store {o : EvId} {c : Cell} (h : TmemWrite L1 (X s a vs ws) o c) :
    o = (0, 1) := by
  obtain ⟨g, i⟩ := o
  have hev : ∀ ev, (X s a vs ws).get (g, i) = some ev → g = 0 := by
    intro ev hg
    by_contra hne
    simp [Execution.get, X, hne] at hg
  rcases h with ⟨_, _, _, _, _, _, ⟨pc, hp⟩, -⟩ | ⟨_, _, _, _, ⟨pc, hp⟩, -, -⟩ |
      ⟨_, _, _, _, hcp, -, -, -⟩ | ⟨_, ⟨pc, hp⟩, -⟩
  all_goals
    first
    | obtain rfl := hev _ hp
      rw [get0] at hp
      rcases i with _ | _ | _ | _ | i <;> simp at hp ⊢
    | obtain ⟨pc, hp⟩ := hcp
      obtain rfl := hev _ hp
      rw [get0] at hp
      rcases i with _ | _ | _ | _ | i <;> simp at hp ⊢

/-- The store at `(0, 1)` is the source of the load at `(0, 3)`: their cells agree and no
other write of the cell exists. -/
theorem readSource {j : Nat} (hj : j < vs.length) :
    ReadSource L1 (X s a vs ws) .ld (0, 1) (0, 3) (tcDataCell L1 0 s a j) := by
  refine ⟨by decide, .inr (.inl ⟨a, vs, s, j, ⟨1, rfl⟩, hj, rfl⟩),
    .inr (.inl ⟨⟨a, vs, s, ⟨1, rfl⟩⟩, .inl ⟨(0, 2), ⟨2, rfl⟩, rfl, by decide,
      .inl (baseCausalityAt (by decide) (by decide) (by decide))⟩⟩), ?_, ?_⟩
  · intro o ho
    exact .inl (only_store ho)
  · intro cta r hr hcov d hd
    exfalso
    rcases hd with ⟨n, base, pc, -, ⟨group, hg⟩, -⟩ | ⟨q, hq, -⟩
    · obtain ⟨g, i⟩ := d
      by_cases h0 : g = 0
      · subst h0
        rw [get0] at hg
        rcases i with _ | _ | _ | _ | i <;> simp [own] at hg
      · simp [Execution.get, X, h0] at hg
    · simp [X] at hq

/-- **Store, then load**: a load satisfying the read rule returns, in every register, the word
the store wrote in that register. -/
theorem roundtrip (hok : LoadReadOk L1 [] (X s a vs ws)) (hlen : ws.length = vs.length)
    (h4 : ∀ v ∈ vs, v.bytes = 4) (_hcol : ∀ j < vs.length, (tcDataCell L1 0 s a j).column < 512)
    {j : Nat} (hj : j < vs.length) : ws[j]? = vs[j]? := by
  obtain ⟨v, hv⟩ : ∃ v, vs[j]? = some v := ⟨vs[j], List.getElem?_eq_getElem hj⟩
  obtain ⟨w, hw, hc⟩ := hok (0, 3) a ws s j (0, 1) (tcDataCell L1 0 s a j) v ⟨3, rfl⟩
    ⟨a, ws, s, ⟨3, rfl⟩, by omega, rfl⟩ (readSource (by omega))
    (.inr (.inl ⟨a, vs, s, j, ⟨1, rfl⟩, hv, rfl⟩))
  rw [hw, hv]
  rcases hc with ⟨-, rfl⟩ | ⟨h2, -⟩
  · rfl
  · have := h4 v (List.mem_of_getElem? hv)
    omega

end Roundtrip

private def w (n : Nat) : Value := .bits 32 (BitVec.ofNat 64 n)

-- `.16x32bx2` with offset 64 at column 8: the lower half-warp's thread 0 gets 7 and 9 back.
example (ws : List Value) (hok : LoadReadOk L1 [] (X (.s16x32bx2 64) 8 [w 7, w 9] ws))
    (hlen : ws.length = 2) : ws = [w 7, w 9] := by
  have h := fun j (hj : j < 2) => roundtrip hok hlen (by simp [w, Value.bytes])
    (fun j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      rcases j with _ | _ | j <;> first | decide | omega) (j := j) hj
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 2
  · exact h j hj
  · simp [List.getElem?_eq_none (by omega : ws.length ≤ j)]; omega

-- `.16x256b`: thread 0's four registers are lanes 0, 0, 8, 8; each comes back.
example (ws : List Value) (hok : LoadReadOk L1 [] (X .s16x256b 0 [w 1, w 2, w 3, w 4] ws))
    (hlen : ws.length = 4) : ws = [w 1, w 2, w 3, w 4] := by
  have h := fun j (hj : j < 4) => roundtrip hok hlen (by simp [w, Value.bytes])
    (fun j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      rcases j with _ | _ | _ | _ | j <;> first | decide | omega) (j := j) hj
  apply List.ext_getElem?
  intro j
  by_cases hj : j < 4
  · exact h j hj
  · simp [List.getElem?_eq_none (by omega : ws.length ≤ j)]; omega

-- The upper half-warp's thread 16 reads, in each register, the cell its own store wrote: at the
-- second access, 64 columns on.
example : tcDataCell L1 16 (.s16x32bx2 64) 8 1 = ⟨0, 0, 73⟩ := rfl

/-! ## Rejections -/

-- Columns outside the allocation: thread 16's half of a `.16x32bx2` store with offset 64 writes
-- columns 64 and 65, outside a 32-column allocation, so the access is unsafe.
private def own32 : Tmem.Pair.WarpRequest := ⟨0, 0, fun _ => 0, 0, some ⟨.shared, 0, 0⟩, .alloc 32⟩
def Y : Execution where
  tr g := if g = 0 then [⟨0, .tc (.resource .one own32.dst own32.request)⟩]
    else if g = 16 then [⟨1, .tc (.st 0 [w 7, w 9] (.s16x32bx2 64))⟩] else []
  rf _ _ := none
  tmemHistory cta := if cta = 0 then [⟨own32, .one, .alloc 32 0⟩] else []

example : Tmem.Pair.AccessUnsafe L1 Y := by
  intro h
  have hc : Tmem.Pair.Access L1 Y (16, 0) ⟨0, 0, 64⟩ :=
    .inr (.inr (.inl ⟨0, [w 7, w 9], _, 0, ⟨1, rfl⟩, by decide, rfl⟩))
  obtain ⟨cta, r, hr, n, base, he, -, -, hhi, -⟩ := (h _ _ hc).1
  by_cases h0 : cta = 0
  · subst h0
    simp only [Y, ↓reduceIte, List.mem_singleton] at hr
    subst hr
    cases he
    simp at hhi
  · simp [Y, h0] at hr

-- Lanes of one warp that disagree on the half-split offset of their `k`-th collective make the
-- execution unsafe (ERR-ALIGNED-MISMATCH compares the shape, offset included).
def Z : Execution where
  tr g := if g = 0 then [⟨5, .tc (.st 0 [w 7] (.s16x32bx2 64))⟩]
    else if g = 1 then [⟨5, .tc (.st 0 [w 7] (.s16x32bx2 32))⟩] else []
  rf _ _ := none

example (K : Kernel) : AlignedClass.tc.Divergent L1 K Z := by
  refine (AlignedClass.divergent_tc_iff L1).2 ⟨(0, 0), (1, 0), 0, 5, 5,
    .st 0 [w 7] (.s16x32bx2 64), .st 0 [w 7] (.s16x32bx2 32),
    ⟨⟨by simp [L1, Launch.threads], by simp [L1, Launch.threads], rfl⟩, rfl⟩,
    ⟨⟨_, rfl, rfl⟩, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl⟩, rfl, rfl, .inr (by simp [tcStatic])⟩

-- A lane that exits without the collective another lane of its warp performs: unsafe.
def W : Execution where
  tr g := if g = 0 then [⟨5, .tc (.ld 0 [w 7] .s16x64b)⟩]
    else if g = 1 then [⟨6, .exit⟩] else []
  rf _ _ := none

example (K : Kernel) : AlignedClass.tc.Exited L1 K W :=
  (AlignedClass.exited_tc_iff L1).2 ⟨(0, 0), (1, 0), 0,
    ⟨⟨by simp [L1, Launch.threads], by simp [L1, Launch.threads], rfl⟩, rfl⟩,
    ⟨⟨_, rfl, rfl⟩, rfl⟩, ⟨⟨6, rfl⟩, by decide⟩⟩

end
end PTX.Tests.TcShape
