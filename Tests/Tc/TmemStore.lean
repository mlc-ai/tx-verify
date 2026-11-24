-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Lemmas.Tmem.TmemStore
public import Lemmas.Tcgen05.TcGroup
public import Lemmas.Order.OrderBaseCausality

/-! `tcgen05.st` (DEP-TMEM-STORE-VALUE): decoding, the warp lane rule, the cells and values a
store writes, completion by `wait::st` or by the st→ld/st→st pipeline, and stores as
writers in the stability and conflict rules. -/
namespace PTX.Tests.TmemStore
open TcMma
noncomputable section

/-! ## Decoding and issue -/

private def env : Decode.Env := { classes := [⟨"r".toList, 8, 32⟩], labels := [], params := [] }

example : Decode.op env "tcgen05.st.sync.aligned.32x32b.x2.b32"
    [.address [.register "r0"], .vector [.register "r1", .register "r2"]] =
    .ok (.tcSt 0 [.reg 1, .reg 2] .s32x32b) := rfl
example : Decode.op env "tcgen05.wait::st.sync.aligned" [] = .ok .tcWaitSt := rfl
-- The shape suffix must match the vector length.
example : (Decode.op env "tcgen05.st.sync.aligned.32x32b.x4.b32"
    [.address [.register "r0"], .vector [.register "r1", .register "r2"]]).toOption = none := rfl
-- `.unpack::16b` decodes to the packed shape (THREAD-TC-PACK16).
example : Decode.op env "tcgen05.st.sync.aligned.32x32b.x2.unpack::16b.b32"
    [.address [.register "r0"], .vector [.register "r1", .register "r2"]] =
    .ok (.tcSt 0 [.reg 1, .reg 2] (.packed16 .s32x32b)) := rfl

private def launch : Launch := { grid := 1, block := 64, params := fun _ => none, clusterSize := 1 }
private def st (lane : Nat) : TState := { regs := fun
  | 0 => some (.bits 32 (BitVec.ofNat 64 (lane * 2 ^ 16 + 8)))
  | 1 => some (.bits 32 (BitVec.ofNat 64 7))
  | 2 => some (.bits 32 (BitVec.ofNat 64 9))
  | _ => none }
private def stOp : Op := .tcSt 0 [.reg 1, .reg 2]

-- The register values are read at issue; the event carries them and the address.
example : tcTmpl launch 3 (st 0) stOp =
    .tc (.st 8 [.bits 32 (BitVec.ofNat 64 7), .bits 32 (BitVec.ofNat 64 9)] .s32x32b)
      (next (st 0)) := rfl
example : eventTmpl [] launch 40 (st 32) stOp =
    .tc (.st (32 * 2 ^ 16 + 8) [.bits 32 (BitVec.ofNat 64 7), .bits 32 (BitVec.ofNat 64 9)]
      .s32x32b)
      (next (st 32)) := rfl
-- Raw row zero selects local row zero of warp 1's physical lanes 32–63.
example : tcTmpl launch 40 (st 0) stOp =
    .tc (.st 8 [.bits 32 (BitVec.ofNat 64 7), .bits 32 (BitVec.ofNat 64 9)] .s32x32b)
      (next (st 0)) := rfl
-- The lane field of warp 1 (EXT-TMEM-LANE-FIELD): 0 (relative) and 32 (absolute) stay in
-- lanes 32–63; 16 runs a 32-lane access past the chunk, 64 names warp 2's lanes.
example : tcDataAddressOk launch 40 .s32x32b (0 * 2 ^ 16 + 8) = true := rfl
example : tcDataAddressOk launch 40 .s32x32b (32 * 2 ^ 16 + 8) = true := rfl
example : tcDataAddressOk launch 40 .s32x32b (16 * 2 ^ 16 + 8) = false := rfl
example : tcDataAddressOk launch 40 .s32x32b (64 * 2 ^ 16 + 8) = false := rfl
example : tcTmpl launch 40 (st 16) stOp = .ub .noRule := rfl
example : tcTmpl launch 40 (st 64) stOp = .ub .noRule := rfl
-- A 16-lane access by warp 1 may start at relative lane 16 or absolute lane 48, not 56.
example : tmemLaneFieldOk launch 40 16 16 = true := rfl
example : tmemLaneFieldOk launch 40 48 16 = true := rfl
example : tmemLaneFieldOk launch 40 56 16 = false := rfl
-- An access of no lanes is not accepted: the two readings of field 32 would start at 64 and 32.
example : tmemLaneFieldOk launch 40 32 0 = false := rfl
example : ¬ (32 + 1 ≤ 32 ∧ laneBase launch 40 ≤ 32) := tmemLaneField_disjoint (by decide) (by
    decide)
-- Three registers is not a .32x32b shape.
example : tcTmpl launch 3 (st 0) (.tcSt 0 [.reg 1, .reg 1, .reg 1]) = .ub .noRule := rfl
-- Sources are read as data movement (`readValue`, as `st.shared`): a packed pair of f16 payloads
-- is stored unchanged, and a value that is not 4 bytes wide is a type mismatch.
private def stF (x y : ℝ) : TState := { regs := fun
  | 0 => some (.bits 32 (BitVec.ofNat 64 8))
  | 1 => some (.pair (.float .f16 x) (.float .f16 y))
  | 2 => some (.bits 64 (BitVec.ofNat 64 9))
  | _ => none }
example (x y : ℝ) : tcTmpl launch 3 (stF x y) (.tcSt 0 [.reg 1]) =
    .tc (.st 8 [.pair (.float .f16 x) (.float .f16 y)] .s32x32b) (next (stF x y)) := rfl
example (x y : ℝ) : tcTmpl launch 3 (stF x y) (.tcSt 0 [.reg 2]) = .ub .typeMismatch := rfl
example : tcTmpl launch 3 (st 0) .tcWaitSt = .tc .waitSt (next (st 0)) := rfl
example : stOp.isLocal = false := rfl
example : isTcColl ⟨0, .tc (.st 0 [] .s32x32b)⟩ = true := rfl

/-! ## Cells, values and completion -/

private def w7 : Value := .bits 32 (BitVec.ofNat 64 7)
private def w9 : Value := .bits 32 (BitVec.ofNat 64 9)

-- Thread 0 stores, then loads the same cells without waiting; thread 1 (same warp) stores
-- and waits; thread 32 (warp 1) stores to its own lanes.
def X : Execution where
  tr := fun g =>
    if g = 0 then [⟨0, .tc (.st 8 [w7, w9] .s32x32b)⟩, ⟨1, .tc (.ld 8 [w7, w9] .s32x32b)⟩]
    else if g = 1 then [⟨0, .tc (.st 8 [w9] .s32x32b)⟩, ⟨2, .tc .waitSt⟩, ⟨3, .exit⟩]
    else if g = 32 then [⟨0, .tc (.st (32 * 2 ^ 16) [w7] .s32x32b)⟩]
    else []
  rf := fun _ _ => none

private theorem po' {g i j : Nat} (hij : i < j) (hj : j < (X.tr g).length) :
    baseCausality launch X (g, i) (g, j) :=
  .single (.inl (po_of_not_access rfl hij hj (by
    simp only [Execution.get, X]
    split_ifs <;> rcases j with _ | _ | _ | j <;> simp [Event.acc])))

-- Register slot j uses its warp's physical lane chunk and the selected column.
example : StoreCell launch X (0, 0) ⟨0, 0, 9⟩ := ⟨8, [w7, w9], _, 1, ⟨0, rfl⟩, by decide, rfl⟩
example : StoreValue launch X (0, 0) ⟨0, 0, 9⟩ w9 := ⟨8, [w7, w9], _, 1, ⟨0, rfl⟩, rfl, rfl⟩
example : StoreCell launch X (1, 0) ⟨0, 1, 8⟩ := ⟨8, [w9], _, 0, ⟨0, rfl⟩, by decide, rfl⟩
example : StoreCell launch X (32, 0) ⟨0, 32, 0⟩ :=
  ⟨32 * 2 ^ 16, [w7], _, 0, ⟨0, rfl⟩, by decide, rfl⟩
-- Past the register count there is no cell.
example : ¬ StoreCell launch X (0, 0) ⟨0, 0, 10⟩ := by
  rintro ⟨a, vals, sh, j, ⟨pc, h⟩, hj, hc⟩
  simp [Execution.get, X] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  simp at hj
  simp [tcDataCell_s32x32b, tcDataCell32, laneBase, laneOf, launch] at hc
  omega

-- st→ld in the same thread is pipelined: no wait::st is needed before the load.
example : StoreDoneBefore launch X (0, 0) (0, 1) :=
  ⟨⟨8, [w7, w9], .s32x32b, ⟨0, rfl⟩⟩, .inr (.inl ⟨by simp [SameWarp, SameCta, launch,
    Launch.threads], .inl (po' (by decide) (by decide)), ⟨8, [w7, w9], .s32x32b, ⟨0, rfl⟩⟩,
    ⟨8, [w7, w9], .s32x32b, ⟨1, rfl⟩⟩⟩)⟩
-- Thread 1's store completes by its own wait::st, before its exit.
example : WaitBefore launch X .waitSt (1, 0) (1, 2) :=
  ⟨(1, 1), ⟨2, rfl⟩, rfl, by decide, .inl (po' (by decide) (by decide))⟩
-- Without a wait::st, thread 32's store is not completed before anything of its thread.
example (e : EvId) : ¬ WaitBefore launch X .waitSt (32, 0) e := by
  rintro ⟨w, ⟨pc, h⟩, hw, hlt, -⟩
  obtain ⟨g, i⟩ := w
  simp only at hw; subst hw
  cases i <;> simp [Execution.get, X] at h hlt

/-! ## Accumulating onto a stored D

Thread 0 initializes D[0][0] with `tcgen05.st` (5), waits with `wait::st`, then issues an
accumulating kind::i8 MMA with A = 1, B = 2: the derived result is 5 + 32 * 2 = 69. -/

private def k8 : TcShared.Descriptor := ⟨1024, 128, 256, 0, false, false, .none⟩
private def int8 (v : Int) : Option Byte := some (.bits 8 (BitVec.ofInt 64 v), 0)
private def i8x1 : Descriptor := ⟨.one, .i8 true true false, 128, 8, false, false, false, false,
    false⟩
private def spec1 : OperandSpec := ⟨i8x1, k8, k8, 0, 0, none, {}⟩
private def masks : List Nat := [0, 0, 0, 0]
private def w5 : Value := .bits 32 (BitVec.ofNat 64 5)
private def ops : AsyncCopy.MmaOperands :=
  ⟨List.replicate 4096 (int8 1), List.replicate 256 (int8 2)⟩

def Y : Execution where
  tr := fun g => if g = 0 then
      [⟨0, .tc (.st 0 [w5] .s32x32b)⟩, ⟨1, .tc .waitSt⟩, ⟨2, .tc (.mma 0 spec1 true masks)⟩]
    else []
  rf := fun _ _ => none
  async := { mmaOperands := fun i => if i = (0, 2) then some ops else none }

private def L1 : Launch := { grid := 1, block := 32, params := fun _ => none, clusterSize := 1 }

private theorem events {e : EvId} {ev : Event} (h : Y.get e = some ev) :
    e = (0, 0) ∨ e = (0, 1) ∨ e = (0, 2) := by
  obtain ⟨g, i⟩ := e
  by_cases hg : g = 0
  · subst hg
    match i with
    | 0 => exact .inl rfl
    | 1 => exact .inr (.inl rfl)
    | 2 => exact .inr (.inr rfl)
    | _ + 3 => simp [Execution.get, Y] at h
  · simp [Execution.get, Y, hg] at h

private theorem writes (other : EvId) (cell : Cell) (h : TmemWrite L1 Y other cell) :
    other = (0, 0) ∨ other = (0, 2) := by
  rcases h with ⟨_, _, _, _, _, _, ⟨pc, hp⟩, -⟩ | ⟨_, _, _, _, ⟨pc, hp⟩, -, -⟩ |
    ⟨_, _, _, _, hcp, -, -, -⟩ | ⟨_, ⟨pc, hp⟩, -⟩
  all_goals
    first
    | rcases events hp with rfl | rfl | rfl
      · exact .inl rfl
      · simp [Execution.get, Y] at hp
      · exact .inr rfl
    | obtain ⟨pc, hp⟩ := hcp
      rcases events hp with rfl | rfl | rfl
      · exact .inl rfl
      · simp [Execution.get, Y] at hp
      · exact .inr rfl

private theorem source : ReadSource L1 Y .acc (0, 0) (0, 2) ⟨0, 0, 0⟩ := by
  refine ⟨by decide, .inr (.inl ⟨0, [w5], _, 0, ⟨0, rfl⟩, by decide, rfl⟩),
    .inr (.inl ⟨⟨_, _, _, ⟨0, rfl⟩⟩, .inl ⟨(0, 1), ⟨1, rfl⟩, rfl, by decide,
      .inl (.single (.inl ⟨rfl, by decide, by decide⟩))⟩⟩), ?_, ?_⟩
  · intro other ho
    rcases writes other _ ho with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inl rfl))
  · intro key r hr
    simp [Y] at hr

-- The stored word is a valid old D; the derived value includes it.
example : Result L1 [] Y (0, 2) ⟨0, 0, 0⟩ (.bits 32 (BitVec.ofNat 64 69)) :=
  .accumulateStored (row := 0) (col := 0) (operands := ops) ⟨2, rfl⟩ (by decide) (by simp [Y])
    ⟨0, [w5], .s32x32b, 0, ⟨0, rfl⟩, rfl, rfl⟩ source rfl

-- Without the wait::st, the store is not ordered before the MMA (st→mma is not a pipeline).
def Z : Execution where
  tr := fun g =>
    if g = 0 then [⟨0, .tc (.st 0 [w5] .s32x32b)⟩, ⟨2, .tc (.mma 0 spec1 true masks)⟩] else []
  rf := fun _ _ => none

example : ¬ WriteBefore L1 Z (0, 0) (0, 1) := by
  have hnoWait : ∀ e, ¬ WaitBefore L1 Z .waitSt (0, 0) e := by
    rintro e ⟨w, ⟨pc, h⟩, hw, -, -⟩
    obtain ⟨g, i⟩ := w
    simp only at hw; subst hw
    match i with
    | 0 | 1 => simp [Execution.get, Z] at h
    | _ + 2 => simp [Execution.get, Z] at h
  have hnoSt : ∀ a vals sh, ¬ Z.TSt (0, 1) a vals sh := by
    rintro a vals sh ⟨pc, h⟩
    simp [Execution.get, Z] at h
  have hnoLd : ∀ a vals sh, ¬ Z.TLd (0, 1) a vals sh := by
    rintro a vals sh ⟨pc, h⟩
    simp [Execution.get, Z] at h
  have hnoCp : ∀ c, ¬ Z.CpIssue (0, 0) c := by
    rintro c ⟨pc, h⟩
    simp [Execution.get, Z] at h
  have hnoMma : ∀ d s accum mask, ¬ Z.MmaIssue (0, 0) d s accum mask := by
    rintro d s accum mask ⟨pc, h⟩
    simp [Execution.get, Z] at h
  have hnoShift : ∀ s, ¬ Z.ShiftIssue (0, 0) s := by
    rintro s ⟨pc, h⟩
    simp [Execution.get, Z] at h
  -- A completion of `(0, 0)`'s asynchronous part needs an MMA or a copy there.
  have hnoNotifies : ∀ n m, ¬ AsyncCopy.Notifies Z (0, 0) .mmaDone n m := by
    rintro n m ⟨commit, cs, rank, -, htrack, -, -, -⟩
    obtain ⟨-, -, htc, -⟩ := htrack
    rcases htc with ⟨d, s, accum, mask, him⟩ | ⟨c, hcp⟩ | ⟨sh, hsh⟩
    · exact hnoMma d s accum mask him
    · exact hnoCp c hcp
    · exact hnoShift sh hsh
  rintro (hbefore | hstore | hcpPipe)
  · rcases hbefore with hdone | hpipe
    · rcases hdone with ⟨w, ws, hobs, -, -⟩ | ⟨w, hco, hasync⟩
      · obtain ⟨n, m, hn, -⟩ := hobs
        exact hnoNotifies n m hn
      · obtain ⟨acq, ws, hobs, -⟩ := hco
        obtain ⟨n, m, hn, -⟩ := hobs
        exact hnoNotifies n m hn
    · obtain ⟨-, htc, d, s, accum, mask, -, -, -, -, him, -, -⟩ := hpipe
      exact hnoMma d s accum mask him
  · obtain ⟨-, hrest⟩ := hstore
    rcases hrest with hwait | hpipLd | hpipSt
    · exact hnoWait _ hwait
    · obtain ⟨-, -, -, hld⟩ := hpipLd
      obtain ⟨address, vals, shape, ht⟩ := hld
      exact hnoLd address vals shape ht
    · obtain ⟨-, -, -, hst⟩ := hpipSt
      obtain ⟨address, vals, shape, ht⟩ := hst
      exact hnoSt address vals shape ht
  · obtain ⟨-, -, c, -, -, -, -, hcp, -, -, -⟩ := hcpPipe
    exact hnoCp c hcp

end
end PTX.Tests.TmemStore
