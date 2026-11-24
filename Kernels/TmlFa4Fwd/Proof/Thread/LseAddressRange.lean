-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.WriteSpace
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Softmax (scoreEventWrites)

private abbrev auditBase : BitVec 64 := 274877906944
private abbrev auditStride : BitVec 64 := 274877906944

private def packedOffset (head : BitVec 64) (offset : BitVec 32) : BitVec 64 :=
  (head * auditStride + offset.signExtend 64) <<< 2

private def rowOffset (tile row : BitVec 32) : BitVec 64 :=
  ((tile.signExtend 64) ||| (row.zeroExtend 64)) <<< 2

private def low40 (x : BitVec 64) : Nat := x.toNat % 1099511627776

private theorem low40_add (x y : BitVec 64) :
    low40 (x + y) = (low40 x + low40 y) % 1099511627776 := by
  unfold low40
  rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ (by decide : 1099511627776 ∣ 2 ^ 64)]
  rw [Nat.add_mod_mod, Nat.mod_add_mod]

private theorem low40_mul (x y : BitVec 64) :
    low40 (x * y) = (x.toNat * y.toNat) % 1099511627776 := by
  unfold low40
  rw [BitVec.toNat_mul, Nat.mod_mod_of_dvd _ (by decide : 1099511627776 ∣ 2 ^ 64)]

private theorem low40_shift (x : BitVec 64) : low40 (x <<< 2) = (4 * low40 x) % 1099511627776 := by
  unfold low40
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_mod_of_dvd _ (by decide : 1099511627776 ∣ 2 ^ 64)]
  change (x.toNat * 4) % 1099511627776 = 4 * (x.toNat % 1099511627776) % 1099511627776
  rw [Nat.mul_comm x.toNat]
  omega

private theorem signBits (x : BitVec 32) :
    (x.signExtend 64).toNat =
      (if x.msb then 18446744069414584320 else 0) + x.toNat := by
  rw [BitVec.signExtend_eq_append_of_le (by decide : 32 ≤ 64)]
  rw [BitVec.toNat_cast, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt]
  cases x.msb <;> rfl

private theorem orSignBits (x y : BitVec 32) :
    ((x.signExtend 64) ||| (y.zeroExtend 64)).toNat =
      (if x.msb then 18446744069414584320 else 0) + (x.toNat ||| y.toNat) := by
  change ((x.signExtend 64) ||| (y.setWidth 64)).toNat = _
  rw [BitVec.toNat_or, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), signBits]
  cases x.msb
  · simp
  · simp only [↓reduceIte]
    have hx := x.isLt
    have hy := y.isLt
    have hxy := Nat.or_lt_two_pow hx hy
    have hPrefix (z : Nat) (hz : z < 2 ^ 32) :
        18446744069414584320 + z = 18446744069414584320 ||| z :=
      Nat.two_pow_add_eq_or_of_lt (i := 32) hz 4294967295
    rw [hPrefix _ hx, hPrefix _ hxy, Nat.or_assoc]

private theorem mul4Modulo (n : Nat) :
    4 * (n % 1099511627776) % 1099511627776 = 4 * n % 1099511627776 := by
  rw [Nat.mul_mod 4 (n % 1099511627776), Nat.mod_mod, ← Nat.mul_mod]

private theorem low40_packed (head : BitVec 64) (q : BitVec 32) :
    low40 (packedOffset head q) = (4 * (q.signExtend 64).toNat) % 1099511627776 := by
  rw [packedOffset, low40_shift, low40_add, low40_mul]
  unfold low40
  rw [Nat.add_mod_mod, Nat.mod_add_mod, mul4Modulo, Nat.mul_add]
  rw [show 4 * (head.toNat * auditStride.toNat) = 1099511627776 * head.toNat by
    change 4 * (head.toNat * 274877906944) = 1099511627776 * head.toNat
    omega]
  rw [Nat.mul_add_mod_self_left]

private theorem low40_row (tile row : BitVec 32) :
    low40 (rowOffset tile row) =
      (4 * ((tile.signExtend 64) ||| (row.zeroExtend 64)).toNat) % 1099511627776 := by
  rw [rowOffset, low40_shift, low40, mul4Modulo]

private theorem packedAddressLower (head : BitVec 64) (q tile row : BitVec 32)
    (stage : Bool) :
    137438953472 ≤ (auditBase + packedOffset head q + rowOffset tile row +
      (if stage then 512 else 0)).toNat := by
  let w := auditBase + packedOffset head q + rowOffset tile row + (if stage then 512 else 0)
  suffices 137438953472 ≤ low40 w from this.trans (Nat.mod_le ..)
  have hq := q.isLt
  have ht := Nat.or_lt_two_pow tile.isLt row.isLt
  change q.toNat < 4294967296 at hq
  change tile.toNat ||| row.toNat < 4294967296 at ht
  simp only [w, low40_add, low40_packed, low40_row]
  rw [show low40 auditBase = 274877906944 by decide]
  simp only [low40, signBits, orSignBits, Nat.add_mod_mod, Nat.mod_add_mod]
  rw [show (if stage then (512 : BitVec 64) else 0).toNat = if stage then 512 else 0 by
    cases stage <;> rfl]
  cases stage <;> cases q.msb <;> cases tile.msb <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem trunc64 (x : BitVec 64) : truncBits 64 x = x := by
  apply BitVec.eq_of_toNat_eq
  simp [truncBits, Nat.mod_eq_of_lt x.isLt]

private theorem readWord64 {l : Launch} {g r : Nat} {s : TState} {x : BitVec 64}
    (h : s.regs r = some (.bits 64 x)) : readBits l g s 64 (.reg r) = .ok x := by
  simp [readBits, readReg, h, trunc64, bind, Except.bind, pure, Except.pure]

private theorem signedWord (x : BitVec 64) :
    cvtIntBits false .s 64 .s 32 x = (x.truncate 32).signExtend 64 := by
  simp only [cvtIntBits, intSat, Bool.not_false, ↓reduceIte, intBits, trunc64]
  change BitVec.ofInt 64 (toSigned 32 x) = _
  have hs : (x.truncate 32).toInt = toSigned 32 x := by
    change (x.setWidth 32).toInt = toSigned 32 x
    rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_setWidth, toSigned]
    change Int.bmod (↑(x.toNat % 4294967296)) 4294967296 = _
    rw [Int.bmod_def]
    have h : x.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
    split <;> omega
  rw [← hs, ← BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64), BitVec.ofInt_toInt]

private theorem zeroWord (x : BitVec 64) :
    truncBits 32 x = (x.truncate 32).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  change (truncBits 32 x).toNat = ((x.setWidth 32).setWidth 64).toNat
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), BitVec.toNat_setWidth,
    truncBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt ((Nat.mod_lt _ (by decide)).trans (by decide))

private def wordCvt (signed : Bool) (dst src : Nat) : Op :=
  let ty := if signed then IType.s else IType.u
  .cvt { dst := .int ty 64, src := .int ty 32, rnd := none, d := dst, srcs := [.reg src] }

private def wordInt (op : IntOp) (ty : IType) (dst : Nat) (src : List Opnd) : Op :=
  .int ⟨op, .int ty 64, false, [some dst], src⟩

private theorem tauDecoded {l : Launch} {g : Nat} {s u : TState} {op : Op}
    (ht : Tau kernel Assumptions.all l g s u)
    (hc : kernel.code[s.pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hCore : Assumptions.coreOp op = true)
    (hf : s.fault = none) (hExp : s.pc ∉ Assumptions.swExp2Sites)
    (hLd : s.pc ∉ Assumptions.tcLdDataflowSites)
    (hTmem : s.pc ∉ Assumptions.delayedTmemSites) : execLocal l g s op = .ok u := by
  unfold Tau at ht
  rw [Assumptions.out_all_eq_nil hExp hLd hTmem hc hCore] at ht
  simp only [out, hf, hc, guardHolds, pure, Except.pure, hl, ↓reduceIte, execLocalA_nil] at ht
  cases h : execLocal l g s op with
  | error f => simp [h] at ht
  | ok t => simpa [h] using ht

private theorem readNarrow {l : Launch} {g r : Nat} {s : TState} {x : BitVec 64}
    (hr : readBits l g s 32 (.reg r) = .ok x) : truncBits 32 x = x := by
  simp only [readBits, bind, Except.bind] at hr
  cases hv : readReg s r with
  | error f => simp [hv] at hr
  | ok v =>
    rw [hv] at hr
    cases v <;> try first
      | cases hr
        exact truncBits_idem _ _
      | simp [throw, throwThe, MonadExceptOf.throw] at hr
    all_goals
      split at hr
      · cases hr
        exact truncBits_idem _ _
      · cases hr

private theorem rawCvt {l : Launch} {g d r : Nat} {s u : TState} {signed : Bool}
    (h : execLocal l g s (wordCvt signed d r) = .ok u) :
    (∃ x : BitVec 32, u = next (setReg s d
      (.bits 64 (if signed then x.signExtend 64 else x.zeroExtend 64)))) ∨
    (signed = false ∧ ∃ w generic sp off, u = next (setReg s d (.ptr w generic sp off))) := by
  let c (k : IType) : CvtInstr :=
    { dst := .int k 64, src := .int k 32, rnd := none, d := d, srcs := [.reg r] }
  cases signed
  · change execCvt l g s (c .u) = .ok u at h
    simp only [c, execCvt, readValue, bind, Except.bind] at h
    cases hReg : readReg s r with
    | error f => simp [hReg] at h
    | ok v =>
      rw [hReg] at h
      cases v <;> dsimp only at h
      case ptr =>
        simp only [show 64 ≠ 32 by decide, show 32 ≤ 64 by decide, true_or, false_or,
          true_and, and_true] at h
        split at h
        · exact .inr ⟨rfl, _, _, _, _, (Except.ok.inj h).symm⟩
        · cases h
      all_goals
        cases hb : readBits l g s 32 (.reg r) with
        | error f => rw [hb] at h; cases h
        | ok x =>
          simp only [hb, pure, Except.pure, trunc64] at h
          have hx := (readNarrow hb).symm.trans (zeroWord x)
          exact .inl ⟨x.truncate 32, hx ▸ (Except.ok.inj h).symm⟩
  · change execCvt l g s (c .s) = .ok u at h
    simp only [c, execCvt, readValue, bind, Except.bind] at h
    cases hReg : readReg s r with
    | error f => simp [hReg] at h
    | ok v =>
      rw [hReg] at h
      cases v <;> dsimp only at h
      case ptr => cases h
      all_goals
        cases hb : readBits l g s 32 (.reg r) with
        | error f => rw [hb] at h; cases h
        | ok x =>
          simp only [hb, pure, Except.pure, MemExt.extendBits, signedWord, trunc64] at h
          exact .inl ⟨x.truncate 32, (Except.ok.inj h).symm⟩

private theorem rawMad {l : Launch} {g : Nat} {s u : TState} {v : BitVec 64}
    (hq : s.regs 9522 = some (.bits 64 v))
    (hs : s.regs 7501 = some (.bits 64 auditStride))
    (h : execLocal l g s (wordInt (.mad .lo) .s 9523 [.reg 9605, .reg 7501, .reg 9522])
      = .ok u) :
    ∃ head : BitVec 64, u = next (setReg s 9523 (.bits 64 (head * auditStride + v))) := by
  change execInt l g s ⟨.mad .lo, .int .s 64, false, [some 9523], [.reg 9605, .reg 7501, .reg 9522]⟩
    = .ok u at h
  simp only [execInt, DType.width, readWord64 hs, readWord64 hq, trunc64,
    bind, Except.bind] at h
  cases hHead : readBits l g s 64 (.reg 9605) with
  | error f => simp [hHead] at h
  | ok x =>
    refine ⟨x, ?_⟩
    simpa [hHead, pure, Except.pure] using h.symm

private theorem rawShift {l : Launch} {g d r : Nat} {s u : TState} {x : BitVec 64}
    (hx : s.regs r = some (.bits 64 x))
    (h : execLocal l g s (wordInt .shl .b d [.reg r, .imm 2]) = .ok u) :
    u = next (setReg s d (.bits 64 (x <<< 2))) := by
  change execInt l g s ⟨.shl, .int .b 64, false, [some d], [.reg r, .imm 2]⟩
    = .ok u at h
  have hTwo : readBits l g s 32 (.imm 2) = .ok (2 : BitVec 64) := rfl
  simpa [execInt, DType.width, readWord64 hx, hTwo, trunc64, bind, Except.bind,
    pure, Except.pure] using h.symm

private theorem rawAdd {l : Launch} {g d a b : Nat} {s u : TState} {x y : BitVec 64}
    (hx : s.regs a = some (.bits 64 x)) (hy : s.regs b = some (.bits 64 y))
    (h : execLocal l g s (wordInt .add .s d [.reg a, .reg b]) = .ok u) :
    u = next (setReg s d (.bits 64 (x + y))) := by
  change execInt l g s ⟨.add, .int .s 64, false, [some d], [.reg a, .reg b]⟩
    = .ok u at h
  have ha : readReg s a = .ok (.bits 64 x) := by simp [readReg, hx, pure, Except.pure]
  have hb : readReg s b = .ok (.bits 64 y) := by simp [readReg, hy, pure, Except.pure]
  simpa [execInt, DType.width, readValue, ha, hb, readWord64 hx, readWord64 hy,
    trunc64, bind, Except.bind, pure, Except.pure] using h.symm

private theorem rawOr {l : Launch} {g : Nat} {s u : TState} {x : BitVec 64}
    (hx : s.regs 9527 = some (.bits 64 x))
    (hy : (∃ row : BitVec 32, s.regs 9526 = some (.bits 64 (row.zeroExtend 64))) ∨
      (∃ w generic sp off, s.regs 9526 = some (.ptr w generic sp off)))
    (h : execLocal l g s (wordInt .or .b 9528 [.reg 9527, .reg 9526]) = .ok u) :
    ∃ row : BitVec 32, u = next (setReg s 9528 (.bits 64 (x ||| row.zeroExtend 64))) := by
  change execInt l g s ⟨.or, .int .b 64, false, [some 9528], [.reg 9527, .reg 9526]⟩
    = .ok u at h
  rcases hy with ⟨row, hy⟩ | ⟨w, gen, sp, off, hy⟩
  · exact ⟨row, by
      simpa [execInt, DType.width, readWord64 hx, readWord64 hy, bind,
        Except.bind, pure, Except.pure] using h.symm⟩
  · have hPtr : readBits l g s 64 (.reg 9526) = .error .noRule := by
      simp [readBits, readReg, hy, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw]
    simp [execInt, DType.width, readWord64 hx, hPtr, bind, Except.bind] at h

private inductive RawCell where
  | start | headRow | packed | base | row | tile | within | delta | address
  deriving DecidableEq

private def rawCells : List RawCell :=
  [.start, .headRow, .packed, .base, .row, .tile, .within, .delta, .address]

private theorem RawCell.mem (c : RawCell) : c ∈ rawCells := by cases c <;> decide

private def RawCell.site : RawCell → Nat
  | .start => 9057
  | .headRow => 9058
  | .packed => 9059
  | .base => 9060
  | .row => 9067
  | .tile => 9068
  | .within => 9069
  | .delta => 9070
  | .address => 9071

private def RawCell.last : RawCell → Nat
  | .base => 9071
  | .row => 9069
  | .address => 9082
  | c => c.site + 1

private def RawCell.reg : RawCell → Nat
  | .start => 9522
  | .headRow => 9523
  | .packed => 9524
  | .base => 9525
  | .row => 9526
  | .tile => 9527
  | .within => 9528
  | .delta => 9529
  | .address => 7491

private def RawCell.op : RawCell → Op
  | .start => wordCvt true 9522 1634
  | .headRow => wordInt (.mad .lo) .s 9523 [.reg 9605, .reg 7501, .reg 9522]
  | .packed => wordInt .shl .b 9524 [.reg 9523, .imm 2]
  | .base => wordInt .add .s 9525 [.reg 7500, .reg 9524]
  | .row => wordCvt false 9526 1613
  | .tile => wordCvt true 9527 5967
  | .within => wordInt .or .b 9528 [.reg 9527, .reg 9526]
  | .delta => wordInt .shl .b 9529 [.reg 9528, .imm 2]
  | .address => wordInt .add .s 7491 [.reg 9525, .reg 9529]

private def RawCell.live (c : RawCell) (site : Nat) : Prop :=
  c.site < site ∧ site ≤ c.last

private instance (c : RawCell) (site : Nat) : Decidable (c.live site) := by
  unfold RawCell.live
  infer_instance

private def RawCell.words (c : RawCell) (s : TState) : Prop :=
  let word (x : BitVec 64) := s.regs c.reg = some (.bits 64 x)
  match c with
  | .start | .tile => ∃ x : BitVec 32, word (x.signExtend 64)
  | .headRow => ∃ (head : BitVec 64) (q : BitVec 32), word (head * auditStride + q.signExtend 64)
  | .packed => ∃ head q, word (packedOffset head q)
  | .base => ∃ head q, word (auditBase + packedOffset head q)
  | .row => (∃ x : BitVec 32, word (x.zeroExtend 64)) ∨
    (∃ w generic sp off, s.regs c.reg = some (.ptr w generic sp off))
  | .within => ∃ (tile row : BitVec 32), word (tile.signExtend 64 ||| row.zeroExtend 64)
  | .delta => ∃ tile row, word (rowOffset tile row)
  | .address => ∃ head q tile row, word (auditBase + packedOffset head q + rowOffset tile row)

private theorem RawCell.words_preserved (c : RawCell) {s u : TState}
    (hKeep : u.regs c.reg = s.regs c.reg) (h : c.words s) : c.words u := by
  cases c <;> simpa only [RawCell.words, hKeep] using h

private def RawAddressState (s : TState) : Prop :=
  s.regs 7500 = some (.bits 64 auditBase) ∧ s.regs 7501 = some (.bits 64 auditStride) ∧
  ∀ c : RawCell, c.live s.pc → c.words s

private theorem RawCell.code (c : RawCell) :
    kernel.code[c.site]? = some ⟨none, c.op⟩ := by
  cases c
  · exact Flow.code_9057
  · exact Flow.code_9058
  · exact Flow.code_9059
  · exact Flow.code_9060
  · exact Flow.code_9067
  · exact Flow.code_9068
  · exact Flow.code_9069
  · exact Flow.code_9070
  · exact Flow.code_9071

private theorem rawDefined {l : Launch} {g : Nat} {s u : TState} (c : RawCell)
    (hPc : s.pc = c.site) (hFrame : RawAddressState s)
    (h : execLocal l g s c.op = .ok u) : c.words u := by
  have hLive (before : RawCell) (hBefore : before.live c.site) : before.words s :=
    hFrame.2.2 _ (by rwa [hPc])
  cases c
  case start =>
    obtain ⟨v, rfl⟩ | ⟨hNo, _⟩ := rawCvt (signed := true) h
    · exact ⟨v, by simp [RawCell.reg, next, setReg]⟩
    · cases hNo
  case headRow =>
    obtain ⟨q, hq⟩ := hLive .start (by decide)
    obtain ⟨head, rfl⟩ := rawMad hq hFrame.2.1 h
    exact ⟨head, q, by simp [RawCell.reg, next, setReg]⟩
  case packed =>
    obtain ⟨head, q, hq⟩ := hLive .headRow (by decide)
    obtain rfl := rawShift hq h
    exact ⟨head, q, by simp [RawCell.reg, packedOffset, next, setReg]⟩
  case base =>
    obtain ⟨head, q, hq⟩ := hLive .packed (by decide)
    obtain rfl := rawAdd hFrame.1 hq h
    exact ⟨head, q, by simp [RawCell.reg, next, setReg]⟩
  case row =>
    obtain ⟨v, rfl⟩ | ⟨_, w, gen, sp, off, rfl⟩ := rawCvt (signed := false) h
    · exact .inl ⟨v, by simp [RawCell.reg, next, setReg]⟩
    · exact .inr ⟨w, gen, sp, off, by simp [RawCell.reg, next, setReg]⟩
  case tile =>
    obtain ⟨v, rfl⟩ | ⟨hNo, _⟩ := rawCvt (signed := true) h
    · exact ⟨v, by simp [RawCell.reg, next, setReg]⟩
    · cases hNo
  case within =>
    obtain ⟨tile, ht⟩ := hLive .tile (by decide)
    obtain ⟨row, rfl⟩ := rawOr ht (hLive .row (by decide)) h
    exact ⟨tile, row, by simp [RawCell.reg, next, setReg]⟩
  case delta =>
    obtain ⟨tile, row, ht⟩ := hLive .within (by decide)
    obtain rfl := rawShift ht h
    exact ⟨tile, row, by simp [RawCell.reg, rowOffset, next, setReg]⟩
  case address =>
    obtain ⟨head, q, hq⟩ := hLive .base (by decide)
    obtain ⟨tile, row, ht⟩ := hLive .delta (by decide)
    obtain rfl := rawAdd hq ht h
    exact ⟨head, q, tile, row, by simp [RawCell.reg, next, setReg]⟩

private def rawWrites (ins : Instr) : List Nat :=
  writesRegs ins.op ++ scoreEventWrites ins.op

private def rawAudit (site : Nat) (ins : Instr) : Bool :=
  (ins.op.isLocal || correctionReturningOp ins.op) &&
    [7500, 7501].all (fun r => !(rawWrites ins).contains r) &&
    rawCells.all (fun c => site == c.site || !(rawWrites ins).contains c.reg) &&
    match ins.op with
    | .bra target _ => rawCells.all (fun c => !decide (c.live target) || decide (c.live site))
    | .brx .. => false
    | _ => true

private theorem rawAuditAt {site : Nat} {ins : Instr}
    (hLo : 7745 ≤ site) (hHi : site < 9205) (hc : kernel.code[site]? = some ins) :
    rawAudit site ins = true := by
  let code := ((kernel.code.drop 7745).take (9205 - 7745)).zipIdx 7745
  have hAll : code.all (fun (i, site) => rawAudit site i) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (ins, site)
  apply List.mem_of_getElem? (i := site - 7745)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem rawAddressStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 7745 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3)
    (hS : RawAddressState s) (hw : WStep kernel Assumptions.all l g s e u) :
    RawAddressState u := by
  have finish {ins : Instr} (hCode : rawAudit s.pc ins = true)
      (hKeep : ∀ r ∉ rawWrites ins, u.regs r = s.regs r)
      (hEntry : ∀ c : RawCell, c.live u.pc → s.pc = c.site ∨ c.live s.pc)
      (hNew : ∀ c : RawCell, s.pc = c.site → c.words u) : RawAddressState u := by
    simp only [rawAudit, Bool.and_eq_true] at hCode
    have hAbi (r : Nat) (hr : r ∈ [7500, 7501]) : r ∉ rawWrites ins := by
      simpa using List.all_eq_true.mp hCode.1.1.2 _ hr
    refine ⟨(hKeep _ (hAbi _ (by decide))).trans hS.1,
      (hKeep _ (hAbi _ (by decide))).trans hS.2.1, ?_⟩
    intro c hLive
    by_cases hPc : s.pc = c.site
    · exact hNew c hPc
    · have hReg : c.reg ∉ rawWrites ins := by
        simpa [hPc] using List.all_eq_true.mp hCode.1.2 c c.mem
      exact c.words_preserved (hKeep _ hReg) (hS.2.2 _ ((hEntry c hLive).resolve_left hPc))
  have advance (hPc : u.pc = s.pc + 1) (c : RawCell) (hLive : c.live u.pc) :
      s.pc = c.site ∨ c.live s.pc := by
    unfold RawCell.live at hLive ⊢
    omega
  rcases hw with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have hNot : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨ins, hc, hf, hFrame⟩ := correctionTauFrame hNot ht
    have hAudit := rawAuditAt hLo hHi hc
    have hNew (c : RawCell) (hp : s.pc = c.site) : c.words u := by
      have hDecoded := hp.symm ▸ c.code
      apply rawDefined c hp hS
      apply tauDecoded ht hDecoded (by cases c <;> rfl) (by cases c <;> rfl) hf hNot
      · rw [hp]; cases c <;> decide
      · rw [hp]; cases c <;> decide
    rcases hFrame with ⟨rfl, _⟩ | ⟨_, _, hFrame⟩
    · exact finish hAudit (fun _ _ => rfl) (advance rfl) hNew
    · have hPc := hFrame.pc
      have hn : ∀ (c : RawCell), c.live u.pc → s.pc = c.site ∨ c.live s.pc := by
        intro c hLive
        cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
        case bra t _ =>
          have h := hAudit
          simp only [rawAudit, hop, Bool.and_eq_true] at h
          have hBranch := List.all_eq_true.mp h.2 c c.mem
          rw [hPc] at hLive
          exact .inr (by simpa [hLive] using hBranch)
        case brx => simp [rawAudit, hop] at hAudit
        all_goals exact advance hPc c hLive
      exact finish hAudit (fun r hr => hFrame.regs r (fun h => hr (List.mem_append_left _ h)))
        hn hNew
  · obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source he
    have hAudit := rawAuditAt hLo hHi hc
    have hPlan : correctionReturningOp ins.op = true := by
      have h := hAudit
      simp only [rawAudit, Bool.and_eq_true, hLocal, Bool.false_or] at h
      exact h.1.1.1
    have hPres {r : Nat} (hr : r ∉ rawWrites ins) :=
      correctionEventProgress (r := r) hc hPlan hSub (fun h => hr (List.mem_append_right _ h)) he
    have hPc := (hPres (r := 7500) (by
      have h := hAudit
      simp only [rawAudit, Bool.and_eq_true] at h
      simpa using List.all_eq_true.mp h.1.1.2 7500 (by decide))).1.pc
    apply finish hAudit (fun _ hr => (hPres hr).2)
    · intro c hLive
      rcases hPc with ⟨h, _⟩ | ⟨h, _⟩
      · exact advance h c hLive
      · exact .inr (h ▸ hLive)
    · intro c hEq
      have hDecode := hEq.symm ▸ c.code
      obtain rfl := Option.some.inj (hDecode.symm.trans hc)
      cases c <;> cases hLocal

private theorem storeAddressLower {l : Launch} {g : Nat} {s : TState} {o : Option TState}
    {a : Acc} {bytes : List Byte} {w : BitVec 64} {pc src : Nat}
    (stage : Bool) (hReg : s.regs 7491 = some (.bits 64 w))
    (hLow : 137438953472 ≤ (w + (if stage then 512 else 0)).toNat)
    (hf : Fires s.pc (storeTmpl l g s .global 32 7491 (if stage then 512 else 0) [.reg src])
      ⟨pc, .wr a bytes⟩ o) : 137438953472 ≤ a.loc.addr := by
  rcases fires_write_tmpl hf with ⟨u, hStore⟩ | ⟨u, hStore, _⟩ <;>
    unfold storeTmpl at hStore
  all_goals
    have hEff : effAddr l g s .global 7491 (if stage then 512 else 0) =
        .ok (globalLoc (w + (if stage then 512 else 0)).toNat) := by
      cases stage <;> simp [effAddr, readWord64 hReg, bind, Except.bind, pure, Except.pure,
        globalLoc]
    simp only [hEff, bind, Except.bind, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceDiv] at hStore
  · cases ha : elemAcc (globalLoc (w + (if stage then 512 else 0)).toNat) 4 1 s.sub with
    | error f => rw [ha] at hStore; cases hStore
    | ok b =>
      rw [ha] at hStore
      dsimp only at hStore
      split at hStore
      · cases hStore
      · split at hStore
        · cases hStore
        · obtain ⟨rfl, _, _⟩ := Tmpl.write.inj hStore
          let base := globalLoc (w + (if stage then 512 else 0)).toNat
          change elemAcc base 4 1 s.sub = .ok b at ha
          unfold elemAcc at ha
          by_cases hBad : 4 = 0 ∨ base.addr % (4 * 1) ≠ 0
          · rw [ite_eq_left hBad] at ha
            cases ha
          · rw [ite_eq_right hBad] at ha
            cases ha
            change _ ≤ (w + (if stage then 512 else 0)).toNat + 4 * s.sub
            omega
  · split at hStore
    · cases hStore
    · split at hStore
      · cases hStore
      · split at hStore <;> cases hStore

/-- With this launch's ABI constants the correction's scalar global stores stay above the
metadata even if the scheduler reads different 32-bit values. -/
theorem lseWriteAddressLower {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hBase : p.lseBase = 274877906944) (hStride : p.lseStride = 274877906944)
    {w : EvId} {a : Acc} {bytes : List Byte} (he : X.Writes w a bytes)
    (hGlobal : a.loc.space = .global) : 137438953472 ≤ a.loc.addr := by
  obtain ⟨g, j⟩ := w
  obtain ⟨pc, hGet⟩ := he
  have hMem : X.MemWrites (.thread (g, j)) a bytes := Or.inl ⟨pc, hGet⟩
  obtain ⟨i, site, hRef, hSite, hWrite⟩ | ⟨i, x, y, k, site, addr, spec, hRef, _⟩ :=
    globalWriteSources hX hMem hGlobal
  swap
  · cases hRef
  obtain rfl := AsyncCopy.Ref.thread.inj hRef
  have hEq := Event.mk.inj (Option.some.inj (hGet.symm.trans hWrite))
  obtain rfl := hEq.1
  simp only [lseStoreSites, List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hLate : 173 < pc := by omega
  have hEnd : pc < 9205 := by omega
  have hRole := roleBodyPcOfEvent hp hX hGet hLate
    (by simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]; omega)
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    change roleBodyPc (warpIndex l g) pc at hRole
    unfold roleBodyPc at hRole
    split_ifs at hRole <;> omega
  have hInit (t : TState)
      (ht : At t 7745 ((1072, b32 (g / l.block)) :: nonzeroBarrierFacts p l g)) :
      RawAddressState t := by
    have hAbi := ht.2.2.2.2
    refine ⟨?_, ?_, fun c h => ?_⟩
    · have hh := holds_lookup (r := 7500) (v := b64 p.lseBase) hAbi rfl
      simpa [b64, hBase] using hh
    · have hh := holds_lookup (r := 7501) (v := b64 p.lseStride) hAbi rfl
      simpa [b64, hStride] using hh
    · rw [ht.1] at h
      cases c <;> exact ((by decide : ¬ RawCell.live _ 7745) h).elim
  obtain ⟨s, o, hPc, _, hFrame, hStep⟩ :=
    correctionRoleEventWith hp hX hWarp.1 hWarp.2 hGet hLate hEnd hInit rawAddressStep
  change s.pc = pc at hPc
  have hLive : RawCell.address.live s.pc := by
    rw [hPc]
    change 9071 < pc ∧ pc ≤ 9082
    omega
  obtain ⟨head, q, tile, row, hReg⟩ := hFrame.2.2 .address hLive
  obtain ⟨tm, ht, hf⟩ := hStep
  rcases out_ev ht with ⟨fault, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hf.1
  rcases hSite with rfl | rfl
  · rw [hPc, Flow.code_9073] at hc
    obtain rfl := Option.some.inj hc
    exact storeAddressLower false hReg (packedAddressLower head q tile row false) hf
  · rw [hPc, Flow.code_9082] at hc
    obtain rfl := Option.some.inj hc
    exact storeAddressLower true hReg (packedAddressLower head q tile row true) hf

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
