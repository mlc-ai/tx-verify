-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Tc.TcMmaSafety

/-! The `tcgen05.mma` qualifiers of PROG-ISA-TC-MMA: decoding of every qualifier, the forms
`TcMmaInstr.rule` gives a rule, `kind::f8f6f4` descriptors (THREAD-TC-MMA-DESCRIPTOR), the
zero-column mask (THREAD-TC) and the collector buffer rule (ERR-TC-COLLECTOR-REUSE). -/
namespace PTX.Tests.TcMmaQualifiers
open TcMma
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 4, 32⟩, ⟨"rd".toList, 2, 64⟩, ⟨"p".toList, 1, 1⟩], labels := [],
      params := [] }

/-- The rule of a decoded instruction; `none` for a decoding error. -/
private def ruleOf : Except String Op → Option (Option RuleId)
  | .ok op => some op.rule
  | .error _ => none

/-! ## Decoding -/

private def collectorAB : TcMmaInstr :=
  { group := .one, kind := .f16, d := 0, a := .smem (.reg 4), bdesc := .reg 5,
    idesc := .reg 1, mask := List.replicate 4 (.imm 0), enableD := .reg 6,
    collectorA := .fill, collectorB := .use }

private def wsZcm : TcMmaInstr :=
  { group := .one, ws := true, kind := .i8, d := 0, a := .tmem 2 0,
    bdesc := .reg 5, idesc := .reg 1, mask := List.replicate 4 (.imm 0), enableD := .reg 6,
    zeroColumnMask := some (.reg 4), collectorB := .use, bBuffer := 2 }

private def scaled : TcMmaInstr :=
  { group := .one, kind := .mxf8f6f4, d := 0, a := .smem (.reg 4),
    bdesc := .reg 5, idesc := .reg 1, mask := List.replicate 4 (.imm 0), enableD := .reg 6,
    scale := some { vec := some .x1, sfa := (2, 0), sfb := (3, 0) } }

private def lastuse : TcMmaInstr :=
  { group := .one, kind := .f16, d := 0, a := .smem (.reg 4),
    bdesc := .reg 5, idesc := .reg 1, mask := [], enableD := .imm 1, collectorA := .lastuse }

-- Collector usage of A and B, without a lane mask.
example : Decode.op env "tcgen05.mma.cta_group::1.kind::f16.collector::a::fill.collector::b::use"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .register "p0"] =
    .ok (.tcMma collectorAB) := rfl
-- The D address `[r + 0]` is `[r]`; a non-zero offset is rejected.
example : Decode.op env "tcgen05.mma.cta_group::1.kind::f16.collector::a::fill.collector::b::use"
    [.address [.offset "+" (.register "r0") (.literal "0")], .register "rd0", .register "rd1",
      .register "r1", .register "p0"] =
    .ok (.tcMma collectorAB) := rfl
example : (Decode.op env "tcgen05.mma.cta_group::1.kind::f16"
    [.address [.offset "+" (.register "r0") (.literal "4")], .register "rd0", .register "rd1",
      .register "r1", .register "p0"]).isOk = false := rfl
-- `.ws` with B buffer 2, A in Tensor Memory and a zero-column mask.
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::i8.collector::b2::use"
    [.address [.register "r0"], .address [.register "r2"], .register "rd1", .register "r1",
      .register "p0", .register "rd0"] =
    .ok (.tcMma wsZcm) := rfl
-- A form without qualifiers is the dense form.
example : Decode.op env "tcgen05.mma.cta_group::1.kind::f8f6f4"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .register "p0"] =
    .ok (.tcMma (.dense .one false .f8f6f4 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6))) := rfl
-- Block scaling records the scale-vector qualifier and the scale factor addresses.
example : Decode.op env "tcgen05.mma.cta_group::1.kind::mxf8f6f4.block_scale.scale_vec::1X"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .address [.register "r2"], .address [.register "r3"], .register "p0"] =
    .ok (.tcMma scaled) := rfl

/-! ## Rules -/

-- Dense f8f6f4, collector usage and the `.ws` zero-column mask have THREAD-TC.
example : ruleOf (Decode.op env "tcgen05.mma.cta_group::1.kind::f8f6f4"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .register "p0"]) = some (some .threadTc) := rfl
example : ruleOf (Decode.op env "tcgen05.mma.ws.cta_group::1.kind::i8.collector::b2::use"
    [.address [.register "r0"], .address [.register "r2"], .register "rd1", .register "r1",
      .register "p0", .register "rd0"]) = some (some .threadTc) := rfl
-- Block scaling, sparsity, `kind::ti16` and the lookup table decode without a rule.
example : ruleOf (Decode.op env "tcgen05.mma.cta_group::1.kind::mxf8f6f4.block_scale.scale_vec::1X"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .address [.register "r2"], .address [.register "r3"], .register "p0"]) = some none := rfl
example : ruleOf (Decode.op env "tcgen05.mma.sp.cta_group::1.kind::ti16"
    [.address [.register "r0"], .register "rd0", .register "rd1", .address [.register "r2"],
      .register "r1", .register "p0"]) = some none := rfl
example : ruleOf (Decode.op env "tcgen05.mma.cta_group::1.kind::ti16"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .register "p0"]) = some none := rfl
-- At execution a form without a rule is `ub noRule`.
example (L : Launch) (g : Nat) (t : TState) (m : TcMmaInstr) (h : m.rule = none) :
    eventTmpl [] L g t (.tcMma m) = .ub .noRule := by
  rw [eventTmpl_rule]; simp [Op.rule, h]
-- The former constructors issue as before (per-form lemmas).
example (L : Launch) (g : Nat) (t : TState) :
    tcTmpl L g t (.tcMma (.dense .one false .f16 0 (.smem (.reg 4)) (.reg 5) (.reg 1)
      (List.replicate 4 (.imm 0)) (.reg 6))) =
      mmaSmemTmpl L g t .one false .f16 0 (.reg 4) (.reg 5) (.reg 1)
        (List.replicate 4 (.imm 0)) (.reg 6) none {} :=
  tcTmpl_tcMma_smem (Or.inr (Or.inl rfl))

/-! ## kind::f8f6f4 descriptors -/

/-- F32 D (bits 4-5 = 1), A type `a` (bits 7-9), B type `b` (bits 10-12), N = 64, M = 128. -/
private def idesc (a b : Nat) : Nat := 16 + a * 2 ^ 7 + b * 2 ^ 10 + 8 * 2 ^ 17 + 8 * 2 ^ 24

example : (decode .one false .f8f6f4 (idesc 0 1)).map (·.kind) = some (.f8f6f4 .e4m3 .e5m2 .f32) :=
  rfl
example : (decode .one false .f8f6f4 (idesc 5 3)).map (·.kind) = some (.f8f6f4 .e2m1 .e2m3 .f32) :=
  rfl
example : ((decode .one false .f8f6f4 (idesc 0 0)).map (·.kind.k), (decode .one false .f8f6f4
    (idesc 0 0)).map (·.kind.width)) = (some 32, some 1) := rfl
-- Rejected: type code 2, the saturate bit, K = 64 (bit 29), a transposed 4-bit A.
example : decode .one false .f8f6f4 (idesc 2 0) = none := rfl
example : decode .one false .f8f6f4 (idesc 0 0 + 8) = none := rfl
example : decode .one false .f8f6f4 (idesc 0 0 + 2 ^ 29) = none := rfl
example : decode .one false .f8f6f4 (idesc 5 0 + 2 ^ 15) = none := rfl
example : ((decode .one false .f8f6f4 (idesc 0 0 + 2 ^ 15)).map (·.transposeA)) = some true := rfl
-- The block-scaled kinds have no dense descriptor.
example : decode .one false .mxf8f6f4 (idesc 0 0) = none := rfl

/-! ## Zero-column mask -/

example : zeroColumnMaskNone 0 = true := rfl
example : zeroColumnMaskNone (4 * 2 ^ 40 + 3 * 2 ^ 48) = true := rfl
example : zeroColumnMaskNone (2 ^ 39) = false := rfl
example : zeroColumnMaskNone (2 * 2 ^ 56) = false := rfl
example : zeroColumnMaskNone (2 ^ 36) = false := rfl

/-! ## Collector buffers -/

example : Collectors.op { a := .use } .a = some .use := rfl
example : Collectors.op { b := .fill, bBuffer := 2 } (.b 2) = some .fill := rfl
-- An issue that names B buffer 2 leaves buffer 0 alone.
example : Collectors.op { b := .use, bBuffer := 2 } (.b 0) = none := rfl
example : lastuse.collectors = { a := .lastuse } := rfl
-- No reuse: the collector rule holds.
example (X : Execution)
    (h : ∀ u d s acc mask, X.MmaIssue u d s acc mask → s.collector = {}) : CollectorSafe X :=
  collectorSafe_of_noReuse fun u d s acc mask hu => by simp [h u d s acc mask hu,
    MmaCollector.reuses]

/-- An execution whose only event is an MMA issue that reuses the A buffer, with no fill. -/
private def reuseAlone (s : OperandSpec) : Execution :=
  { tr := fun i => if i = 0 then [⟨0, .tc (.mma 0 s true [])⟩] else [],
    rf := fun _ _ => none }

-- A reuse without an earlier fill of the buffer is unsafe.
example (s : OperandSpec) (hs : s.collector.a = .use) : ¬ CollectorSafe (reuseAlone s) := by
  intro h
  have hu : (reuseAlone s).MmaIssue (0, 0) 0 s true [] := ⟨0, rfl⟩
  obtain ⟨_, f, ⟨hf1, hf2, _⟩, _⟩ := h (0, 0) 0 s true [] .a hu (by simp [Collectors.op, hs,
    MmaCollector.reuses])
  omega

end
end PTX.Tests.TcMmaQualifiers
