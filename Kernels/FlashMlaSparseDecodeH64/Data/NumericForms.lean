-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Data.Decoded

@[expose] public section

/-!
# Floating instruction forms of the FlashMLA sparse decode head64 kernel

`forms` lists every floating instruction form of `Decoded.kernel.code` with its instruction
count, in first-occurrence order. `forms_counts` proves each count is the number of instructions
with that form text, `forms_cover` proves every selected instruction has one of the listed
texts, and `forms_distinct` proves the texts are pairwise distinct, so the list is exactly the
distinct-and-count inventory of `formText` over the decoded program. The inventory is what the
numerical assumptions name, so that each assumption covers a form and a count rather than a
hand count.

The program's floating work, by form:
* the softmax row maximum and sum, rescaling and correction: `max.ftz.f32` 36, `mul.f32x2` 256,
  `add.f32x2` 32, `fma.rn.f32x2` 16, `sub.ftz.f32` 3, `add.ftz.f32` 3, `fma.rn.ftz.f32` 2,
  `mul.ftz.f32` 3, `neg.ftz.f32` 1 and four floating `setp` (one `gt` against 6.0, one `eq`
  against 0.0, and two `eq` against `0fFF800000`, the negative infinity that marks an empty
  row);
* `ex2.approx.ftz.f32` 34, the exponentials, and `lg2.approx.ftz.f32` 1 for the LSE, whose
  `logf` uses it;
* `div.approx.ftz.f32` 1 (the output multiplier `1 / (li + exp2(sink - mi))`) and no
  `rcp.approx`;
* the e4m3/ue8m0 dequantization: `cvt.rn.bf16x2.e4m3x2` 128, `cvt.rn.bf16x2.ue8m0x2` 32,
  `mul.bf16x2` 128 and `cvt.rn.bf16x2.f32` 144;
* `tcgen05.mma.ws.cta_group::1.kind::f16` 24: 16 read A from Tensor Memory and 8 from a shared
  matrix descriptor.

Which Core constructor covers which form (`Assumption/IdealReal.lean`,
`Assumption/ApproxExact.lean`): the scalar and pair floating arithmetic, including the
negated reference, uses the ideal float forms except
`mul.bf16x2` and the three `cvt.rn.bf16x2` conversions, and `ApproxForm` has `div` and `ex2`
but not `lg2`; `IdealScope.mma` has `kind::f16`. Those forms need kernel-local rules. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64

open PTX

/-! ## The text of a form -/

/-- `f16`, `bf16`, `f32`, ... as written in a floating type. -/
def floatFmtText : FloatFmt → String
  | .f16 => "f16" | .bf16 => "bf16" | .f32 => "f32" | .f64 => "f64"
  | .e4m3 => "e4m3" | .e5m2 => "e5m2"

/-- A floating type name (`tf32`, `ue8m0`, ... included). -/
def ftypeText : FType → String
  | .f16 => "f16" | .bf16 => "bf16" | .tf32 => "tf32" | .f32 => "f32" | .f64 => "f64"
  | .e4m3 => "e4m3" | .e5m2 => "e5m2" | .e2m3 => "e2m3" | .e3m2 => "e3m2" | .e2m1 => "e2m1"
  | .ue8m0 => "ue8m0" | .ue5m3 => "ue5m3" | .s2f6 => "s2f6"

/-- The `x2`, `x4` or `x8` suffix of a packed type; the explicit small cases keep the text
reducible in the kernel, as in `lanesText`. -/
def packText : Nat → String
  | 2 => "x2"
  | 4 => "x4"
  | 8 => "x8"
  | n => "x" ++ toString n

/-- A data type as written in an instruction (`bf16x2` for the packed type). -/
def dtypeText : DType → String
  | .pred => "pred"
  | .int k w => (match k with | .b => "b" | .u => "u" | .s => "s") ++ toString w
  | .float f => ftypeText f
  | .packed e n => dtypeText e ++ packText n

def cmpText : Cmp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .lo => "lo" | .ls => "ls" | .hi => "hi" | .hs => "hs"

/-- A floating comparison; `equ`, `neu`, ... are the unordered counterparts of `eq`, `ne`, ... -/
def fcmpText : FCmp → String
  | .ord c => cmpText c
  | .unord c => cmpText c ++ "u"
  | .num => "num"
  | .nan => "nan"

def boolOpText : BoolOp → String
  | .and => "and" | .or => "or" | .xor => "xor"

def floatRoundText : FloatRound → String
  | .rn => "rn" | .rz => "rz" | .rm => "rm" | .rp => "rp"

def testPropText : TestProp → String
  | .finite => "finite" | .infinite => "infinite" | .number => "number"
  | .notanumber => "notanumber" | .normal => "normal" | .subnormal => "subnormal"

/-- The operation name of a floating instruction, before its comparison (`setp`, `set`) or
test property (`testp`) and its rounding and qualifiers. -/
def floatOpText : FOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .fma => "fma" | .mad => "mad"
  | .div => "div" | .rcp => "rcp" | .sqrt => "sqrt" | .rsqrt => "rsqrt"
  | .ex2 => "ex2" | .lg2 => "lg2" | .sin => "sin" | .cos => "cos" | .tanh => "tanh"
  | .abs => "abs" | .neg => "neg" | .min => "min" | .max => "max" | .copysign => "copysign"
  | .testp p => "testp." ++ testPropText p
  | .setp .. => "setp"
  | .set _ _ d => "set." ++ dtypeText d

def cvtRndText : CvtRnd → String
  | .rn => "rn" | .rz => "rz" | .rm => "rm" | .rp => "rp" | .rni => "rni" | .rzi => "rzi"
  | .rmi => "rmi" | .rpi => "rpi" | .rna => "rna" | .rs => "rs"

def mmaKindText : MmaKind → String
  | .i8 => "kind::i8" | .f16 => "kind::f16" | .tf32 => "kind::tf32"
  | .f8f6f4 => "kind::f8f6f4" | .mxf8f6f4 => "kind::mxf8f6f4" | .mxf4 => "kind::mxf4"
  | .mxf4nvf4 => "kind::mxf4nvf4" | .ti16 => "kind::ti16"

def ctaGroupText : CtaGroup → String
  | .one => "cta_group::1" | .two => "cta_group::2"

/-- A `0f` constant that encodes an infinity (`0fFF800000` or `0f7F800000`). The same test as
`Assumption.isInfConst`, repeated here because this data module is imported by the assumptions
and so cannot import them. -/
def isInfConst : Opnd → Bool
  | .f32imm b => b == 0xFF800000 || b == 0x7F800000
  | _ => false

/-- The suffix of a packed floating type: empty for one lane, `x2`, `x4` or `x8` otherwise.
Only one and two lanes occur in this program; the last case keeps the text right for another
lane count, and the explicit small cases keep the text reducible in the kernel (a `toString` of
a computed number is not). -/
def lanesText : Nat → String
  | 1 => ""
  | 2 => "x2"
  | 4 => "x4"
  | 8 => "x8"
  | n => "x" ++ toString n

/-- The text of a floating instruction form: the operation, its comparison or test property,
its rounding modifier, `.approx`/`.full`, its qualifiers, its type with `x2` for a packed
type, and the mark of an infinite constant operand. -/
def floatInstrFormText (f : FloatInstr) : String :=
  let cmp := match f.op with
    | .setp c b => "." ++ fcmpText c ++ (match b with | some b => "." ++ boolOpText b | none => "")
    | .set c b _ => "." ++ fcmpText c ++
        (match b with | some b => "." ++ boolOpText b | none => "")
    | _ => ""
  let rnd := match f.rnd with | some r => "." ++ floatRoundText r | none => ""
  let mode := match f.mode with | .ieee => "" | .approx => ".approx" | .full => ".full"
  let ftz := if f.ftz then ".ftz" else ""
  let sat := if f.sat then ".sat" else ""
  let relu := if f.relu then ".relu" else ""
  let oob := if f.oob then ".oob" else ""
  let nan := if f.nanMod then ".NaN" else ""
  let xorsign := if f.xorsign then ".xorsign" else ""
  let absq := if f.absMod then ".abs" else ""
  let lanes := lanesText f.ty.lanes
  let inf := match f.op with
    | .setp .. => if f.srcs.any isInfConst then " (with an infinite constant operand)" else ""
    | _ => ""
  floatOpText f.op ++ cmp ++ rnd ++ mode ++ ftz ++ sat ++ relu ++ oob ++ nan ++ xorsign ++
    absq ++ "." ++ floatFmtText f.ty.fmt ++ lanes ++ inf

/-- The text of a conversion form: `cvt`, its rounding modifier and qualifiers, then its
destination and source types. -/
def cvtInstrFormText (c : CvtInstr) : String :=
  "cvt" ++ (match c.rnd with | some r => "." ++ cvtRndText r | none => "") ++
    (if c.ftz then ".ftz" else "") ++ (if c.sat then ".sat" else "") ++
    (if c.relu then ".relu" else "") ++ (if c.satfinite then ".satfinite" else "") ++
    (if c.pzo then ".pzo" else "") ++ (if c.scaled then ".scaled" else "") ++
    "." ++ dtypeText c.dst ++ "." ++ dtypeText c.src

/-- The text of an MMA form: the instruction, `.ws` when written, the CTA group and the kind. -/
def tcMmaInstrFormText (m : TcMmaInstr) : String :=
  "tcgen05.mma" ++ (if m.ws then ".ws" else "") ++ "." ++ ctaGroupText m.group ++ "." ++
    mmaKindText m.kind

/-- A floating type, or a packed one of them. -/
def isFloatingType : DType → Bool
  | .float _ => true
  | .packed e _ => isFloatingType e
  | _ => false

/-- The floating form text of an instruction, or `none` when the instruction is not a floating
instruction, a floating conversion or an MMA. -/
def formText : Op → Option String
  | .float f => some (floatInstrFormText f)
  | .cvt c =>
    if isFloatingType c.dst || isFloatingType c.src then some (cvtInstrFormText c) else none
  | .tcMma m => some (tcMmaInstrFormText m)
  | _ => none

/-! ## The inventory -/

/-- The form text of every floating instruction, floating conversion and MMA of the program,
in source order. -/
def texts : List String := Decoded.kernel.code.filterMap fun i => formText i.op

/-- The number of selected instructions whose form text is `s`. -/
def countText (s : String) : Nat := (texts.filter fun t => t == s).length

/-- The kernel's floating instruction forms with their counts, in first-occurrence order. -/
def forms : List (String × Nat) :=
  [("mul.ftz.f32", 3), ("add.f32x2", 32), ("max.ftz.f32", 36), ("sub.ftz.f32", 3),
    ("setp.gt.ftz.f32", 1), ("ex2.approx.ftz.f32", 34), ("neg.ftz.f32", 1),
    ("fma.rn.f32x2", 16), ("cvt.rn.bf16x2.f32", 144), ("add.ftz.f32", 3),
    ("fma.rn.ftz.f32", 2), ("mul.f32x2", 256),
    ("setp.eq.ftz.f32 (with an infinite constant operand)", 2), ("lg2.approx.ftz.f32", 1),
    ("setp.eq.ftz.f32", 1), ("div.approx.ftz.f32", 1),
    ("tcgen05.mma.ws.cta_group::1.kind::f16", 24), ("cvt.rn.bf16x2.ue8m0x2", 32),
    ("cvt.rn.bf16x2.e4m3x2", 128), ("mul.bf16x2", 128)]

/-- Each count of `forms` is the number of selected instructions with that form text. The texts
are pairwise distinct (`forms_distinct`), so `forms` is the distinct-and-count inventory of
`texts`. -/
theorem forms_counts : forms.all (fun p => countText p.1 == p.2) = true := by
  decide +kernel

/-- Every selected instruction's form text is one of the inventory's texts. -/
theorem forms_cover : texts.all (fun t => forms.any (fun p => p.1 == t)) = true := by
  decide +kernel

/-- The inventory's texts are pairwise distinct. -/
theorem forms_distinct : (forms.map (·.1)).eraseDups = forms.map (·.1) := by
  decide

/-- The counts sum to the number of floating instructions, floating conversions and MMAs. -/
theorem forms_sum : (forms.map (·.2)).sum = texts.length := by
  decide +kernel

/-- The kernel has 848 floating instructions, floating conversions and MMAs: 520 `float`, 304
floating `cvt` and 24 `tcgen05.mma`. -/
theorem forms_total : texts.length = 848 := by
  decide +kernel

/-! ## Key counts -/

/-- The number of instructions whose operation satisfies `f`. -/
def countWhere (f : Op → Bool) : Nat :=
  (Decoded.kernel.code.filter fun i => f i.op).length

/-- `ex2.approx.ftz.f32` sites. -/
theorem ex2_count : countWhere (fun op => match op with
    | .float f => f.op == .ex2
    | _ => false) = 34 := by
  decide +kernel

/-- `lg2.approx.ftz.f32` sites. -/
theorem lg2_count : countWhere (fun op => match op with
    | .float f => f.op == .lg2
    | _ => false) = 1 := by
  decide +kernel

/-- `mul.bf16x2` sites. -/
theorem mulBf16x2_count : countWhere (fun op => match op with
    | .float f => f.op == .mul && f.ty == ⟨.bf16, 2⟩
    | _ => false) = 128 := by
  decide +kernel

/-- `cvt.rn.bf16x2.f32` sites. -/
theorem cvtBf16x2F32_count : countWhere (fun op => match op with
    | .cvt c => c.rnd == some .rn && c.dst == .packed (.float .bf16) 2 &&
        c.src == .float .f32
    | _ => false) = 144 := by
  decide +kernel

/-- `cvt.rn.bf16x2.e4m3x2` sites. -/
theorem cvtBf16x2E4m3x2_count : countWhere (fun op => match op with
    | .cvt c => c.rnd == some .rn && c.dst == .packed (.float .bf16) 2 &&
        c.src == .packed (.float .e4m3) 2
    | _ => false) = 128 := by
  decide +kernel

/-- `cvt.rn.bf16x2.ue8m0x2` sites. -/
theorem cvtBf16x2Ue8m0x2_count : countWhere (fun op => match op with
    | .cvt c => c.rnd == some .rn && c.dst == .packed (.float .bf16) 2 &&
        c.src == .packed (.float .ue8m0) 2
    | _ => false) = 32 := by
  decide +kernel

/-- `tcgen05.mma` sites. -/
theorem tcMma_count : countWhere (fun op => match op with
    | .tcMma _ => true
    | _ => false) = 24 := by
  decide +kernel

/-- The program has no warp-level `mma` and no unmodeled instruction, so `formText` covers every
instruction with floating arithmetic. -/
theorem noOtherFloat :
    (Decoded.kernel.code.filter fun i => match i.op with
      | .matrix _ | .unmodeled _ => true
      | _ => false).length = 0 := by
  decide +kernel

end PTX.Kernels.FlashMlaSparseDecodeH64
