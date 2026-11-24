-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.PackedNormalize
import Kernels.FlashKdaFwd.Audit.Literals

/-! Trace the first live gate coordinate through its scalar arithmetic. The machine binary
uses standalone additions and multiplications for the unqualified PTX operations here. -/
namespace FlashKda.GateOverflow
open PTX
noncomputable section

structure Registers where
  parameter : Nat
  argument : Nat
  gain : Nat
  bias : Nat
  gate : Nat
  scale : Nat
  result : Nat

def regs (packed : Bool) : Registers :=
  if packed then ⟨293,294,211,216,381,1265,1283⟩
  else ⟨288,289,207,211,367,244,1249⟩

def scalar (op : FOp) (dst : Nat) (srcs : List Opnd) (mode := FMode.ieee)
    (rnd : Option FloatRound := none) : FloatInstr :=
  {op, mode, rnd, ty := ⟨.f32,1⟩, ftz := true, dsts := [some dst], srcs}

def gainCode (r : Registers) : List FloatInstr :=
  [scalar .mul r.argument [.reg r.parameter,.f32imm 0x3fb8aa3b],
   scalar .ex2 r.gain [.reg r.argument] .approx]

def gateCode (r : Registers) : List FloatInstr :=
  let b := r.gate
  [scalar .add (b+3) [.reg r.bias,.reg r.gate],
   scalar .mul (b+4) [.reg r.gain,.reg (b+3)],
   scalar .mul (b+2) [.reg (b+4),.f32imm 0xbfb8aa3b],
   scalar .ex2 (b+1) [.reg (b+2)] .approx,
   scalar .add (b+5) [.reg (b+1),.f32imm 0x3f800000],
   scalar .rcp (b+6) [.reg (b+5)] .approx,
   scalar .fma r.result [.reg r.scale,.reg (b+6),.f32imm 0] .ieee (some .rn)]

def sites (packed gain : Bool) : Option (List FloatInstr) :=
  let start := if gain then (if packed then 93 else 64) else (if packed then 199 else 166)
  Normalize.sites (if packed then 1 else 9) (List.range' start (if gain then 2 else 7))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem decoded (packed gain : Bool) : sites packed gain =
    some (if gain then gainCode (regs packed) else gateCode (regs packed)) := by
  cases packed <;> cases gain <;> rfl

/-- The next instruction consumes the prefix register in a four-byte shared-memory store. -/
def store (packed : Bool) : Option (List Instr) := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[if packed then 1 else 9]!).toOption
  let pc := if packed then 206 else 173
  let site ← p.instrs[pc]?
  (Decode.code p.env pc [site]).toOption

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem store_decoded (packed : Bool) : store packed = some [⟨none,.mem {
    kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
    addr := ⟨.reg (if packed then 215 else 210) 32,8192⟩, srcs := [.reg (regs packed).result]
  }⟩] := by cases packed <;> rfl

abbrev File := List (Nat × FVal)

def operand (file : File) : Opnd → Option FVal
  | .reg r => file.lookup r
  | .f32imm w => FloatFmt.f32.layout.decode w
  | _ => none

def standalone (i : FloatInstr) : FloatInstr :=
  if i.mode == .ieee && i.rnd.isNone && (i.op == .add || i.op == .mul)
  then {i with rnd := some .rn} else i

/-- Evaluate the decoded scalar registers and immediate words under the separate machine
arithmetic. The approximate instructions retain their ordinary TxVerify special-case tables. -/
def execute (file : File) (i : FloatInstr) : Option File := do
  let [some dst] := i.dsts | none
  let args ← i.srcs.mapM (operand file)
  let .val v ← (standalone i).lane args | none
  return (dst,v) :: file

private theorem writes {file : File} {i : FloatInstr} {dst args v} (dest : i.dsts = [some dst])
    (readArgs : i.srcs.mapM (operand file) = some args)
    (value : (standalone i).lane args = some (.val v)) :
    execute file i = some ((dst,v)::file) := by
  simp [execute,dest,readArgs,value]

def gain (packed : Bool) (word : Nat) : Option FVal := do
  let r := regs packed
  let v ← FloatFmt.f32.layout.decode word
  let code ← sites packed true
  let file ← code.foldlM execute [(r.parameter,v)]
  file.lookup r.gain

def firstGate (packed : Bool) (gainValue : FVal) : Option FVal := do
  let r := regs packed
  let scale ← FloatFmt.f32.layout.decode 0xc0e6d4ca
  let code ← sites packed false
  let file ← code.foldlM execute
    [(r.gain,gainValue),(r.bias,.zero false),(r.gate,.zero false),(r.scale,scale)]
  file.lookup r.result

theorem firstGate_inf (packed : Bool) : firstGate packed (.inf false) = some (.nan none) := by
  unfold firstGate
  rw [decoded]
  cases packed <;> decide +kernel

abbrev magnitude := Layout.magnitude 8 23
def firstWord : Nat := 0x7f317218

/-- The adjacent positive binary32 words straddle the exact round-to-infinity midpoint
after multiplication by the compiler's single-precision log-base-two conversion factor. -/
theorem threshold :
    magnitude (firstWord-1) * Literals.log2e < (2:ℚ)^128 - 2^103 ∧
    (2:ℚ)^128 - 2^103 ≤ magnitude firstWord * Literals.log2e := by decide +kernel

private def mul32 := scalar .mul 0 [] .ieee (some .rn)

def exponent100 : ℚ := 4727423/32768

local macro "fields" : tactic => `(tactic|
  norm_num [Layout.fieldVal,Layout.magnitude,Layout.bias,RoundMode.away,Literals.log2e,exponent100])

private theorem mul100 : mul32.lane [.fin 100,.fin Literals.log2e] =
    some (.val (.fin exponent100)) := by
  have rounded : (Layout.binary 8 23 true .ieee).round .rn .inf
      ((100*Literals.log2e : ℚ) : ℝ) false = some (.fin exponent100) := by
    rw [Layout.round_between (m := .rn) (F := 0x431044fe) (by trivial) (by decide)
      (by fields) (by fields) (by simp)]
    fields
  have kept : FloatFmt.f32.layout.flush (.fin exponent100) = .fin exponent100 := by decide +kernel
  have flush : mul32.flushIn [.fin 100,.fin Literals.log2e] = [.fin 100,.fin Literals.log2e] :=
    by decide +kernel
  change (FOut.val <$> mul32.arith _) = _
  simp [FloatInstr.arith,mul32,scalar,FloatRound.mode]
  unfold mul32 scalar at flush
  rw [flush]
  change FloatFmt.f32.layout.roundVal .rn true _ = _
  rw [show (FVal.fin 100).mul (.fin Literals.log2e) = .fin (100*Literals.log2e) by decide +kernel]
  unfold Layout.roundVal Layout.roundFtz
  change ((Layout.binary 8 23 true .ieee).round .rn .inf _ false).bind _ = _
  rw [rounded]
  have normal : ¬ |((100*Literals.log2e : ℚ) : ℝ)| < (FloatFmt.f32.layout.minNormal : ℚ) := by
    norm_num [FloatFmt.layout,Layout.minNormal,Layout.bias,Literals.log2e]
  simp [kept]
  intro below
  exact (normal (by simpa using below)).elim

/-- The multiplication for parameter 100 is still finite. The exact base-two exponential
already exceeds the largest finite binary32 value before the approximation is applied. -/
theorem argument_100 (packed : Bool) :
    (do
      let r := regs packed
      let code ← sites packed true
      let i ← code.head?
      let file ← execute [(r.parameter,.fin 100)] i
      file.lookup r.argument) = some (.fin exponent100) ∧
    (FloatFmt.f32.layout.maxNorm : ℝ) < (2:ℝ)^(exponent100:ℝ) := by
  constructor
  · let r := regs packed
    have one : execute [(r.parameter,.fin 100)]
        (scalar .mul r.argument [.reg r.parameter,.f32imm 0x3fb8aa3b]) =
        some [(r.argument,.fin exponent100),(r.parameter,.fin 100)] := by
      apply writes (args := [.fin 100,.fin Literals.log2e]) rfl
      · simp [scalar,operand,Literals.encoded.2,List.mapM_cons,List.mapM_nil]
      · exact mul100
    rw [decoded]
    change (execute [(r.parameter,.fin 100)] _).bind (List.lookup r.argument) = _
    rw [one]
    simp
  · have big := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by norm_num [exponent100] : (128:ℝ) ≤ exponent100)
    refine lt_of_lt_of_le ?_ big
    change ((Layout.binary 8 23 true .ieee).maxNorm : ℝ) < (2:ℝ)^(128:ℝ)
    norm_num [Layout.maxNorm_binary,Layout.topField,Layout.magnitude,Layout.bias]

private theorem rounded_overflow {x : ℚ} (large : (2:ℚ)^128 - 2^103 ≤ x) :
    FloatFmt.f32.layout.roundVal .rn true (.fin x) = some (.inf false) := by
  have bound : (2:ℝ)^128 - 2^103 ≤ x := by exact_mod_cast large
  have pos : (0:ℝ) < x := by linarith
  change (Layout.binary 8 23 true .ieee).roundFtz .rn true x = _
  unfold Layout.roundFtz
  rw [Layout.round_inf_ieee (m := .rn) (by trivial) (by
    rw [abs_of_pos pos]
    norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias]
    linarith)]
  simp only [abs_of_pos pos, not_lt.mpr pos.le, decide_false]
  norm_num [Layout.topField, Layout.magnitude, Layout.bias, Layout.fieldVal] at *
  split <;> first | linarith | simp [Layout.flush]

private theorem multiply {w : Nat} (lo : firstWord ≤ w) :
    mul32.lane [.fin (magnitude w),.fin Literals.log2e] = some (.val (.inf false)) := by
  have mono := (Layout.magnitude_strictMono 8 23).monotone lo
  have pos := Layout.magnitude_pos (eb := 8) (mb := 23) (by
    have : 0 < firstWord := by decide
    omega : 0 < w)
  have factor : (0:ℚ) < Literals.log2e := by decide +kernel
  have normal : FloatFmt.f32.layout.minNormal ≤ magnitude w :=
    le_trans (by decide +kernel : FloatFmt.f32.layout.minNormal ≤ magnitude firstWord) mono
  have flush : mul32.flushIn [.fin (magnitude w),.fin Literals.log2e] =
      [.fin (magnitude w),.fin Literals.log2e] := by
    have first : FloatFmt.f32.layout.flush (.fin (magnitude w)) = .fin (magnitude w) := by
      simp [Layout.flush,Layout.subnormal,abs_of_pos pos,not_lt.mpr normal]
    have second : FloatFmt.f32.layout.flush (.fin Literals.log2e) = .fin Literals.log2e :=
      by decide +kernel
    change [FloatFmt.f32.layout.flush _,FloatFmt.f32.layout.flush _] = _
    rw [first,second]
  change (FOut.val <$> mul32.arith _) = _
  simp [FloatInstr.arith,mul32,scalar,FloatRound.mode]
  unfold mul32 scalar at flush
  rw [flush]
  change FloatFmt.f32.layout.roundVal .rn true _ = _
  rw [show (FVal.fin (magnitude w)).mul (.fin Literals.log2e) =
      .fin (magnitude w * Literals.log2e) by
    simp [FVal.mul,FVal.toRat,ne_of_gt (mul_pos pos factor)]]
  exact rounded_overflow (threshold.2.trans (mul_le_mul_of_nonneg_right mono factor.le))

theorem gain_overflows (packed : Bool) {w : Nat} (lo : firstWord ≤ w) (hi : w ≤ 0x7f7fffff) :
    gain packed w = some (.inf false) := by
  have nz : w ≠ 0 := by
    have : 0 < firstWord := by decide
    omega
  have input : FloatFmt.f32.layout.decode w = some (.fin (magnitude w)) := by
    have h := FloatFmt.decode_field .f32 false hi
    change FloatFmt.f32.layout.decode (0+w) = some (Layout.fieldVal 8 23 w false) at h
    simpa [Layout.fieldVal,nz,magnitude] using h
  let r := regs packed
  let file : File := [(r.parameter,.fin (magnitude w))]
  have runMul : execute file (scalar .mul r.argument [.reg r.parameter,.f32imm 0x3fb8aa3b]) =
      some ((r.argument,.inf false)::file) := by
    apply writes (args := [.fin (magnitude w),.fin Literals.log2e]) rfl
    · simp [scalar,operand,file,Literals.encoded.2,List.mapM_cons,List.mapM_nil]
    · exact multiply lo
  unfold gain
  rw [input,decoded]
  change (List.foldlM execute file (gainCode r)).bind (List.lookup r.gain) = _
  simp only [gainCode,List.foldlM_cons,runMul]
  cases packed <;> rfl

/-- Starting from the public parameter word and the two zero gate operands, the first
live base-two gate prefix is necessarily NaN under the observed separate operations. -/
theorem nan_prefix (packed : Bool) {w : Nat} (lo : firstWord ≤ w) (hi : w ≤ 0x7f7fffff) :
    (gain packed w).bind (firstGate packed) = some (.nan none) := by
  rw [gain_overflows packed lo hi]
  exact firstGate_inf packed

theorem real_gate (param : ℝ) (i : Fin 128) :
    Algorithm.logGate (-5) param (fun _ => 0) (fun _ => 0) i = -5/2 := by
  norm_num [Algorithm.logGate,Algorithm.sigmoid]

end
end FlashKda.GateOverflow
