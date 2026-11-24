-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SetpCore
public import Lemmas.Flow.Cvt
public import Lemmas.Flow.SegFree

@[expose] public section

/-! # Packed multiplications and conversions to halves at one state

A proof tool: the state-wise forms of `exec_floatE_mul2` and `exec_cvtPair`, for an assumption
list that reads the form exactly (`IdealAt`) and leaves its declines to the Core rule
(`DeclineAt`) only at some states (for example outside the segments of another assumption).
`mul.rnd{.ftz}.f32x2 d, a, b` writes the outcome `floatE` of its operands' values or faults
(`exec_floatE_mul2_at`); `cvt.rn.f16x2.f32 d, a, b` writes the outcome `cvtPairE` or faults
(`exec_cvtPair_at`).

Runs, for code that multiplies packed pairs by one pair `c`, then unpacks the products and
converts each to a pair of halves (a Tensor Memory rescale or normalization):
* `mulsE_run`: a run of `mul.rnd{.ftz}.f32x2 d, s, c`. When no step faults (`mulsEOk`), local
  steps write each destination with its outcome (`mulOutV`, `mulRunE`); otherwise the thread is
  dead.
* `unpacks_run`: a run of `mov.b64 {lo, hi}, s` from sources that hold pairs of four-byte
  values: local steps write the halves (`unpackRun`).
* `unpackCvts_run`: a run of such an unpack followed by `cvt.rn.f16x2.f32 d, hi, lo`. When no
  conversion faults (`cvtsOk`), local steps write the halves and the converted pair
  (`unpackCvtRun`); otherwise the thread is dead. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem exec_floatE_mul2_at {t : TState} (hA : IdealAt A .mulF32x2 L g t)
    (hD : DeclineAt A .mulF32x2 L g t) {rnd : FloatRound} {fz : Bool} {d a b : Nat}
    {va vb : Value} (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (.float { mul2I rnd fz with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (floatE (mul2I rnd fz) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp
      (.float { mul2I rnd fz with dsts := [some d], srcs := [.reg a, .reg b] }) =
      some .mulF32x2 := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t
      (.float { mul2I rnd fz with dsts := [some d], srcs := [.reg a, .reg b] }) =
      (idealVal (mul2I rnd fz) [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealVal, readERealPair_reg_val (L := L) (g := g) ha,
      readERealPair_reg_val (L := L) (g := g) hb, bindRead_map]
    rcases pairRead va with _ | (e | ⟨x0, x1⟩)
    · rfl
    · rfl
    rcases pairRead vb with _ | (e | ⟨y0, y1⟩)
    · rfl
    · rfl
    simp only [bindRead]
    rcases mulEReal x0 y0 with _ | r0 <;> rcases mulEReal x1 y1 with _ | r1 <;> rfl
  unfold floatE
  cases hv : idealVal (mul2I rnd fz) [va, vb] with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_mul2_core ha hb]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

theorem exec_cvtPair_at {t : TState} (hA : IdealAt A .cvtRnF16x2F32 L g t)
    (hD : DeclineAt A .cvtRnF16x2F32 L g t) {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (.cvt (cvtPairInstr d a b)) =
      (cvtPairE va vb).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.cvt (cvtPairInstr d a b)) = some .cvtRnF16x2F32 := by
    simp [FloatForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?, CvtInstr.plain]
  have hra := readERealOpnd_reg (fmt := .f32) ha
  have hrb := readERealOpnd_reg (fmt := .f32) hb
  have hI : execIdealFloat L g t (.cvt (cvtPairInstr d a b)) =
      bindRead (readEReal .f32 va) fun x => bindRead (readEReal .f32 vb) fun y =>
        some (pure (PTX.next (setReg t d (.pair (erealValue .f16 y) (erealValue .f16 x))))) := by
    simp [execIdealFloat, CvtInstr.widenF16?, CvtInstr.packF16?, CvtInstr.plain, hra, hrb]
  unfold cvtPairE
  rcases hx : readEReal .f32 va with _ | (e | x)
  · rw [hD _ hf (by rw [hI, hx]; rfl), execLocal_cvtPair ha hb]
  · rw [hA _ hf _ (by rw [hI, hx]; rfl)]; rfl
  · rcases hy : readEReal .f32 vb with _ | (e | y)
    · rw [hD _ hf (by rw [hI, hx, hy]; rfl), execLocal_cvtPair ha hb]
    · rw [hA _ hf _ (by rw [hI, hx, hy]; rfl)]; rfl
    · rw [hA _ hf _ (by rw [hI, hx, hy]; rfl)]; rfl

/-! ### A run of packed multiplications -/

/-- The packed multiplications `(d, s)` (`mul.rnd{.ftz}.f32x2 d, s, c`) from `pc` on. -/
def MulCodeE (K : Kernel) (rnd : FloatRound) (fz : Bool) (c : Nat) :
    Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | pc, m :: ms =>
    K.code[pc]? = some ⟨none, .float
      { mul2I rnd fz with dsts := [some m.1], srcs := [.reg m.2, .reg c] }⟩ ∧
      MulCodeE K rnd fz c (pc + 1) ms

/-- `MulCodeE` decided on the code. -/
def mulCodeEB (K : Kernel) (rnd : FloatRound) (fz : Bool) (c : Nat) :
    Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | pc, m :: ms =>
    (match K.code[pc]? with
      | some ⟨none, .float f⟩ =>
        f == { mul2I rnd fz with dsts := [some m.1], srcs := [.reg m.2, .reg c] }
      | _ => false) && mulCodeEB K rnd fz c (pc + 1) ms

theorem MulCodeE.of_bool {K : Kernel} {rnd : FloatRound} {fz : Bool} {c : Nat} :
    ∀ {pc : Nat} {ms : List (Nat × Nat)}, mulCodeEB K rnd fz c pc ms = true →
      MulCodeE K rnd fz c pc ms
  | _, [], _ => trivial
  | pc, m :: ms, h => by
    simp only [mulCodeEB, Bool.and_eq_true] at h
    refine ⟨?_, MulCodeE.of_bool h.2⟩
    have h1 := h.1
    split at h1
    · rename_i f hc
      rw [hc, beq_iff_eq.mp h1]
    · cases h1

/-- The pair a multiplication writes (a pair of zeros where it faults). -/
def mulOutV (rnd : FloatRound) (fz : Bool) (w c : Value) : Value :=
  okVal (.pair (b32 0) (b32 0)) (floatE (mul2I rnd fz) [w, c])

/-- No multiplication of the run faults. -/
def mulsEOk (rnd : FloatRound) (fz : Bool) (v : Nat → Value) (vc : Value)
    (ms : List (Nat × Nat)) : Bool :=
  ms.all fun m => (floatE (mul2I rnd fz) [v m.2, vc]).toBool

/-- The state after the multiplications, from source values `v` and the pair `vc`. -/
def mulRunE (rnd : FloatRound) (fz : Bool) (v : Nat → Value) (vc : Value) :
    TState → List (Nat × Nat) → TState
  | t, [] => t
  | t, m :: ms => mulRunE rnd fz v vc (PTX.next (setReg t m.1 (mulOutV rnd fz (v m.2) vc))) ms

theorem mulRunE_skel (rnd : FloatRound) (fz : Bool) (v : Nat → Value) (vc : Value) :
    ∀ (ms : List (Nat × Nat)) (t : TState),
    (mulRunE rnd fz v vc t ms).pc = t.pc + ms.length ∧ (mulRunE rnd fz v vc t ms).sub = t.sub ∧
      (mulRunE rnd fz v vc t ms).acc = t.acc ∧ (mulRunE rnd fz v vc t ms).fault = t.fault
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | m :: ms, t => by
    obtain ⟨h1, h2, h3, h4⟩ := mulRunE_skel rnd fz v vc ms
      (PTX.next (setReg t m.1 (mulOutV rnd fz (v m.2) vc)))
    refine ⟨?_, h2, h3, h4⟩
    rw [mulRunE, h1]
    simp only [PTX.next, setReg, List.length_cons]
    omega

theorem mulRunE_other (rnd : FloatRound) (fz : Bool) (v : Nat → Value) (vc : Value) {r : Nat} :
    ∀ (ms : List (Nat × Nat)) (t : TState), (∀ m ∈ ms, m.1 ≠ r) →
      (mulRunE rnd fz v vc t ms).regs r = t.regs r
  | [], _, _ => rfl
  | m :: ms, t, h => by
    rw [mulRunE, mulRunE_other rnd fz v vc ms _ (fun q hq => h q (by simp [hq]))]
    simp [PTX.next, setReg, Function.update_of_ne (h m (by simp)).symm]

theorem mulRunE_val (rnd : FloatRound) (fz : Bool) (v : Nat → Value) (vc : Value) {d s : Nat} :
    ∀ (ms : List (Nat × Nat)) (t : TState), (ms.map Prod.fst).Nodup → (d, s) ∈ ms →
      (mulRunE rnd fz v vc t ms).regs d = some (mulOutV rnd fz (v s) vc)
  | [], _, _, hm => by simp at hm
  | m :: ms, t, hnd, hm => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [mulRunE, mulRunE_other rnd fz v vc ms _ (fun q hq he => hnd.1 ⟨q, hq, he⟩)]
      simp [PTX.next, setReg]
    · exact mulRunE_val rnd fz v vc ms _ hnd.2 hm

/-- **A run of packed multiplications**: each writes its outcome when no step faults; otherwise
the thread is dead. -/
theorem mulsE_run {K : Kernel} {rnd : FloatRound} {fz : Bool} (v : Nat → Value) {c : Nat}
    {vc : Value} : ∀ (ms : List (Nat × Nat)) (t : TState), MulCodeE K rnd fz c t.pc ms →
    t.fault = none → t.regs c = some vc → (∀ m ∈ ms, t.regs m.2 = some (v m.2)) →
    (∀ m ∈ ms, m.1 ≠ c ∧ ∀ m' ∈ ms, m.1 ≠ m'.2) →
    (∀ i < ms.length, ∀ s : TState, s.pc = t.pc + i →
      IdealAt A .mulF32x2 L g s ∧ DeclineAt A .mulF32x2 L g s) →
    (mulsEOk rnd fz v vc ms = true → run K A L g ms.length t = some (mulRunE rnd fz v vc t ms)) ∧
    (mulsEOk rnd fz v vc ms = false → Machine.Dead (K := K) (A := A) (L := L) (g := g) t)
  | [], t, _, _, _, _, _, _ => ⟨fun _ => rfl, fun h => by simp [mulsEOk] at h⟩
  | m :: ms, t, hc, hf, hcv, hv, hfr, hI => by
    obtain ⟨hA, hD⟩ := hI 0 (by simp) t (by simp)
    have hex := exec_floatE_mul2_at (rnd := rnd) (fz := fz) (d := m.1) hA hD
      (hv m (by simp)) hcv
    set t1 := PTX.next (setReg t m.1 (mulOutV rnd fz (v m.2) vc))
    have hm := hfr m (by simp)
    have hcv1 : t1.regs c = some vc := by
      simp [t1, PTX.next, setReg, Function.update_of_ne hm.1.symm, hcv]
    have hreg : ∀ q ∈ ms, t1.regs q.2 = some (v q.2) := by
      intro q hq
      simp only [t1, PTX.next, setReg, Function.update_of_ne (hm.2 q (by simp [hq])).symm]
      exact hv q (by simp [hq])
    have ih := mulsE_run v ms t1 hc.2 hf hcv1 hreg
      (fun q hq => ⟨(hfr q (by simp [hq])).1,
        fun q' hq' => (hfr q (by simp [hq])).2 q' (by simp [hq'])⟩)
      (fun i hi s hs' => hI (i + 1) (by simp; omega) s
        (by rw [hs']; simp [t1, PTX.next, setReg]; omega))
    rcases hE : floatE (mul2I rnd fz) [v m.2, vc] with e | x
    · rw [hE] at hex
      refine ⟨fun h => by simp [mulsEOk, hE, Except.toBool] at h, fun _ => ?_⟩
      exact dead_of_error hc.1 rfl hf hex
    · rw [hE] at hex
      have hx : mulOutV rnd fz (v m.2) vc = x := by simp [mulOutV, hE, okVal]
      have o1 : out K A L g t = .tau t1 := by
        rw [tau_of_ok hc.1 rfl hf hex]; simp only [t1, hx]
      have he : mulsEOk rnd fz v vc (m :: ms) = mulsEOk rnd fz v vc ms := by
        simp [mulsEOk, hE, Except.toBool]
      refine ⟨fun h => ?_, fun h => Machine.dead_of_tau o1 (ih.2 (he ▸ h))⟩
      simp only [List.length_cons, run, tauStep, o1, Option.bind_some, mulRunE]
      exact ih.1 (he ▸ h)

/-! ### Runs of unpacks, and of unpacks with conversions to halves -/

/-- `mov.b64 {lo, hi}, a` on a register that holds a pair of four-byte values writes the halves,
at a state without a segment where no assumption names the move. -/
theorem exec_unpack_pair {t : TState} (hM : CoreMoves A) (hS : SegFreePc A t.pc)
    {lo hi a : Nat} {x y : Value} (h : t.regs a = some (.pair x y)) (hx : x.bytes = 4)
    (hy : y.bytes = 4) :
    execLocalA A L g t (.move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg a]⟩) =
      .ok (PTX.next (setReg (setReg t lo x) hi y)) := by
  rw [(hS.at rfl).exec, execLocalRule_of_none (hM _ L g t)]
  have h1 : (Value.pair x y).bytes = 8 := by simp [Value.bytes, hx, hy]
  have h2 : (splitValue 64 (.pair x y)) = (x, y) := by simp [splitValue]
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, h, h1, h2,
    hx, hy, bind, Except.bind, pure, Except.pure]

/-- The unpacks `(s, lo, hi)` (`mov.b64 {lo, hi}, s`) from `pc` on. -/
def UnpackCode (K : Kernel) : Nat → List (Nat × Nat × Nat) → Prop
  | _, [] => True
  | pc, u :: us =>
    K.code[pc]? = some ⟨none, .move ⟨.unpack, .int .b 64, [some u.2.1, some u.2.2], [.reg u.1]⟩⟩ ∧
      UnpackCode K (pc + 1) us

/-- `UnpackCode` decided on the code. -/
def unpackCodeB (K : Kernel) : Nat → List (Nat × Nat × Nat) → Bool
  | _, [] => true
  | pc, u :: us =>
    (match K.code[pc]? with
      | some ⟨none, .move m⟩ =>
        m == ⟨.unpack, .int .b 64, [some u.2.1, some u.2.2], [.reg u.1]⟩
      | _ => false) && unpackCodeB K (pc + 1) us

theorem UnpackCode.of_bool {K : Kernel} : ∀ {pc : Nat} {us : List (Nat × Nat × Nat)},
    unpackCodeB K pc us = true → UnpackCode K pc us
  | _, [], _ => trivial
  | pc, u :: us, h => by
    simp only [unpackCodeB, Bool.and_eq_true] at h
    refine ⟨?_, UnpackCode.of_bool h.2⟩
    have h1 := h.1
    split at h1
    · rename_i m hc
      rw [hc, beq_iff_eq.mp h1]
    · cases h1

/-- The state after the unpacks, from source values `v`. -/
def unpackRun (v : Nat → Value) : TState → List (Nat × Nat × Nat) → TState
  | t, [] => t
  | t, u :: us => unpackRun v (PTX.next (setReg (setReg t u.2.1 (splitValue 64 (v u.1)).1) u.2.2
      (splitValue 64 (v u.1)).2)) us

theorem unpackRun_skel (v : Nat → Value) : ∀ (us : List (Nat × Nat × Nat)) (t : TState),
    (unpackRun v t us).pc = t.pc + us.length ∧ (unpackRun v t us).sub = t.sub ∧
      (unpackRun v t us).acc = t.acc ∧ (unpackRun v t us).fault = t.fault
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | u :: us, t => by
    obtain ⟨h1, h2, h3, h4⟩ := unpackRun_skel v us (PTX.next (setReg (setReg t u.2.1
      (splitValue 64 (v u.1)).1) u.2.2 (splitValue 64 (v u.1)).2))
    refine ⟨?_, h2, h3, h4⟩
    rw [unpackRun, h1]
    simp only [PTX.next, setReg, List.length_cons]
    omega

theorem unpackRun_other (v : Nat → Value) {r : Nat} : ∀ (us : List (Nat × Nat × Nat))
    (t : TState), (∀ u ∈ us, u.2.1 ≠ r ∧ u.2.2 ≠ r) → (unpackRun v t us).regs r = t.regs r
  | [], _, _ => rfl
  | u :: us, t, h => by
    rw [unpackRun, unpackRun_other v us _ (fun q hq => h q (by simp [hq]))]
    have hu := h u (by simp)
    simp [PTX.next, setReg, Function.update_of_ne hu.1.symm, Function.update_of_ne hu.2.symm]

/-- **A run of unpacks** of pairs of four-byte values: local steps write the halves. -/
theorem unpacks_run {K : Kernel} (hM : CoreMoves A) (v : Nat → Value) :
    ∀ (us : List (Nat × Nat × Nat)) (t : TState), UnpackCode K t.pc us → t.fault = none →
    (∀ u ∈ us, t.regs u.1 = some (v u.1)) →
    (∀ u ∈ us, ∃ x y, v u.1 = .pair x y ∧ x.bytes = 4 ∧ y.bytes = 4) →
    (∀ u ∈ us, ∀ u' ∈ us, u'.2.1 ≠ u.1 ∧ u'.2.2 ≠ u.1) →
    (∀ i < us.length, SegFreePc A (t.pc + i)) →
    run K A L g us.length t = some (unpackRun v t us)
  | [], _, _, _, _, _, _, _ => rfl
  | u :: us, t, hc, hf, hv, hp, hfr, hS => by
    obtain ⟨x, y, hxy, hx, hy⟩ := hp u (by simp)
    have hS0 : SegFreePc A t.pc := by simpa using hS 0 (by simp)
    have hex := exec_unpack_pair (L := L) (g := g) (lo := u.2.1) (hi := u.2.2) hM hS0
      ((hv u (by simp)).trans (by rw [hxy])) hx hy
    have hsp : splitValue 64 (v u.1) = (x, y) := by rw [hxy]; simp [splitValue]
    set t1 := PTX.next (setReg (setReg t u.2.1 (splitValue 64 (v u.1)).1) u.2.2
      (splitValue 64 (v u.1)).2)
    have o1 : out K A L g t = .tau t1 := by
      rw [tau_of_ok hc.1 rfl hf hex]; simp [t1, hsp]
    have hreg : ∀ q ∈ us, t1.regs q.1 = some (v q.1) := by
      intro q hq
      have h1 := hfr q (by simp [hq]) u (by simp)
      simp only [t1, PTX.next, setReg, Function.update_of_ne h1.1.symm,
        Function.update_of_ne h1.2.symm]
      exact hv q (by simp [hq])
    have ih := unpacks_run hM v us t1 hc.2 hf hreg (fun q hq => hp q (by simp [hq]))
      (fun q hq q' hq' => hfr q (by simp [hq]) q' (by simp [hq']))
      (fun i hi => by
        have := hS (i + 1) (by simp; omega)
        rwa [show t.pc + (i + 1) = t1.pc + i by simp [t1, PTX.next, setReg]; omega] at this)
    simp only [List.length_cons, run, tauStep, o1, Option.bind_some, unpackRun]
    exact ih

/-- The unpacks with conversions `(s, lo, hi, d)` (`mov.b64 {lo, hi}, s` then
`cvt.rn.f16x2.f32 d, hi, lo`) from `pc` on. -/
def UnpackCvtCode (K : Kernel) : Nat → List (Nat × Nat × Nat × Nat) → Prop
  | _, [] => True
  | pc, u :: us =>
    K.code[pc]? = some ⟨none, .move ⟨.unpack, .int .b 64, [some u.2.1, some u.2.2.1],
        [.reg u.1]⟩⟩ ∧
      K.code[pc + 1]? = some ⟨none, .cvt (cvtPairInstr u.2.2.2 u.2.2.1 u.2.1)⟩ ∧
      UnpackCvtCode K (pc + 2) us

/-- `UnpackCvtCode` decided on the code. -/
def unpackCvtCodeB (K : Kernel) : Nat → List (Nat × Nat × Nat × Nat) → Bool
  | _, [] => true
  | pc, u :: us =>
    (match K.code[pc]? with
      | some ⟨none, .move m⟩ =>
        m == ⟨.unpack, .int .b 64, [some u.2.1, some u.2.2.1], [.reg u.1]⟩
      | _ => false) &&
    (match K.code[pc + 1]? with
      | some ⟨none, .cvt c⟩ => c == cvtPairInstr u.2.2.2 u.2.2.1 u.2.1
      | _ => false) && unpackCvtCodeB K (pc + 2) us

theorem UnpackCvtCode.of_bool {K : Kernel} : ∀ {pc : Nat} {us : List (Nat × Nat × Nat × Nat)},
    unpackCvtCodeB K pc us = true → UnpackCvtCode K pc us
  | _, [], _ => trivial
  | pc, u :: us, h => by
    simp only [unpackCvtCodeB, Bool.and_eq_true] at h
    refine ⟨?_, ?_, UnpackCvtCode.of_bool h.2⟩
    · have h1 := h.1.1
      split at h1
      · rename_i m hc
        rw [hc, beq_iff_eq.mp h1]
      · cases h1
    · have h1 := h.1.2
      split at h1
      · rename_i c hc
        rw [hc, beq_iff_eq.mp h1]
      · cases h1

/-- The pair of halves the conversion of the unpacked pair `w` writes (`b32 0` where it
faults): its high element in the high half. -/
def cvtOfPair (w : Value) : Value := cvtPairV (splitValue 64 w).2 (splitValue 64 w).1

/-- No conversion of the run faults. -/
def cvtsOk (v : Nat → Value) (us : List (Nat × Nat × Nat × Nat)) : Bool :=
  us.all fun u => (cvtPairE (splitValue 64 (v u.1)).2 (splitValue 64 (v u.1)).1).toBool

/-- The state after the unpacks and conversions, from source values `v`. -/
def unpackCvtRun (v : Nat → Value) : TState → List (Nat × Nat × Nat × Nat) → TState
  | t, [] => t
  | t, u :: us => unpackCvtRun v (PTX.next (setReg (PTX.next (setReg (setReg t u.2.1
      (splitValue 64 (v u.1)).1) u.2.2.1 (splitValue 64 (v u.1)).2)) u.2.2.2
      (cvtOfPair (v u.1)))) us

theorem unpackCvtRun_skel (v : Nat → Value) : ∀ (us : List (Nat × Nat × Nat × Nat))
    (t : TState),
    (unpackCvtRun v t us).pc = t.pc + 2 * us.length ∧ (unpackCvtRun v t us).sub = t.sub ∧
      (unpackCvtRun v t us).acc = t.acc ∧ (unpackCvtRun v t us).fault = t.fault
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | u :: us, t => by
    obtain ⟨h1, h2, h3, h4⟩ := unpackCvtRun_skel v us (PTX.next (setReg (PTX.next (setReg
      (setReg t u.2.1 (splitValue 64 (v u.1)).1) u.2.2.1 (splitValue 64 (v u.1)).2)) u.2.2.2
      (cvtOfPair (v u.1))))
    refine ⟨?_, h2, h3, h4⟩
    rw [unpackCvtRun, h1]
    simp only [PTX.next, setReg, List.length_cons]
    omega

theorem unpackCvtRun_other (v : Nat → Value) {r : Nat} : ∀ (us : List (Nat × Nat × Nat × Nat))
    (t : TState), (∀ u ∈ us, u.2.1 ≠ r ∧ u.2.2.1 ≠ r ∧ u.2.2.2 ≠ r) →
      (unpackCvtRun v t us).regs r = t.regs r
  | [], _, _ => rfl
  | u :: us, t, h => by
    rw [unpackCvtRun, unpackCvtRun_other v us _ (fun q hq => h q (by simp [hq]))]
    have hu := h u (by simp)
    simp [PTX.next, setReg, Function.update_of_ne hu.1.symm, Function.update_of_ne hu.2.1.symm,
      Function.update_of_ne hu.2.2.symm]

/-- **A run of unpacks with conversions to halves** of pairs of four-byte values: when no
conversion faults, local steps write the halves and the converted pairs; otherwise the thread is
dead. -/
theorem unpackCvts_run {K : Kernel} (hM : CoreMoves A) (v : Nat → Value) :
    ∀ (us : List (Nat × Nat × Nat × Nat)) (t : TState), UnpackCvtCode K t.pc us →
    t.fault = none → (∀ u ∈ us, t.regs u.1 = some (v u.1)) →
    (∀ u ∈ us, ∃ x y, v u.1 = .pair x y ∧ x.bytes = 4 ∧ y.bytes = 4) →
    (∀ u ∈ us, u.2.1 ≠ u.2.2.1) →
    (∀ u ∈ us, ∀ u' ∈ us, u'.2.1 ≠ u.1 ∧ u'.2.2.1 ≠ u.1 ∧ u'.2.2.2 ≠ u.1) →
    (∀ i < 2 * us.length, SegFreePc A (t.pc + i)) →
    (∀ i < us.length, ∀ s : TState, s.pc = t.pc + 2 * i + 1 →
      IdealAt A .cvtRnF16x2F32 L g s ∧ DeclineAt A .cvtRnF16x2F32 L g s) →
    (cvtsOk v us = true → run K A L g (2 * us.length) t = some (unpackCvtRun v t us)) ∧
    (cvtsOk v us = false → Machine.Dead (K := K) (A := A) (L := L) (g := g) t)
  | [], _, _, _, _, _, _, _, _, _ => ⟨fun _ => rfl, fun h => by simp [cvtsOk] at h⟩
  | u :: us, t, hc, hf, hv, hp, hlh, hfr, hS, hI => by
    obtain ⟨x, y, hxy, hx, hy⟩ := hp u (by simp)
    have hS0 : SegFreePc A t.pc := by simpa using hS 0 (by simp)
    have hex := exec_unpack_pair (L := L) (g := g) (lo := u.2.1) (hi := u.2.2.1) hM hS0
      ((hv u (by simp)).trans (by rw [hxy])) hx hy
    have hsp : splitValue 64 (v u.1) = (x, y) := by rw [hxy]; simp [splitValue]
    set t1 := PTX.next (setReg (setReg t u.2.1 (splitValue 64 (v u.1)).1) u.2.2.1
      (splitValue 64 (v u.1)).2)
    have o1 : out K A L g t = .tau t1 := by
      rw [tau_of_ok hc.1 rfl hf hex]; simp [t1, hsp]
    have hlo : t1.regs u.2.1 = some (splitValue 64 (v u.1)).1 := by
      simp [t1, PTX.next, setReg, Function.update_of_ne (hlh u (by simp))]
    have hhi : t1.regs u.2.2.1 = some (splitValue 64 (v u.1)).2 := by
      simp [t1, PTX.next, setReg]
    obtain ⟨hA, hD⟩ := hI 0 (by simp) t1 (by simp [t1, PTX.next, setReg])
    have hex2 := exec_cvtPair_at (d := u.2.2.2) hA hD hhi hlo
    set t2 := PTX.next (setReg t1 u.2.2.2 (cvtOfPair (v u.1)))
    have hreg : ∀ q ∈ us, t2.regs q.1 = some (v q.1) := by
      intro q hq
      have h1 := hfr q (by simp [hq]) u (by simp)
      simp only [t2, t1, PTX.next, setReg, Function.update_of_ne h1.1.symm,
        Function.update_of_ne h1.2.1.symm, Function.update_of_ne h1.2.2.symm]
      exact hv q (by simp [hq])
    have hpc2 : t2.pc = t.pc + 2 := by simp [t2, t1, PTX.next, setReg]
    have ih := unpackCvts_run hM v us t2 (by rw [hpc2]; exact hc.2.2) hf hreg
      (fun q hq => hp q (by simp [hq])) (fun q hq => hlh q (by simp [hq]))
      (fun q hq q' hq' => hfr q (by simp [hq]) q' (by simp [hq']))
      (fun i hi => by
        have := hS (i + 2) (by simp; omega)
        rwa [show t.pc + (i + 2) = t2.pc + i by rw [hpc2]; omega] at this)
      (fun i hi s hs' => hI (i + 1) (by simp; omega) s (by rw [hs', hpc2]; omega))
    have hc2 : K.code[t1.pc]? = some ⟨none, .cvt (cvtPairInstr u.2.2.2 u.2.2.1 u.2.1)⟩ := by
      rw [show t1.pc = t.pc + 1 by simp [t1, PTX.next, setReg]]; exact hc.2.1
    rcases hE : cvtPairE (splitValue 64 (v u.1)).2 (splitValue 64 (v u.1)).1 with e | w
    · rw [hE] at hex2
      refine ⟨fun h => by simp [cvtsOk, hE, Except.toBool] at h, fun _ => ?_⟩
      exact Machine.dead_of_tau o1 (dead_of_error hc2 rfl hf hex2)
    · rw [hE] at hex2
      have hw : cvtOfPair (v u.1) = w := by simp [cvtOfPair, cvtPairV, hE]
      have o2 : out K A L g t1 = .tau t2 := by
        rw [tau_of_ok hc2 rfl hf hex2]; simp only [t2, hw]
      have he : cvtsOk v (u :: us) = cvtsOk v us := by simp [cvtsOk, hE, Except.toBool]
      refine ⟨fun h => ?_, fun h =>
        Machine.dead_of_tau o1 (Machine.dead_of_tau o2 (ih.2 (he ▸ h)))⟩
      simp only [List.length_cons, show 2 * (us.length + 1) = 2 * us.length + 1 + 1 by ring,
        run, tauStep, o1, o2, Option.bind_some, unpackCvtRun]
      exact ih.1 (he ▸ h)

/-- The destinations of a run of unpacks hold the halves of their sources, when no two
destinations coincide. -/
theorem unpackRun_val (v : Nat → Value) : ∀ (us : List (Nat × Nat × Nat)) (t : TState),
    (us.flatMap fun u => [u.2.1, u.2.2]).Nodup → ∀ u ∈ us,
      (unpackRun v t us).regs u.2.1 = some (splitValue 64 (v u.1)).1 ∧
        (unpackRun v t us).regs u.2.2 = some (splitValue 64 (v u.1)).2
  | [], _, _, u, hu => by simp at hu
  | u :: us, t, hnd, u', hu' => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and] at hnd
    obtain ⟨⟨hlh, hlo⟩, hhi, hnd⟩ := hnd
    rcases List.mem_cons.mp hu' with rfl | hu'
    · have hfr : ∀ q ∈ us, q.2.1 ≠ u'.2.1 ∧ q.2.2 ≠ u'.2.1 := fun q hq =>
        ⟨fun h => (hlo q hq).1 h.symm, fun h => (hlo q hq).2.1 h.symm⟩
      have hfr2 : ∀ q ∈ us, q.2.1 ≠ u'.2.2 ∧ q.2.2 ≠ u'.2.2 := fun q hq =>
        ⟨fun h => (hhi q hq).1 h.symm, fun h => (hhi q hq).2.1 h.symm⟩
      rw [unpackRun, unpackRun_other v us _ hfr, unpackRun_other v us _ hfr2]
      simp [PTX.next, setReg, Function.update_of_ne hlh]
    · exact unpackRun_val v us _ hnd u' hu'

/-- The conversion destinations of a run of unpacks with conversions hold the converted pairs,
when no destination of the run is written twice. -/
theorem unpackCvtRun_val (v : Nat → Value) : ∀ (us : List (Nat × Nat × Nat × Nat))
    (t : TState), (∀ u ∈ us, ∀ u' ∈ us, u' ≠ u →
      u'.2.1 ≠ u.2.2.2 ∧ u'.2.2.1 ≠ u.2.2.2 ∧ u'.2.2.2 ≠ u.2.2.2) → us.Nodup → ∀ u ∈ us,
      (unpackCvtRun v t us).regs u.2.2.2 = some (cvtOfPair (v u.1))
  | [], _, _, _, u, hu => by simp at hu
  | u :: us, t, hd, hnd, u', hu' => by
    rcases List.mem_cons.mp hu' with rfl | hu'
    · have hnin := (List.nodup_cons.mp hnd).1
      rw [unpackCvtRun, unpackCvtRun_other v us _ (fun q hq =>
        hd u' (by simp) q (by simp [hq]) (fun h => hnin (h ▸ hq)))]
      simp [PTX.next, setReg]
    · exact unpackCvtRun_val v us _ (fun q hq q' hq' => hd q (by simp [hq]) q' (by simp [hq']))
        (List.nodup_cons.mp hnd).2 u' hu'

end
end PTX.Flow
