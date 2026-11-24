-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Flow.Code
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.RegBits
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Local
public import Lemmas.Flow.SegFree
public import Lemmas.Flow.SegDead
public import Lemmas.Isa.Rule

@[expose] public section

/-! # Integer instructions that read a loaded word

A load puts the loaded value into its register as it is: `rebuild` returns a stored value itself
when the bytes are the pieces of one stored value (`Core/Thread/Access.lean`), so the register of
a four-byte load need not hold a 32-bit integer. The code reads such a register with `readBits`,
as the bits of its pattern (`Value.regBits`), or faults when it has none. A machine that follows
the code for every loaded value keeps the loaded value in its table; the segment evaluator cannot
read a register whose value is not a literal, so the instructions that read it are proved one at
a time: `seg_int1` makes one integer instruction a segment of one step from the rule's result at
every state of the facts, and `dead_int1` makes it a fault. `readBits_word` reads a register
holding a value with a pattern. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Raw
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The assumptions every site machine of the kernel evaluates under. -/
abbrev asms : List Assumption := Assumptions.all

/-- The 32-bit number a register holding `v` reads as (`readBits` at width 32), if it reads as
bits at all: the low 32 bits of an integer or of a bit pattern; none for a pointer or a value
without a pattern. -/
def word32Of (v : Value) : Option Nat := v.regBits.map fun x => (truncBits 32 x).toNat

theorem word32Of_lt {v : Value} {n : Nat} (h : word32Of v = some n) : n < 2 ^ 32 := by
  unfold word32Of at h
  cases hv : v.regBits with
  | none => simp [hv] at h
  | some x =>
    simp only [hv, Option.map_some, Option.some.injEq] at h
    subst h
    simp only [truncBits, BitVec.toNat_ofNat]
    omega

theorem word32Of_b32 (n : Nat) : word32Of (b32 n) = some (n % 2 ^ 32) := by
  simp [word32Of, Value.regBits, b32, truncBits, BitVec.toNat_ofNat]
  omega

/-- A register holding a word that reads as `n` reads as a 32-bit register holding `n`. -/
theorem readBits_word32 {L : Launch} {g : Nat} {t : TState} {r : Nat} {v : Value} {n : Nat}
    (hr : t.regs r = some v) (hw : word32Of v = some n) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 (BitVec.ofNat 64 n)) := by
  unfold word32Of at hw
  cases hv : v.regBits with
  | none => simp [hv] at hw
  | some x =>
    simp only [hv, Option.map_some, Option.some.injEq] at hw
    rw [readBits_regBits hr hv]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, BitVec.toNat_ofNat] at hw ⊢
    omega

/-- A word without bits faults when read as bits. -/
theorem readBits_word32_none {L : Launch} {g : Nat} {t : TState} {r : Nat} {v : Value}
    (hr : t.regs r = some v) (hw : word32Of v = none) :
    ∃ f, readBits L g t 32 (.reg r) = .error f := by
  unfold word32Of at hw
  exact readBits_regBits_none hr (by simpa using hw)

/-- `add.s32` of a register holding a word and an immediate: the word read as bits plus the
immediate (a word is no pointer, so the pointer rules do not apply). -/
theorem execInt_add_imm {L : Launch} {g : Nat} {t : TState} {d r : Nat} {imm : Int} {v : Value}
    {n : Nat} (hr : t.regs r = some v) (hw : word32Of v = some n) :
    execInt L g t ⟨.add, .int .s 32, false, [some d], [.reg r, .imm imm]⟩ =
      .ok (PTX.next (setReg t d (.bits 32 (truncBits 32
        (truncBits 32 (BitVec.ofNat 64 n) + truncBits 32 (BitVec.ofInt 64 imm)))))) := by
  have hb := readBits_word32 (L := L) (g := g) hr hw
  have hnp : ∀ w gen tg off, v ≠ .ptr w gen tg off := by
    rintro w gen tg off rfl
    simp [word32Of, Value.regBits] at hw
  simp only [execInt, readValue, readReg, hr, DType.width]
  cases v with
  | ptr w gen tg off => exact absurd rfl (hnp w gen tg off)
  | _ => simp_all [bind, Except.bind, pure, Except.pure, readBits]

/-- No assumption of the kernel has a local rule for an integer instruction. -/
theorem asms_localRule_int {L : Launch} {g : Nat} {t : TState} {i : IntInstr} :
    ∀ a ∈ asms, a.localRule L g t (.int i) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by
      simp [Assumption.FloatForm.ofOp] at h
  · exact Assumption.approxExact_localRule_none fun f h => by
      simp [Assumption.ApproxForm.ofOp] at h
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

/-- No assumption of the kernel takes a segment at a pc outside the software-`exp2` sites. -/
theorem asms_segFree {pc : Nat} (h : Assumptions.emuSites.contains pc = false) :
    Assumption.SegFreePc asms pc := by
  intro a ha L g t ht
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · rfl
  · rfl
  · have : pc ∉ Assumptions.emuSites := by simpa using h
    simp [Assumptions.swExp2, ht, this]
  all_goals rfl

/-- The local step of an integer instruction is its Core rule. -/
theorem exec_int {L : Launch} {g pc : Nat} {t : TState} {ii : IntInstr}
    (hrule : ii.rule = some .threadInt) (hsf : Assumption.SegFreePc asms pc) (hpc : t.pc = pc) :
    execLocalA asms L g t (.int ii) = execInt L g t ii := by
  have hs := Assumption.SegFreePc.of_eq hpc hsf
  simp only [hs.exec, execLocalRule_of_none (asms_localRule_int (t := t)), execLocal_int hrule]

/-- **One integer instruction** as a segment of one step: at every state of the facts `F` its
rule writes `v` to `d`, and the facts `G` hold of the registers after the write. -/
theorem seg_int1 {L : Launch} {g pc d : Nat} {ii : IntInstr} {F G : List (Nat × Value)}
    {v : Value} (hc : kernel.code[pc]? = some ⟨none, .int ii⟩)
    (hrule : ii.rule = some .threadInt) (hl : (Op.int ii).isLocal = true)
    (hsf : Assumption.SegFreePc asms pc)
    (hex : ∀ t, At t pc F → execInt L g t ii = .ok (PTX.next (setReg t d v)))
    (hG : ∀ R, Holds R F → Holds (Function.update R d (some v)) G) :
    Seg kernel asms L g 1 pc F (pc + 1) G := by
  intro t h
  have hexec : execLocalA asms L g t (.int ii) = .ok (PTX.next (setReg t d v)) := by
    rw [exec_int hrule hsf h.1]
    exact hex t h
  refine ⟨_, run_local hc hl h hexec, ?_⟩
  exact ⟨by simp [PTX.next, setReg, h.1], h.2.1, h.2.2.1, h.2.2.2.1, hG _ h.2.2.2.2⟩

/-- **One integer instruction that faults**: at every state of the facts its rule fails, so the
state is dead. -/
theorem dead_int1 {L : Launch} {g pc : Nat} {ii : IntInstr} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨none, .int ii⟩)
    (hrule : ii.rule = some .threadInt) (hl : (Op.int ii).isLocal = true)
    (hsf : Assumption.SegFreePc asms pc)
    (hex : ∀ t, At t pc F → ∃ f, execInt L g t ii = .error f) {t : TState} (h : At t pc F) :
    Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t := by
  obtain ⟨f, hf⟩ := hex t h
  have hc' : kernel.code[t.pc]? = some ⟨none, .int ii⟩ := h.1 ▸ hc
  exact dead_of_error hc' hl h.2.2.2.1 (by rw [exec_int hrule hsf h.1]; exact hf)

/-- The facts of a table at the next pc after a write of the table's value to `d`. -/
theorem holds_set_live {R : Nat → Option Value} {l1 l2 : List Nat} {val : Nat → Value}
    {d : Nat} {x : Value} (h : Holds R (factsFrom l1 val)) (hx : val d = x)
    (hl : ∀ r ∈ l2, r = d ∨ r ∈ l1) : Holds (Function.update R d (some x)) (factsFrom l2 val) := by
  refine holds_of_pointwise fun r hr => ?_
  by_cases hd : r = d
  · subst hd
    simp [hx]
  · rw [Function.update_of_ne hd]
    rcases hl r hr with h' | h'
    · exact absurd h' hd
    · exact holds_mem h (mem_factsFrom h')

/-- **The outcome of `add.s32 %d, %r, imm`** on a register holding `v` (Core's `execInt`): the
offset of a shared, local or constant pointer, else the 32-bit sum of the register's bits and the
immediate; an error for a value without bits (the instruction faults). -/
def addImmE (v : Value) (imm : Int) : Exec Value :=
  match v with
  | .ptr _ _ (.shared ..) _ | .ptr _ _ (.local _) _ | .ptr _ _ .const _ =>
    offsetPointer 32 v (toSigned 32 (truncBits 32 (BitVec.ofInt 64 imm)))
  | _ => match v.regBits with
    | some x =>
      .ok (.bits 32 (truncBits 32 (truncBits 32 x + truncBits 32 (BitVec.ofInt 64 imm))))
    | none => .error .noRule

/-- `addImmE` of a value that is not a pointer: the sum of its bits and the immediate. -/
theorem addImmE_nonptr {v : Value} {imm : Int} (hv : ∀ w gen tg off, v ≠ .ptr w gen tg off) :
    addImmE v imm = match v.regBits with
      | some x =>
        .ok (.bits 32 (truncBits 32 (truncBits 32 x + truncBits 32 (BitVec.ofInt 64 imm))))
      | none => .error .noRule := by
  cases v <;> simp_all [addImmE]

/-- `add.s32` of a register holding a value that is not a pointer and an immediate: the sum of
the register's bits and the immediate. -/
theorem execInt_add_nonptr {L : Launch} {g : Nat} {t : TState} {d r : Nat} {imm : Int}
    {v : Value} (hr : t.regs r = some v) (hv : ∀ w gen tg off, v ≠ .ptr w gen tg off) :
    execInt L g t ⟨.add, .int .s 32, false, [some d], [.reg r, .imm imm]⟩ =
      (do let x ← readBits L g t 32 (.reg r)
          pure (PTX.next (setReg t d (.bits 32
            (truncBits 32 (x + truncBits 32 (BitVec.ofInt 64 imm))))))) := by
  cases v <;> simp_all [execInt, readValue, readReg, readBits, DType.width, bind, Except.bind,
    pure, Except.pure]

/-- `add.s32` of a register and an immediate is `addImmE` of the register's value. -/
theorem execInt_addImm_ok {L : Launch} {g : Nat} {t : TState} {d r : Nat} {imm : Int}
    {v x : Value} (hr : t.regs r = some v) (hx : addImmE v imm = .ok x) :
    execInt L g t ⟨.add, .int .s 32, false, [some d], [.reg r, .imm imm]⟩ =
      .ok (PTX.next (setReg t d x)) := by
  by_cases hp : ∃ w gen tg off, v = .ptr w gen tg off
  · obtain ⟨w, gen, tg, off, rfl⟩ := hp
    cases tg <;>
      simp_all [addImmE, execInt, readValue, readReg, readBits, Value.regBits, DType.width,
        bind, Except.bind, pure, Except.pure]
  · have hv : ∀ w gen tg off, v ≠ .ptr w gen tg off := fun w gen tg off h => hp ⟨_, _, _, _, h⟩
    rw [execInt_add_nonptr hr hv]
    rw [addImmE_nonptr hv] at hx
    cases hb : v.regBits with
    | none => simp [hb] at hx
    | some x0 =>
      simp only [hb, Except.ok.injEq] at hx
      subst hx
      simp [readBits_regBits hr hb, bind, Except.bind, pure, Except.pure, truncBits]

/-- `add.s32` of a register and an immediate faults when `addImmE` of the register's value is an
error. -/
theorem execInt_addImm_err {L : Launch} {g : Nat} {t : TState} {d r : Nat} {imm : Int}
    {v : Value} (hr : t.regs r = some v) (hx : ∀ x, addImmE v imm ≠ .ok x) :
    ∃ f, execInt L g t ⟨.add, .int .s 32, false, [some d], [.reg r, .imm imm]⟩ = .error f := by
  by_cases hp : ∃ w gen tg off, v = .ptr w gen tg off
  · obtain ⟨w, gen, tg, off, rfl⟩ := hp
    cases tg <;>
      simp_all [addImmE, execInt, readValue, readReg, readBits, Value.regBits, DType.width,
        bind, Except.bind, pure, Except.pure] <;>
      first
        | (cases ho : offsetPointer _ _ _ with
            | error f => exact ⟨f, rfl⟩
            | ok y => exact absurd ho (hx y))
        | exact ⟨_, rfl⟩
  · have hv : ∀ w gen tg off, v ≠ .ptr w gen tg off := fun w gen tg off h => hp ⟨_, _, _, _, h⟩
    rw [execInt_add_nonptr hr hv]
    rw [addImmE_nonptr hv] at hx
    cases hb : v.regBits with
    | none =>
      obtain ⟨f, hf⟩ := readBits_regBits_none (L := L) (g := g) (w := 32) hr hb
      exact ⟨f, by simp [hf, bind, Except.bind]⟩
    | some x0 => simp [hb] at hx

/-- A segment followed by a conditional piece is the conditional piece. -/
theorem segD_pre {L : Launch} {g m n s p b : Nat} {F G H : List (Nat × Value)} {C : Prop}
    (h1 : Seg kernel asms L g m s F p G) (h2 : SegD kernel asms L g n p G b H C) :
    SegD kernel asms L g (m + n) s F b H C := by
  intro t ht
  obtain ⟨t1, hr1, h1'⟩ := h1 t ht
  refine ⟨fun hc => ?_, fun hc => dead_of_run hr1 ((h2 t1 h1').2 hc)⟩
  obtain ⟨t2, hr2, h2'⟩ := (h2 t1 h1').1 hc
  exact ⟨t2, run_comp hr1 hr2, h2'⟩

/-- A conditional piece followed by a segment is the conditional piece. -/
theorem segD_post {L : Launch} {g m n s p b : Nat} {F G H : List (Nat × Value)} {C : Prop}
    (h1 : SegD kernel asms L g m s F p G C) (h2 : Seg kernel asms L g n p G b H) :
    SegD kernel asms L g (m + n) s F b H C := by
  intro t ht
  refine ⟨fun hc => ?_, (h1 t ht).2⟩
  obtain ⟨t1, hr1, h1'⟩ := (h1 t ht).1 hc
  obtain ⟨t2, hr2, h2'⟩ := h2 t1 h1'
  exact ⟨t2, run_comp hr1 hr2, h2'⟩

/-- A segment is a conditional piece under a condition that holds. -/
theorem segD_of_seg {L : Launch} {g n s b : Nat} {F G : List (Nat × Value)} {C : Prop}
    (h : Seg kernel asms L g n s F b G) (hc : C) : SegD kernel asms L g n s F b G C :=
  fun t ht => ⟨fun _ => h t ht, fun hn => absurd hc hn⟩

/-- A conditional piece under an equivalent condition. -/
theorem segD_iff {L : Launch} {g n s b : Nat} {F G : List (Nat × Value)} {C C' : Prop}
    (h : SegD kernel asms L g n s F b G C) (hc : C ↔ C') : SegD kernel asms L g n s F b G C' :=
  fun t ht => ⟨fun h' => (h t ht).1 (hc.2 h'), fun hn => (h t ht).2 fun h' => hn (hc.1 h')⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Raw
