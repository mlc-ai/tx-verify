-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmTotD

@[expose] public section

/-! # The 16 software exponentials on any input (pcs 1913 to 2088)

Instance `i` (pc `1913 + 11 i`) reads the exponent of column `colR i` (`%r(827 + 2 colR i)`) and
writes `%r(810 + i)`. Its temporaries are the registers `2512 + 6 i` to `2517 + 6 i` (`c`, `r`,
`rb`, `f`, `p`, `e`). What Core does with it depends on how the input reads in the extended reals
(`readEReal`), which decides whether `Assumptions.swExp2` takes the instance as one step:

* a number or `-inf` (`some (.ok x)`, `x ≠ ⊤`): the segment rule writes the exact `2 ^ x`;
* `+inf` or a value that is no `.f32` datum: the segment rule faults, the thread is dead;
* a NaN (`none`): the segment rule declines and the 11 instructions run one by one under the
  local rules. Their outcomes are composed here (`nanY`), and the thread is dead where one faults
  (`nanOk`). Whether this path faults, and which word it leaves, is not evaluated: the machine
  records the outcome. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-! ### The path of a NaN input, one instruction at a time -/


theorem nE2_bits (v : Value) : ∃ y, nE2 v = .bits 32 y := by
  unfold nE2 nE2E shlE
  rcases readBitsOf 32 (nE1 v) with e | x
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem nY1_not_ptr (v : Value) : ∀ w gn tg off, nY1 v ≠ .ptr w gn tg off := by
  have hP : ∀ w gn tg off, nP3 v ≠ .ptr w gn tg off := by
    unfold nP3
    rcases h : nP3E v with e | x
    · intro w gn tg off hh; cases hh
    · exact (floatE_dat rfl h).not_ptr
  unfold nY1 nY1E
  rcases h : movE (nP3 v) with e | x
  · intro w gn tg off hh; cases hh
  · rw [movE_eq h]; exact hP

/-! ### The registers and the code of instance `i` -/

/-- The input, the temporaries and the output of instance `i`. -/
abbrev rX (i : Nat) : Nat := 1288 + 2 * colR i
abbrev rB (i : Nat) : Nat := 2512 + 6 * i
abbrev rY (i : Nat) : Nat := 1271 + i

/-- The instruction at `pc` is the floating instruction `f`. -/
def fAt (pc : Nat) (f : FloatInstr) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .float f'⟩ => f' == f
  | _ => false

theorem fAt_spec {pc : Nat} {f : FloatInstr} (h : fAt pc f = true) :
    kernel.code[pc]? = some ⟨none, .float f⟩ := by
  unfold fAt at h
  split at h
  · rename_i f' hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

/-- The instruction at `pc` is the move `m`. -/
def mAt (pc : Nat) (m : MoveInstr) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .move m'⟩ => m' == m
  | _ => false

theorem mAt_spec {pc : Nat} {m : MoveInstr} (h : mAt pc m = true) :
    kernel.code[pc]? = some ⟨none, .move m⟩ := by
  unfold mAt at h
  split at h
  · rename_i m' hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

/-- The instruction at `pc` is the integer instruction `ii`. -/
def iAt (pc : Nat) (ii : IntInstr) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .int i'⟩ => i' == ii
  | _ => false

theorem iAt_spec {pc : Nat} {ii : IntInstr} (h : iAt pc ii = true) :
    kernel.code[pc]? = some ⟨none, .int ii⟩ := by
  unfold iAt at h
  split at h
  · rename_i i' hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

/-- The shift of instance `i`. -/
abbrev shlI (i : Nat) : IntInstr :=
  ⟨.shl, .int .b 32, false, [some (rB i + 5)], [.reg (rB i + 5), .imm 23]⟩
/-- The integer addition of instance `i`. -/
abbrev addSI (i : Nat) : IntInstr :=
  ⟨.add, .int .s 32, false, [some (rY i)], [.reg (rY i), .reg (rB i + 5)]⟩

/-- The 11 instructions of instance `i`, as the step lemmas take them. -/
def emuCode (i : Nat) : Bool :=
  let p := 1913 + 11 * i
  let B := rB i
  fAt p { maxFI with dsts := [some B], srcs := [.reg (rX i), .f32imm 3271426048] } &&
  fAt (p + 1) { addRmI with dsts := [some (B + 1)], srcs := [.reg B, .f32imm 1262485504] } &&
  fAt (p + 2) { subRnI with
    dsts := [some (B + 2)], srcs := [.reg (B + 1), .f32imm 1262485504] } &&
  fAt (p + 3) { subRnI with dsts := [some (B + 3)], srcs := [.reg B, .reg (B + 2)] } &&
  fAt (p + 4) { fmaI .rn true with
    dsts := [some (B + 4)], srcs := [.reg (B + 3), .f32imm 1033760925, .f32imm 1047070372] } &&
  fAt (p + 5) { fmaI .rn true with
    dsts := [some (B + 4)], srcs := [.reg (B + 4), .reg (B + 3), .f32imm 1060238617] } &&
  fAt (p + 6) { fmaI .rn true with
    dsts := [some (B + 4)], srcs := [.reg (B + 4), .reg (B + 3), .f32imm 1065353216] } &&
  mAt (p + 7) ⟨.scalar, .int .b 32, [some (B + 5)], [.reg (B + 1)]⟩ &&
  iAt (p + 8) (shlI i) &&
  mAt (p + 9) ⟨.scalar, .int .b 32, [some (rY i)], [.reg (B + 4)]⟩ &&
  iAt (p + 10) (addSI i)

theorem emu_code : ∀ i < 16, emuCode i = true := by decide +kernel

/-- The 11 instructions of instance `i`. -/
theorem emu_codes {i : Nat} (hi : i < 16) :
    let p := 1913 + 11 * i
    let B := rB i
    kernel.code[p]? = some ⟨none, .float { maxFI with
      dsts := [some B], srcs := [.reg (rX i), .f32imm 3271426048] }⟩ ∧
    kernel.code[p + 1]? = some ⟨none, .float { addRmI with
      dsts := [some (B + 1)], srcs := [.reg B, .f32imm 1262485504] }⟩ ∧
    kernel.code[p + 2]? = some ⟨none, .float { subRnI with
      dsts := [some (B + 2)], srcs := [.reg (B + 1), .f32imm 1262485504] }⟩ ∧
    kernel.code[p + 3]? = some ⟨none, .float { subRnI with
      dsts := [some (B + 3)], srcs := [.reg B, .reg (B + 2)] }⟩ ∧
    kernel.code[p + 4]? = some ⟨none, .float { fmaI .rn true with
      dsts := [some (B + 4)], srcs := [.reg (B + 3), .f32imm 1033760925, .f32imm 1047070372] }⟩ ∧
    kernel.code[p + 5]? = some ⟨none, .float { fmaI .rn true with
      dsts := [some (B + 4)], srcs := [.reg (B + 4), .reg (B + 3), .f32imm 1060238617] }⟩ ∧
    kernel.code[p + 6]? = some ⟨none, .float { fmaI .rn true with
      dsts := [some (B + 4)], srcs := [.reg (B + 4), .reg (B + 3), .f32imm 1065353216] }⟩ ∧
    kernel.code[p + 7]? =
      some ⟨none, .move ⟨.scalar, .int .b 32, [some (B + 5)], [.reg (B + 1)]⟩⟩ ∧
    kernel.code[p + 8]? = some ⟨none, .int (shlI i)⟩ ∧
    kernel.code[p + 9]? =
      some ⟨none, .move ⟨.scalar, .int .b 32, [some (rY i)], [.reg (B + 4)]⟩⟩ ∧
    kernel.code[p + 10]? = some ⟨none, .int (addSI i)⟩ := by
  have := emu_code i hi
  simp only [emuCode, Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := this
  exact ⟨fAt_spec h0, fAt_spec h1, fAt_spec h2, fAt_spec h3, fAt_spec h4, fAt_spec h5,
    fAt_spec h6, mAt_spec h7, iAt_spec h8, mAt_spec h9, iAt_spec h10⟩

theorem emu_inner : ∀ i < 16, ∀ k < 10,
    Assumptions.emuSites.contains (1913 + 11 * i + (k + 1)) = false := by decide +kernel

theorem emu_w : ∀ i < 16, emuW (1913 + 11 * i) =
    [rB i, rB i + 1, rB i + 2, rB i + 3, rB i + 4, rB i + 5, rY i] := by decide +kernel

/-! ### The local rules at the instance's pcs -/

/-- A stage form that the ideal rule declines takes the Core rule at a state where no assumption
takes a segment (an instance whose input is a NaN). -/
theorem declineAtSF {f : FloatForm} (hfs : f ∈ stageForms) {t : TState}
    (hS : Assumption.SegFreeAt asms L g t) (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600)
    (h3 : t.pc ≠ 807) : DeclineAt asms f L g t := by
  intro op hf hn
  have hfs' := hfs
  rw [hS.exec, execLocalRule_of_none]
  intro a ha
  by_cases hd : a ∈ asms.drop 2
  · refine asms_tail_none' h1 h2 h3 (fun c hc => ?_) a hd
    subst hc
    simp only [stageForms, List.mem_cons, List.not_mem_nil, or_false] at hfs
    rcases hfs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Assumption.FloatForm.ofOp] at hf
      split_ifs at hf <;> simp at hf
  · simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false,
      List.drop_succ_cons, List.drop_zero] at ha hd
    rcases ha with rfl | rfl | ha'
    · simp only [Assumptions.idealArith, Assumption.idealReal, hf]
      split_ifs with hm
      · exact hn
      · exact absurd hfs' hm
    · exact Assumption.approxExact_localRule_none fun f' h' => by
        rw [Flow.approxForm_none_of_float hf] at h'; cases h'
    · exact absurd ha' hd

/-- The local step where the software `exp2` assumption selects the segment `r`. -/
theorem execLocalA_sw {t : TState} {op : Op} {r : Exec TState}
    (h : (Assumptions.swExp2 kernel).segmentRule L g t = some r) :
    execLocalA asms L g t op = r := by
  have h1 : Assumptions.idealArith.segmentRule L g t = none := rfl
  have h2 : Assumptions.approx.segmentRule L g t = none := rfl
  simp only [execLocalA, asms, Assumptions.all, List.findSome?_cons, h1, h2, h]

/-- The segment rule at an instance whose input register holds `v`. -/
theorem swRule_eq {i : Nat} (hi : i < 16) {t : TState} {v : Value} {F : List (Nat × Value)}
    (ht : At t (1913 + 11 * i) F) (hx : t.regs (rX i) = some v) :
    (Assumptions.swExp2 kernel).segmentRule L g t =
      Assumptions.execEmu (emuAsg (1913 + 11 * i)) t := by
  obtain ⟨hok, -, -, -, -⟩ := emu_chk i hi
  simp only [emuOk, Bool.and_eq_true] at hok
  obtain ⟨⟨hs, hm⟩, -⟩ := hok
  obtain ⟨asg, hasg⟩ := Option.isSome_iff_exists.mp hm
  have hea : emuAsg (1913 + 11 * i) = asg := by simp [emuAsg, hasg]
  show (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
    (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) []).bind
      (Assumptions.execEmu · t) else none) = _
  rw [if_pos ⟨by rw [ht.1]; exact hs, ht.2.1, by simp [ht.2.2.1]⟩, ht.1, hasg, hea]
  rfl

/-- The segment rule's reading of the input register. -/
theorem execEmu_read {i : Nat} (hi : i < 16) {t : TState} {v : Value}
    (hx : t.regs (rX i) = some v) :
    readERealOpnd t .f32 (.reg (Assumptions.emuReg (emuAsg (1913 + 11 * i)) .x)) =
      readEReal .f32 v := by
  obtain ⟨-, hxr, -, -, -⟩ := emu_chk i hi
  rw [hxr]
  exact readERealOpnd_reg hx

/-! ### The cases of the input -/

/-- The overlay's input of instance `i` and the facts' coverage after it. -/
structure EmuIn (i : Nat) (base : Nat → Value) (ex : List (Nat × Value)) (v : Value) : Prop where
  hi : i < 16
  x : valueEx base ex (rX i) = v

theorem emuIn_reg {i : Nat} {base : Nat → Value} {ex : List (Nat × Value)} {v : Value}
    (hI : EmuIn i base ex v) {t : TState}
    (ht : At t (1913 + 11 * i) (factsFrom (Flow.live (1913 + 11 * i)) (valueEx base ex))) :
    t.regs (rX i) = some v :=
  reg_of ht.2.2.2.2 (emu_chk i hI.hi).2.2.2.1 hI.x

theorem emu_cov {i : Nat} (hi : i < 16) : ∀ r ∈ Flow.live (1913 + 11 * i + 11),
    r = rY i ∨ (r ≠ rB i ∧ r ≠ rB i + 1 ∧ r ≠ rB i + 2 ∧ r ≠ rB i + 3 ∧ r ≠ rB i + 4 ∧
      r ≠ rB i + 5 ∧ r ≠ rY i ∧ r ∈ Flow.live (1913 + 11 * i)) := by
  obtain ⟨-, -, hy, -, hc⟩ := emu_chk i hi
  intro r hr
  have := List.all_eq_true.mp hc r hr
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at this
  rcases this with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · rw [emu_w i hi] at h2
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq] at h2
    refine Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by simpa using h3⟩ <;> omega

/-- **A number or `-inf`**: the segment rule writes the exact power of two. -/
theorem segEmuNum {i : Nat} {base : Nat → Value} {ex : List (Nat × Value)} {v : Value} {x : EReal}
    (hI : EmuIn i base ex v) (hr : readEReal .f32 v = some (.ok x)) (hx : x ≠ ⊤) :
    Seg kernel asms L g 1 (1913 + 11 * i)
      (factsFrom (Flow.live (1913 + 11 * i)) (valueEx base ex)) (1913 + 11 * i + 11)
      (factsFrom (Flow.live (1913 + 11 * i + 11))
        (valueEx base ((rY i, .float .f32 (Softmax.pow2 x)) :: ex))) := by
  obtain ⟨hok, hxr, hyr, hl, hc⟩ := emu_chk i hI.hi
  have h0 := hok
  simp only [emuOk, Bool.and_eq_true] at h0
  obtain ⟨⟨hs, hm⟩, hcf⟩ := h0
  obtain ⟨asg, hasg⟩ := Option.isSome_iff_exists.mp hm
  have hea : emuAsg (1913 + 11 * i) = asg := by simp [emuAsg, hasg]
  obtain ⟨f, hcf'⟩ : ∃ f, kernel.code[1913 + 11 * i]? = some ⟨none, .float f⟩ := by
    cases hh : kernel.code[1913 + 11 * i]? with
    | none => simp [hh] at hcf
    | some ins =>
      obtain ⟨gd, op⟩ := ins
      cases gd <;> cases op <;> simp [hh] at hcf ⊢
  rw [hea] at hxr hyr
  intro t h
  have hxreg : t.regs (Assumptions.emuReg asg .x) = some v := by
    rw [hxr]; exact emuIn_reg hI h
  have hpc : t.pc = 1913 + 11 * i := h.1
  set t' : TState := { t with
      regs := Function.update (Assumptions.emuWrites.foldl
        (fun rs s => Function.update rs (Assumptions.emuReg asg s) none) t.regs)
        (Assumptions.emuReg asg .y) (some (.float .f32 (Softmax.pow2 x))),
      pc := t.pc + Assumptions.emuBody.length, sub := 0, acc := [] } with ht'
  have hex : Assumptions.execEmu asg t = some (.ok t') := by
    simp only [Assumptions.execEmu, readERealOpnd_reg hxreg, hr, bindRead, hx, ↓reduceIte, pure,
      Except.pure]
    rfl
  have hrule : (Assumptions.swExp2 kernel).segmentRule L g t = some (.ok t') := by
    show (if Assumptions.emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
      (Assumptions.matchEmu Assumptions.emuBody (kernel.code.drop t.pc) []).bind
        (Assumptions.execEmu · t) else none) = _
    rw [if_pos ⟨by rw [hpc]; exact hs, h.2.1, by simp [h.2.2.1]⟩, hpc, hasg]
    exact hex
  have hrun : run kernel asms L g 1 t = some t' :=
    run_select (A₁ := [Assumptions.idealArith, Assumptions.approx])
      (A₂ := [Assumptions.lg2Exact, Assumptions.divFullExact, Assumptions.negExact,
        Assumptions.bf16Exact, Assumptions.commitOrder, Assumptions.pollAgree,
        Assumptions.setMaxNRegSync, Assumptions.inputReadOnly]) hcf' rfl h hrule
  refine ⟨t', hrun, ?_, rfl, rfl, h.2.2.2.1, ?_⟩
  · simp only [ht', hpc]; rfl
  · have hw : emuW (1913 + 11 * i) = Assumptions.emuWrites.map (Assumptions.emuReg asg) := by
      simp [emuW, hea]
    refine holds_ext (W := emuW (1913 + 11 * i)) (ys := [(rY i, .float .f32 (Softmax.pow2 x))])
      h.2.2.2.2 (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_)
    · rw [hw] at hr
      have hy : r ≠ Assumptions.emuReg asg .y := fun he => hr (List.mem_map.mpr
        ⟨.y, by simp [Assumptions.emuWrites], he.symm⟩)
      simp only [ht']
      rw [Function.update_of_ne hy]
      exact foldl_update_other (f := Assumptions.emuReg asg) (v := fun _ => none) _
        (fun s hs he => hr (List.mem_map.mpr ⟨s, hs, he⟩))
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
      subst hr
      simp [ht', hyr]
    · rcases (emu_cov hI.hi) r hr with he | ⟨h1, h2, h3, h4, h5, h6, h7, hl'⟩
      · exact Or.inl (by simp [he])
      · refine Or.inr ⟨?_, hl'⟩
        rw [emu_w i hI.hi]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega

/-- **An input whose segment faults** (`+inf` or no `.f32` datum): the thread is dead. -/
theorem deadEmu {i : Nat} {base : Nat → Value} {ex : List (Nat × Value)} {v : Value}
    {f : Fault} (hI : EmuIn i base ex v)
    (hr : readEReal .f32 v = some (.ok ⊤) ∨ readEReal .f32 v = some (.error f)) {t : TState}
    (h : At t (1913 + 11 * i) (factsFrom (Flow.live (1913 + 11 * i)) (valueEx base ex))) :
    Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t := by
  have hx := emuIn_reg hI h
  have hrule := swRule_eq (L := L) (g := g) hI.hi h hx
  have hcode := (emu_codes hI.hi).1
  obtain ⟨e', he'⟩ : ∃ e', Assumptions.execEmu (emuAsg (1913 + 11 * i)) t = some (.error e') := by
    unfold Assumptions.execEmu
    rw [execEmu_read hI.hi hx]
    rcases hr with hr | hr <;> rw [hr]
    · exact ⟨_, by simp [bindRead]; rfl⟩
    · exact ⟨_, rfl⟩
  rw [he'] at hrule
  have hc' := hcode
  rw [← h.1] at hc'
  exact dead_of_error hc' rfl h.2.2.2.1 (execLocalA_sw hrule)

/-! ### A NaN input: the 11 instructions one by one -/

/-- One instruction that writes `d`: the facts grow by `d` with the outcome's value. -/
theorem SegD.grow {pc d : Nat} {op : Op} {Ls : List Nat} {base : Nat → Value}
    {ex : List (Nat × Value)} {E : Exec Value}
    (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hex : ∀ t, At t pc (factsFrom Ls (valueEx base ex)) →
      execLocalA asms L g t op = E.map fun x => PTX.next (setReg t d x)) :
    SegD kernel asms L g 1 pc (factsFrom Ls (valueEx base ex)) (pc + 1)
      (factsFrom (d :: Ls) (valueEx base ((d, okVal (b32 0) E) :: ex))) (E.toBool = true) := by
  refine SegD.oneT hc hl hex (fun x hx _ => ?_) (fun r hr => ?_)
  · rw [valueEx_cons_self]; exact okVal_of_ok hx
  · rcases List.mem_cons.mp hr with rfl | hr'
    · exact Or.inl rfl
    · by_cases hrd : r = d
      · exact Or.inl hrd
      · exact Or.inr ⟨hrd, hr', valueEx_cons_ne _ _ hrd⟩

/-- Read a register of an overlay: the newest entry of its key. -/
macro "vx" : tactic => `(tactic| repeat (first | rw [valueEx_cons_self] |
  rw [valueEx_cons_ne _ _ (by omega)]))

/-- No assumption takes a segment at an instance whose input is a NaN. -/
theorem segFreeNaN {i : Nat} (hi : i < 16) {t : TState} {v : Value} {F : List (Nat × Value)}
    (ht : At t (1913 + 11 * i) F) (hx : t.regs (rX i) = some v)
    (hn : readEReal .f32 v = none) : Assumption.SegFreeAt asms L g t := by
  have hsw : (Assumptions.swExp2 kernel).segmentRule L g t = none := by
    rw [swRule_eq hi ht hx]
    unfold Assumptions.execEmu
    rw [execEmu_read hi hx, hn]
    rfl
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact hsw

section
variable {i : Nat} {base : Nat → Value} {ex : List (Nat × Value)} {v : Value}

theorem segN0 (hI : EmuIn i base ex v) (hn : readEReal .f32 v = none) :
    SegD kernel asms L g 1 (1913 + 11 * i)
      (factsFrom (Flow.live (1913 + 11 * i)) (valueEx base ex)) (1913 + 11 * i + 1)
      (factsFrom (rB i :: Flow.live (1913 + 11 * i))
        (valueEx base ((rB i, nC v) :: ex))) ((nCE v).toBool = true) := by
  refine SegD.grow (emu_codes hI.hi).1 rfl (fun t h => ?_)
  have hx := emuIn_reg hI h
  have hS := segFreeNaN (L := L) (g := g) hI.hi h hx hn
  have hp : t.pc = 1913 + 11 * i := h.1
  have hi := hI.hi
  exact exec_maxFE_nan (declineAtSF (L := L) (g := g) (by decide) hS (by omega) (by omega)
    (by omega)) hn (OpndIs.reg hx) OpndIs.imm

/-- The overlays of the NaN path after `k` instructions. -/
abbrev nx1 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rB i, nC v) :: ex
abbrev nx2 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rB i + 1, nR v) :: nx1 i v ex
abbrev nx3 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rB i + 2, nRb v) :: nx2 i v ex
abbrev nx4 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rB i + 3, nF v) :: nx3 i v ex
abbrev nx5 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rB i + 4, nP1 v) :: nx4 i v ex
abbrev nx6 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rB i + 4, nP2 v) :: nx5 i v ex
abbrev nx7 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rB i + 4, nP3 v) :: nx6 i v ex
abbrev nx8 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rB i + 5, nE1 v) :: nx7 i v ex
abbrev nx9 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rB i + 5, nE2 v) :: nx8 i v ex
abbrev nx10 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rY i, nY1 v) :: nx9 i v ex
abbrev nx11 (i : Nat) (v : Value) (ex : List (Nat × Value)) := (rY i, nanY v) :: nx10 i v ex

theorem emuE {i k : Nat} (hi : i < 16) (hk : k < 10) {t : TState}
    (h : t.pc = 1913 + 11 * i + (k + 1)) : Assumptions.emuSites.contains t.pc = false := by
  rw [h]; exact emu_inner i hi k hk

theorem segN1 (hi : i < 16) (Ls : List Nat) :
    SegD kernel asms L g 1 (1913 + 11 * i + 1)
      (factsFrom (rB i :: Ls) (valueEx base (nx1 i v ex))) (1913 + 11 * i + 1 + 1)
      (factsFrom ((rB i + 1) :: rB i :: Ls) (valueEx base (nx2 i v ex)))
      ((nRE v).toBool = true) := by
  refine SegD.grow (emu_codes hi).2.1 rfl (fun t h => ?_)
  have hE := emuE hi (k := 0) (by omega) h.1
  have hp : t.pc = 1913 + 11 * i + 1 := h.1
  have rc : t.regs (rB i) = some (nC v) := reg_of h.2.2.2.2 (by simp) (by vx)
  exact exec_floatE_addRm (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg rc) OpndIs.imm

theorem segN2 (hi : i < 16) (Ls : List Nat) :
    SegD kernel asms L g 1 (1913 + 11 * i + 2)
      (factsFrom ((rB i + 1) :: Ls) (valueEx base (nx2 i v ex))) (1913 + 11 * i + 2 + 1)
      (factsFrom ((rB i + 2) :: (rB i + 1) :: Ls) (valueEx base (nx3 i v ex)))
      ((nRbE v).toBool = true) := by
  refine SegD.grow (emu_codes hi).2.2.1 rfl (fun t h => ?_)
  have hE := emuE hi (k := 1) (by omega) h.1
  have hp : t.pc = 1913 + 11 * i + 2 := h.1
  have rr : t.regs (rB i + 1) = some (nR v) := reg_of h.2.2.2.2 (by simp) (by vx)
  exact exec_subRnE (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg rr) OpndIs.imm

theorem segN3 (hi : i < 16) (Ls : List Nat) (hc : rB i ∈ Ls) :
    SegD kernel asms L g 1 (1913 + 11 * i + 3)
      (factsFrom ((rB i + 2) :: Ls) (valueEx base (nx3 i v ex))) (1913 + 11 * i + 3 + 1)
      (factsFrom ((rB i + 3) :: (rB i + 2) :: Ls) (valueEx base (nx4 i v ex)))
      ((nFE v).toBool = true) := by
  refine SegD.grow (emu_codes hi).2.2.2.1 rfl (fun t h => ?_)
  have hE := emuE hi (k := 2) (by omega) h.1
  have hp : t.pc = 1913 + 11 * i + 3 := h.1
  have rc : t.regs (rB i) = some (nC v) := reg_of h.2.2.2.2 (by simp [hc]) (by vx)
  have rb : t.regs (rB i + 2) = some (nRb v) := reg_of h.2.2.2.2 (by simp) (by vx)
  exact exec_subRnE (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg rc) (OpndIs.reg rb)

theorem segN4 (hi : i < 16) (Ls : List Nat) :
    SegD kernel asms L g 1 (1913 + 11 * i + 4)
      (factsFrom ((rB i + 3) :: Ls) (valueEx base (nx4 i v ex))) (1913 + 11 * i + 4 + 1)
      (factsFrom ((rB i + 4) :: (rB i + 3) :: Ls) (valueEx base (nx5 i v ex)))
      ((nP1E v).toBool = true) := by
  refine SegD.grow (emu_codes hi).2.2.2.2.1 rfl (fun t h => ?_)
  have hE := emuE hi (k := 3) (by omega) h.1
  have hp : t.pc = 1913 + 11 * i + 4 := h.1
  have rf : t.regs (rB i + 3) = some (nF v) := reg_of h.2.2.2.2 (by simp) (by vx)
  exact exec_floatE_fma_at (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg rf) OpndIs.imm OpndIs.imm

theorem segN5 (hi : i < 16) (Ls : List Nat) (hf : rB i + 3 ∈ Ls) :
    SegD kernel asms L g 1 (1913 + 11 * i + 5)
      (factsFrom ((rB i + 4) :: Ls) (valueEx base (nx5 i v ex))) (1913 + 11 * i + 5 + 1)
      (factsFrom ((rB i + 4) :: (rB i + 4) :: Ls) (valueEx base (nx6 i v ex)))
      ((nP2E v).toBool = true) := by
  refine SegD.grow (emu_codes hi).2.2.2.2.2.1 rfl (fun t h => ?_)
  have hE := emuE hi (k := 4) (by omega) h.1
  have hp : t.pc = 1913 + 11 * i + 5 := h.1
  have rp : t.regs (rB i + 4) = some (nP1 v) := reg_of h.2.2.2.2 (by simp) (by vx)
  have rf : t.regs (rB i + 3) = some (nF v) := reg_of h.2.2.2.2 (by simp [hf]) (by vx)
  exact exec_floatE_fma_at (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg rp) (OpndIs.reg rf) OpndIs.imm

theorem segN6 (hi : i < 16) (Ls : List Nat) (hf : rB i + 3 ∈ Ls) :
    SegD kernel asms L g 1 (1913 + 11 * i + 6)
      (factsFrom ((rB i + 4) :: Ls) (valueEx base (nx6 i v ex))) (1913 + 11 * i + 6 + 1)
      (factsFrom ((rB i + 4) :: (rB i + 4) :: Ls) (valueEx base (nx7 i v ex)))
      ((nP3E v).toBool = true) := by
  refine SegD.grow (emu_codes hi).2.2.2.2.2.2.1 rfl (fun t h => ?_)
  have hE := emuE hi (k := 5) (by omega) h.1
  have hp : t.pc = 1913 + 11 * i + 6 := h.1
  have rp : t.regs (rB i + 4) = some (nP2 v) := reg_of h.2.2.2.2 (by simp) (by vx)
  have rf : t.regs (rB i + 3) = some (nF v) := reg_of h.2.2.2.2 (by simp [hf]) (by vx)
  exact exec_floatE_fma_at (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg rp) (OpndIs.reg rf) OpndIs.imm

theorem segN7 (hi : i < 16) (Ls : List Nat) (hr : rB i + 1 ∈ Ls) :
    SegD kernel asms L g 1 (1913 + 11 * i + 7)
      (factsFrom ((rB i + 4) :: Ls) (valueEx base (nx7 i v ex))) (1913 + 11 * i + 7 + 1)
      (factsFrom ((rB i + 5) :: (rB i + 4) :: Ls) (valueEx base (nx8 i v ex)))
      ((nE1E v).toBool = true) := by
  refine SegD.grow (emu_codes hi).2.2.2.2.2.2.2.1 rfl (fun t h => ?_)
  have hE := emuE hi (k := 6) (by omega) h.1
  have rr : t.regs (rB i + 1) = some (nR v) := reg_of h.2.2.2.2 (by simp [hr]) (by vx)
  exact exec_movE_at asms_movesSm ((segFree hE).at rfl) rr

theorem segN8 (hi : i < 16) (Ls : List Nat) :
    SegD kernel asms L g 1 (1913 + 11 * i + 8)
      (factsFrom ((rB i + 5) :: Ls) (valueEx base (nx8 i v ex))) (1913 + 11 * i + 8 + 1)
      (factsFrom ((rB i + 5) :: (rB i + 5) :: Ls) (valueEx base (nx9 i v ex)))
      ((nE2E v).toBool = true) := by
  refine SegD.grow (emu_codes hi).2.2.2.2.2.2.2.2.1 rfl (fun t h => ?_)
  have hE := emuE hi (k := 7) (by omega) h.1
  have re : t.regs (rB i + 5) = some (nE1 v) := reg_of h.2.2.2.2 (by simp) (by vx)
  rw [Raw.exec_int rfl (segFree hE) rfl]
  exact execInt_shl_imm rfl re

theorem segN9 (hi : i < 16) (Ls : List Nat) (hp : rB i + 4 ∈ Ls) :
    SegD kernel asms L g 1 (1913 + 11 * i + 9)
      (factsFrom ((rB i + 5) :: Ls) (valueEx base (nx9 i v ex))) (1913 + 11 * i + 9 + 1)
      (factsFrom (rY i :: (rB i + 5) :: Ls) (valueEx base (nx10 i v ex)))
      ((nY1E v).toBool = true) := by
  refine SegD.grow (emu_codes hi).2.2.2.2.2.2.2.2.2.1 rfl (fun t h => ?_)
  have hE := emuE hi (k := 8) (by omega) h.1
  have rp : t.regs (rB i + 4) = some (nP3 v) := reg_of h.2.2.2.2 (by simp [hp]) (by vx)
  exact exec_movE_at asms_movesSm ((segFree hE).at rfl) rp

theorem segN10 (hi : i < 16) (Ls : List Nat) :
    SegD kernel asms L g 1 (1913 + 11 * i + 10)
      (factsFrom (rY i :: (rB i + 5) :: Ls) (valueEx base (nx10 i v ex)))
      (1913 + 11 * i + 10 + 1)
      (factsFrom (rY i :: rY i :: (rB i + 5) :: Ls) (valueEx base (nx11 i v ex)))
      ((nY2E v).toBool = true) := by
  refine SegD.grow (emu_codes hi).2.2.2.2.2.2.2.2.2.2 rfl (fun t h => ?_)
  have hE := emuE hi (k := 9) (by omega) h.1
  obtain ⟨y, hy⟩ := nE2_bits v
  have ry : t.regs (rY i) = some (nY1 v) := reg_of h.2.2.2.2 (by simp) (by vx)
  have re : t.regs (rB i + 5) = some (.bits 32 y) :=
    reg_of h.2.2.2.2 (by simp) (by
      rw [valueEx_cons_ne _ _ (by simp only [rY, rB]; omega), valueEx_cons_self]
      exact hy)
  rw [Raw.exec_int rfl (segFree hE) rfl, execInt_add_bits ry re (nY1_not_ptr v)]
  simp only [nY2E, hy]

end

/-! ### One instance on any input, and the 16 instances -/

theorem emuYE_nan {v : Value} (h : readEReal .f32 v = none) : emuYE v = nanY v := by
  unfold emuYE; rw [h]

theorem emuOkE_nan {v : Value} (h : readEReal .f32 v = none) : emuOkE v ↔ nanOk v := by
  unfold emuOkE; rw [h]

theorem emuYE_num {v : Value} {x : EReal} (h : readEReal .f32 v = some (.ok x)) :
    emuYE v = .float .f32 (Softmax.pow2 x) := by
  unfold emuYE; rw [h]

theorem emuOkE_num {v : Value} {x : EReal} (h : readEReal .f32 v = some (.ok x)) :
    emuOkE v ↔ x ≠ ⊤ := by
  unfold emuOkE; rw [h]

theorem emuOkE_err {v : Value} {f : Fault} (h : readEReal .f32 v = some (.error f)) :
    ¬ emuOkE v := by
  unfold emuOkE; rw [h]; exact id

/-- **One software exponential on any input** (pc `1913 + 11 i`): the output register holds
`emuYE` of the input, or the thread is dead where the instance faults. -/
theorem segEmuInst {i : Nat} {base : Nat → Value} {ex : List (Nat × Value)} {v : Value}
    (hI : EmuIn i base ex v) :
    ∃ n, SegD kernel asms L g n (1913 + 11 * i)
      (factsFrom (Flow.live (1913 + 11 * i)) (valueEx base ex)) (1913 + 11 * i + 11)
      (factsFrom (Flow.live (1913 + 11 * i + 11)) (valueEx base ((rY i, emuYE v) :: ex)))
      (emuOkE v) := by
  have hi := hI.hi
  rcases hR : readEReal .f32 v with _ | (e | x)
  · refine ⟨11, ?_⟩
    rw [emuYE_nan hR]
    refine SegD.iff ?_ (emuOkE_nan hR).symm
    have c := ((((((((((segN0 (L := L) (g := g) hI hR).comp (segN1 hi _)).comp
      (segN2 hi _)).comp (segN3 hi _ (by simp))).comp (segN4 hi _)).comp
      (segN5 hi _ (by simp))).comp (segN6 hi _ (by simp))).comp (segN7 hi _ (by simp))).comp
      (segN8 hi _)).comp (segN9 hi _ (by simp))).comp (segN10 hi _)
    refine SegD.weaken_end (SegD.of_len c rfl) (fun R hR' => holds_of_pointwise fun r hr => ?_)
    rcases emu_cov hi r hr with rfl | ⟨h1, h2, h3, h4, h5, h6, h7, hl⟩
    · rw [holds_mem hR' (mem_factsFrom (show rY i ∈ _ from by simp)), valueEx_cons_self,
        valueEx_cons_self]
    · rw [holds_mem hR' (mem_factsFrom (show r ∈ _ from by simp [hl])), valueEx_cons_ne _ _ h7]
      simp only [nx10, nx9, nx8, nx7, nx6, nx5, nx4, nx3, nx2, nx1]
      rw [valueEx_cons_ne _ _ h7, valueEx_cons_ne _ _ h7, valueEx_cons_ne _ _ h6,
        valueEx_cons_ne _ _ h6, valueEx_cons_ne _ _ h5, valueEx_cons_ne _ _ h5,
        valueEx_cons_ne _ _ h5, valueEx_cons_ne _ _ h4, valueEx_cons_ne _ _ h3,
        valueEx_cons_ne _ _ h2, valueEx_cons_ne _ _ h1]
  · refine ⟨1, fun t ht => ⟨fun hc => absurd hc (emuOkE_err hR), fun _ => ?_⟩⟩
    exact deadEmu hI (Or.inr hR) ht
  · by_cases hx : x = ⊤
    · subst hx
      refine ⟨1, fun t ht => ⟨fun hc => absurd rfl ((emuOkE_num hR).mp hc), fun _ => ?_⟩⟩
      exact deadEmu (f := .badValue) hI (Or.inl hR) ht
    · refine ⟨1, ?_⟩
      rw [emuYE_num hR]
      exact SegD.iff (SegD.of_seg (segEmuNum hI hR hx))
        ⟨fun _ => (emuOkE_num hR).mpr hx, fun _ => trivial⟩


theorem valueEx_emT_off (d : D) (recv : Value) (B : Nat → Value) (ex : List (Nat × Value))
    {r : Nat} (i : Nat) (h : ∀ k < i, r ≠ 1271 + k) :
    valueEx B (emT d recv i ++ ex) r = valueEx B ex r := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [emT, List.cons_append, valueEx_cons_ne _ _ (h i (by omega))]
    exact ih fun k hk => h k (by omega)

theorem valueEx_emT_in (d : D) (recv : Value) (B : Nat → Value) (ex : List (Nat × Value))
    {n k : Nat} (hk : k < n) : valueEx B (emT d recv n ++ ex) (1271 + k) = d.yT recv k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [emT, List.cons_append]
    by_cases h : k = n
    · subst h; exact valueEx_cons_self _ _ _ _
    · rw [valueEx_cons_ne _ _ (by omega)]
      exact ih (by omega)

/-- **The first `n` software exponentials on any words.** -/
theorem segEmuTN (d : D) (recv : Value) : ∀ n, n ≤ 16 → ∃ k,
    SegD kernel asms L g k 1913
      (factsFrom (Flow.live 1913) (valueEx (valueOf L g d) (fxT d recv 64 ++ xb10 d recv)))
      (1913 + 11 * n)
      (factsFrom (Flow.live (1913 + 11 * n))
        (valueEx (valueOf L g d) (emT d recv n ++ (fxT d recv 64 ++ xb10 d recv))))
      (∀ i < n, emuOkE (d.xT recv (colR i))) := by
  intro n
  induction n with
  | zero =>
    exact fun _ => ⟨0, SegD.iff (SegD.of_seg (Seg.refl _ _))
      ⟨fun _ j hj => absurd hj (by omega), fun _ => trivial⟩⟩
  | succ n ih =>
    intro hn
    obtain ⟨k, hk⟩ := ih (by omega)
    have hc := colR_lt n (by omega)
    have hI : EmuIn n (valueOf L g d) (emT d recv n ++ (fxT d recv 64 ++ xb10 d recv))
        (d.xT recv (colR n)) := by
      refine ⟨by omega, ?_⟩
      rw [valueEx_emT_off d recv _ _ n (fun j hj => by simp only [rX]; omega)]
      exact valueEx_fxT_in d recv _ _ hc
    obtain ⟨k2, h2⟩ := segEmuInst (L := L) (g := g) hI
    exact ⟨k + k2, SegD.iff (hk.comp h2) ⟨fun ⟨h1, h2⟩ j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact h1 j h
        · exact h2,
      fun h => ⟨fun j hj => h j (by omega), h n (by omega)⟩⟩⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
