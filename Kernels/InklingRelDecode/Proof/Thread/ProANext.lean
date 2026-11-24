-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProATac

@[expose] public section

/-! # The invariant and the abstract successor of the prologue's states

`next L g d e` is the state after event `e` at state `d`. The thread's own facts decide the
branches: the election outcome (`laneOf L g = leader`) and the predicates of the code, which are
the table's (`v_p53` …). A loaded value that is not one 32-bit word (a counter, a request
word) or not one 16-bit value (a query element), and the three loaded words when they do not
satisfy `WordsOk` (`ProADefs`), leave the machine (`some none`): the protocol layer proves that
they do not happen (`Pre.cuInput`, `Pre.seqInput`, `Pre.btInput`, `Pre.qInput`). The three
broadcasts of the warp index (`psh0` … `psh2`) are followed for every received word: the word is
recorded (`Dat.sh0` …), and after the election that follows, the `and.b32` that reads it faults
when it has no bits (`none`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- What the machine needs of the three loaded words, once all three are loaded (they are the
request's `cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]` and `seq_lens[req]`): the request has
`q_len = cu1 - cu0` tokens, at most `seq_lens`, all numbers below `2 ^ 31` (no wrap-around of
the 32-bit arithmetic), and the numerators of the two signed divisions (`%r176 = num_splits - 1 -
split + ⌈seq_lens / 128⌉` and `%r217 = num_splits - 1 - split + ⌊past / 128⌋`) are non-negative
32-bit signed words: `div.s32` has a rule only for a quotient rounded toward zero. -/
def WordsOk (L : Launch) (g : Nat) (dt : Dat) : Prop :=
  (dt.cu0 ≤ dt.cu1 ∧ dt.cu1 < 2 ^ 31 ∧ dt.cu1 - dt.cu0 ≤ dt.sk ∧ dt.sk + 255 < 2 ^ 31) ∧
  0 ≤ intOf IType.s 32 (truncBits 32 (v_r176 L g dt)) ∧
  0 ≤ intOf IType.s 32 (truncBits 32 (v_r217 L g dt))

instance (L : Launch) (g : Nat) (dt : Dat) : Decidable (WordsOk L g dt) := by
  unfold WordsOk; infer_instance

/-- `div.s32` of two 32-bit register values has a rule (Core's `intDiv`: a non-zero divisor and,
for operands of opposite signs, an exact quotient). -/
def divOk (x y : BitVec 64) : Bool :=
  match intDiv IType.s 32 (truncBits 32 x) (truncBits 32 y) with
  | .ok _ => true
  | .error _ => false

/-- The division of pc 59 (`%r25 = %r176 / %r71`) has a rule. -/
abbrev div59 (L : Launch) (g : Nat) (dt : Dat) : Bool := divOk (v_r176 L g dt) (v_r71 L g dt)

/-- The division of pc 182 (`%r218 = %r217 / %r71`) has a rule. -/
abbrev div182 (L : Launch) (g : Nat) (dt : Dat) : Bool := divOk (v_r217 L g dt) (v_r71 L g dt)

/-- A loaded value that is one 32-bit word, as a number. -/
def word32 : Value → Option Nat
  | .bits 32 x => if x.toNat < 2 ^ 32 then some x.toNat else none
  | _ => none

theorem word32_spec {v : Value} {x : Nat} (h : word32 v = some x) : v = b32 x ∧ x < 2 ^ 32 := by
  cases v with
  | bits w y =>
    by_cases hw : w = 32
    · subst hw
      simp only [word32] at h
      split_ifs at h with h1
      obtain rfl := Option.some.inj h
      exact ⟨by simp [b32], h1⟩
    · exfalso
      revert h
      unfold word32
      split
      · rename_i hh
        exact absurd (Value.bits.inj hh).1 hw
      · simp
  | _ => simp [word32] at h

/-- The data after the election at `pc` gave the thread the outcome `b`. -/
def elDt (dt : Dat) (pc : Nat) (b : Bool) : Dat :=
  { dt with el := Function.update dt.el pc b }

@[simp] theorem elDt_w (dt : Dat) (pc : Nat) (b : Bool) : (elDt dt pc b).w = dt.w := rfl

/-- The data after the query load `k` returned the value `v`. -/
def qUpd (dt : Dat) (k : Nat) (v : Value) : Dat := { dt with q := Function.update dt.q k v }

/-- The first site of the query loads from the group `G` on (`G` = 0, …, 3 of 16 loads): the
first load of a group whose rows are valid, else the first store of the packed rows. -/
def qSite (L : Launch) (g : Nat) (dt : Dat) : Nat → Site
  | 0 => if v_p81 L g dt then .ldq0 else if v_p82 L g dt then .ldq16
    else if v_p83 L g dt then .ldq32 else if v_p84 L g dt then .ldq48 else .stq0_0
  | 1 => if v_p82 L g dt then .ldq16 else if v_p83 L g dt then .ldq32
    else if v_p84 L g dt then .ldq48 else .stq0_0
  | 2 => if v_p83 L g dt then .ldq32 else if v_p84 L g dt then .ldq48 else .stq0_0
  | 3 => if v_p84 L g dt then .ldq48 else .stq0_0
  | _ => .stq0_0


/-- The value of the guard of the instruction at a site (true for an unguarded one and for a
site guarded by an election's predicate, whose table value is true). -/
def guardVal (L : Launch) (g : Nat) (dt : Dat) : Site → Bool
  | .arr0 => v_p177 L g dt
  | .arr1 => v_p177 L g dt
  | .arr2 => v_p177 L g dt
  | .ldq0 => v_p81 L g dt
  | .ldq1 => v_p81 L g dt
  | .ldq2 => v_p81 L g dt
  | .ldq3 => v_p81 L g dt
  | .ldq4 => v_p81 L g dt
  | .ldq5 => v_p81 L g dt
  | .ldq6 => v_p81 L g dt
  | .ldq7 => v_p81 L g dt
  | .ldq8 => v_p81 L g dt
  | .ldq9 => v_p81 L g dt
  | .ldq10 => v_p81 L g dt
  | .ldq11 => v_p81 L g dt
  | .ldq12 => v_p81 L g dt
  | .ldq13 => v_p81 L g dt
  | .ldq14 => v_p81 L g dt
  | .ldq15 => v_p81 L g dt
  | .ldq16 => v_p82 L g dt
  | .ldq17 => v_p82 L g dt
  | .ldq18 => v_p82 L g dt
  | .ldq19 => v_p82 L g dt
  | .ldq20 => v_p82 L g dt
  | .ldq21 => v_p82 L g dt
  | .ldq22 => v_p82 L g dt
  | .ldq23 => v_p82 L g dt
  | .ldq24 => v_p82 L g dt
  | .ldq25 => v_p82 L g dt
  | .ldq26 => v_p82 L g dt
  | .ldq27 => v_p82 L g dt
  | .ldq28 => v_p82 L g dt
  | .ldq29 => v_p82 L g dt
  | .ldq30 => v_p82 L g dt
  | .ldq31 => v_p82 L g dt
  | .ldq32 => v_p83 L g dt
  | .ldq33 => v_p83 L g dt
  | .ldq34 => v_p83 L g dt
  | .ldq35 => v_p83 L g dt
  | .ldq36 => v_p83 L g dt
  | .ldq37 => v_p83 L g dt
  | .ldq38 => v_p83 L g dt
  | .ldq39 => v_p83 L g dt
  | .ldq40 => v_p83 L g dt
  | .ldq41 => v_p83 L g dt
  | .ldq42 => v_p83 L g dt
  | .ldq43 => v_p83 L g dt
  | .ldq44 => v_p83 L g dt
  | .ldq45 => v_p83 L g dt
  | .ldq46 => v_p83 L g dt
  | .ldq47 => v_p83 L g dt
  | .ldq48 => v_p84 L g dt
  | .ldq49 => v_p84 L g dt
  | .ldq50 => v_p84 L g dt
  | .ldq51 => v_p84 L g dt
  | .ldq52 => v_p84 L g dt
  | .ldq53 => v_p84 L g dt
  | .ldq54 => v_p84 L g dt
  | .ldq55 => v_p84 L g dt
  | .ldq56 => v_p84 L g dt
  | .ldq57 => v_p84 L g dt
  | .ldq58 => v_p84 L g dt
  | .ldq59 => v_p84 L g dt
  | .ldq60 => v_p84 L g dt
  | .ldq61 => v_p84 L g dt
  | .ldq62 => v_p84 L g dt
  | .ldq63 => v_p84 L g dt
  | _ => true

/-- **The base word gives `add.s32 %r30, %r2, 256` (pc 319) an outcome** (`Raw.addImmE`); on any
other word that instruction faults and the thread dies there. -/
def addOk (w : Value) : Bool :=
  match Raw.addImmE w 256 with
  | .ok _ => true
  | .error _ => false

theorem addOk_iff {w : Value} : addOk w = true ↔ ∃ x, Raw.addImmE w 256 = .ok x := by
  unfold addOk
  split <;> simp_all

/-- **The base word is good**: the word `w` the common start loaded is the 32-bit `b32 pro.tm`
and its column field has room for the 512 columns (the condition of `WComp.baseOk`). The machine
follows every word through the prologue; the composed machine stops at the prologue's last event
`bar18` (`DComp.proNext`) on any other word. -/
def wGood (dt : Dat) : Bool := decide (dt.w = b32 dt.pro.tm) && decide (dt.pro.tm + 512 ≤ 2 ^ 16)

theorem wGood_w {dt : Dat} (h : wGood dt = true) : dt.w = b32 dt.pro.tm := by
  simp only [wGood, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem wGood_col {dt : Dat} (h : wGood dt = true) : dt.pro.tm + 512 ≤ 2 ^ 16 := by
  simp only [wGood, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Bounds of the prologue's states: the inherited registers and parameters are `ArgsOk`'s, the
guard of the site's instruction holds, the query values of the loads to come are the zero of a
masked load, and every query value has two bytes. The loaded words have no invariant: each
division that reads them is tested where it runs (`div59` in the step of the third load,
`div182` in the step of `bar2`). -/
structure Inv (L : Launch) (g : Nat) (d : D) : Prop where
  args : ArgsOk L g d.dt.pro
  guard : guardVal L g d.dt d.site = true
  qz : ∀ j, d.site.qIdx ≤ j → d.dt.q j = qZero
  qb : ∀ j, (d.dt.q j).bytes = 2

/-- The abstract successor after event `e`. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .sMax =>
    some (some ⟨.ldCu0, d.dt⟩)
  | .ldCu0 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some x => some (some ⟨.ldCu1, { d.dt with cu0 := x }⟩)
        | none => some none
      | .error _ => some none
    | _ => none
  | .ldCu1 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some x => some (some ⟨.ldSk, { d.dt with cu1 := x }⟩)
        | none => some none
      | .error _ => some none
    | _ => none
  | .ldSk =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some x =>
          if WordsOk L g { d.dt with sk := x } then some (some ⟨.el0, { d.dt with sk := x }⟩)
          else some none
        | none => some none
      | .error _ => some none
    | _ => none
  | .el0 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 130 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in0, dt'⟩
        else ⟨.el1, dt'⟩))
    | _ => none
  | .in0 =>
    some (some ⟨.el1, d.dt⟩)
  | .el1 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 135 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in1, dt'⟩
        else ⟨.el2, dt'⟩))
    | _ => none
  | .in1 =>
    some (some ⟨.el2, d.dt⟩)
  | .el2 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 139 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in2, dt'⟩
        else ⟨.el3, dt'⟩))
    | _ => none
  | .in2 =>
    some (some ⟨.el3, d.dt⟩)
  | .el3 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 143 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in3, dt'⟩
        else ⟨.el4, dt'⟩))
    | _ => none
  | .in3 =>
    some (some ⟨.el4, d.dt⟩)
  | .el4 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 147 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in4, dt'⟩
        else ⟨.el5, dt'⟩))
    | _ => none
  | .in4 =>
    some (some ⟨.el5, d.dt⟩)
  | .el5 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 151 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in5, dt'⟩
        else ⟨.el6, dt'⟩))
    | _ => none
  | .in5 =>
    some (some ⟨.el6, d.dt⟩)
  | .el6 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 155 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in6, dt'⟩
        else ⟨.el7, dt'⟩))
    | _ => none
  | .in6 =>
    some (some ⟨.el7, d.dt⟩)
  | .el7 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 159 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in7, dt'⟩
        else ⟨.el8, dt'⟩))
    | _ => none
  | .in7 =>
    some (some ⟨.el8, d.dt⟩)
  | .el8 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 163 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in8, dt'⟩
        else ⟨.el9, dt'⟩))
    | _ => none
  | .in8 =>
    some (some ⟨.el9, d.dt⟩)
  | .el9 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 167 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in9, dt'⟩
        else ⟨.el10, dt'⟩))
    | _ => none
  | .in9 =>
    some (some ⟨.el10, d.dt⟩)
  | .el10 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 171 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in10, dt'⟩
        else ⟨.el11, dt'⟩))
    | _ => none
  | .in10 =>
    some (some ⟨.el11, d.dt⟩)
  | .el11 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 175 (laneOf L g == ld)
      some (some (if (v_p40 L g dt' && (laneOf L g == ld)) = true then ⟨.in11, dt'⟩
        else ⟨.fnc0, dt'⟩))
    | _ => none
  | .in11 =>
    some (some ⟨.fnc0, d.dt⟩)
  | .fnc0 =>
    some (some ⟨.bar2, d.dt⟩)
  | .bar2 =>
    if div182 L g d.dt = false ∨ ((!v_p53 L g d.dt) = true ∧ addOk d.dt.w = false) then none
    else some (some ⟨if v_p53 L g d.dt then .pbA0
      else qSite L g d.dt 0, d.dt⟩)
  | .pbA0 =>
    some (some ⟨if v_p177 L g d.dt then .arr0 else .lbA0, d.dt⟩)
  | .arr0 =>
    some (some ⟨.lbA0, d.dt⟩)
  | .lbA0 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some x => some (some ⟨.pbB0, { d.dt with b0 := x }⟩)
        | none => some none
      | .error _ => some none
    | _ => none
  | .pbB0 =>
    some (some ⟨.psh0, d.dt⟩)
  | .psh0 =>
    match e.kind with
    | .shfl _ _ _ _ v _ => some (some ⟨.pel0_0, { d.dt with sh0 := v }⟩)
    | _ => none
  | .pel0_0 =>
    match e.kind with
    | .elect _ _ ld =>
      if Raw.word32Of d.dt.sh0 = none then none else
      let dt' := elDt d.dt 203 (laneOf L g == ld)
      some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc0_0, dt'⟩
        else ⟨.pbC0, dt'⟩))
    | _ => none
  | .ptc0_0 =>
    some (some ⟨.pbC0, d.dt⟩)
  | .pbC0 =>
    some (some ⟨.pel0_1, d.dt⟩)
  | .pel0_1 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 213 (laneOf L g == ld)
      some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc0_1, dt'⟩
        else ⟨.lbB0, dt'⟩))
    | _ => none
  | .ptc0_1 =>
    some (some ⟨.lbB0, d.dt⟩)
  | .lbB0 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some x => some (some ⟨.pbD0, { d.dt with b1 := x }⟩)
        | none => some none
      | .error _ => some none
    | _ => none
  | .pbD0 =>
    some (some ⟨.pel0_2, d.dt⟩)
  | .pel0_2 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 223 (laneOf L g == ld)
      some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc0_2, dt'⟩
        else ⟨.pbE0, dt'⟩))
    | _ => none
  | .ptc0_2 =>
    some (some ⟨.pbE0, d.dt⟩)
  | .pbE0 =>
    some (some ⟨.pel0_3, d.dt⟩)
  | .pel0_3 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 228 (laneOf L g == ld)
      if (!(v_p59 L g dt' && (laneOf L g == ld)) && v_p63 L g dt') = true ∧
        addOk dt'.w = false then none
      else some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc0_3, dt'⟩
        else ⟨if v_p63 L g dt' then qSite L g dt' 0 else .pbA1, dt'⟩))
    | _ => none
  | .ptc0_3 =>
    if v_p63 L g d.dt = true ∧ addOk d.dt.w = false then none
    else some (some ⟨if v_p63 L g d.dt then qSite L g d.dt 0 else .pbA1, d.dt⟩)
  | .pbA1 =>
    some (some ⟨if v_p177 L g d.dt then .arr1 else .lbA1, d.dt⟩)
  | .arr1 =>
    some (some ⟨.lbA1, d.dt⟩)
  | .lbA1 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some x => some (some ⟨.pbB1, { d.dt with b2 := x }⟩)
        | none => some none
      | .error _ => some none
    | _ => none
  | .pbB1 =>
    some (some ⟨.psh1, d.dt⟩)
  | .psh1 =>
    match e.kind with
    | .shfl _ _ _ _ v _ => some (some ⟨.pel1_0, { d.dt with sh1 := v }⟩)
    | _ => none
  | .pel1_0 =>
    match e.kind with
    | .elect _ _ ld =>
      if Raw.word32Of d.dt.sh1 = none then none else
      let dt' := elDt d.dt 245 (laneOf L g == ld)
      some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc1_0, dt'⟩
        else ⟨.pbC1, dt'⟩))
    | _ => none
  | .ptc1_0 =>
    some (some ⟨.pbC1, d.dt⟩)
  | .pbC1 =>
    some (some ⟨.pel1_1, d.dt⟩)
  | .pel1_1 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 255 (laneOf L g == ld)
      some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc1_1, dt'⟩
        else ⟨.lbB1, dt'⟩))
    | _ => none
  | .ptc1_1 =>
    some (some ⟨.lbB1, d.dt⟩)
  | .lbB1 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some x => some (some ⟨.pbD1, { d.dt with b3 := x }⟩)
        | none => some none
      | .error _ => some none
    | _ => none
  | .pbD1 =>
    some (some ⟨.pel1_2, d.dt⟩)
  | .pel1_2 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 265 (laneOf L g == ld)
      some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc1_2, dt'⟩
        else ⟨.pbE1, dt'⟩))
    | _ => none
  | .ptc1_2 =>
    some (some ⟨.pbE1, d.dt⟩)
  | .pbE1 =>
    some (some ⟨.pel1_3, d.dt⟩)
  | .pel1_3 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 270 (laneOf L g == ld)
      if (!(v_p59 L g dt' && (laneOf L g == ld)) && v_p72 L g dt') = true ∧
        addOk dt'.w = false then none
      else some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc1_3, dt'⟩
        else ⟨if v_p72 L g dt' then qSite L g dt' 0 else .pbA2, dt'⟩))
    | _ => none
  | .ptc1_3 =>
    if v_p72 L g d.dt = true ∧ addOk d.dt.w = false then none
    else some (some ⟨if v_p72 L g d.dt then qSite L g d.dt 0 else .pbA2, d.dt⟩)
  | .pbA2 =>
    some (some ⟨if v_p177 L g d.dt then .arr2 else .lbA2, d.dt⟩)
  | .arr2 =>
    some (some ⟨.lbA2, d.dt⟩)
  | .lbA2 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some x => some (some ⟨.pbB2, { d.dt with b4 := x }⟩)
        | none => some none
      | .error _ => some none
    | _ => none
  | .pbB2 =>
    some (some ⟨.psh2, d.dt⟩)
  | .psh2 =>
    match e.kind with
    | .shfl _ _ _ _ v _ => some (some ⟨.pel2_0, { d.dt with sh2 := v }⟩)
    | _ => none
  | .pel2_0 =>
    match e.kind with
    | .elect _ _ ld =>
      if Raw.word32Of d.dt.sh2 = none then none else
      let dt' := elDt d.dt 287 (laneOf L g == ld)
      some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc2_0, dt'⟩
        else ⟨.pbC2, dt'⟩))
    | _ => none
  | .ptc2_0 =>
    some (some ⟨.pbC2, d.dt⟩)
  | .pbC2 =>
    some (some ⟨.pel2_1, d.dt⟩)
  | .pel2_1 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 297 (laneOf L g == ld)
      some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc2_1, dt'⟩
        else ⟨.lbB2, dt'⟩))
    | _ => none
  | .ptc2_1 =>
    some (some ⟨.lbB2, d.dt⟩)
  | .lbB2 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some x => some (some ⟨.pbD2, { d.dt with b5 := x }⟩)
        | none => some none
      | .error _ => some none
    | _ => none
  | .pbD2 =>
    some (some ⟨.pel2_2, d.dt⟩)
  | .pel2_2 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 307 (laneOf L g == ld)
      some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc2_2, dt'⟩
        else ⟨.pbE2, dt'⟩))
    | _ => none
  | .ptc2_2 =>
    some (some ⟨.pbE2, d.dt⟩)
  | .pbE2 =>
    some (some ⟨.pel2_3, d.dt⟩)
  | .pel2_3 =>
    match e.kind with
    | .elect _ _ ld =>
      let dt' := elDt d.dt 312 (laneOf L g == ld)
      if (!(v_p59 L g dt' && (laneOf L g == ld))) = true ∧ addOk dt'.w = false then none
      else some (some (if (v_p59 L g dt' && (laneOf L g == ld)) = true then ⟨.ptc2_3, dt'⟩
        else ⟨qSite L g dt' 0, dt'⟩))
    | _ => none
  | .ptc2_3 =>
    if addOk d.dt.w = false then none
    else some (some ⟨qSite L g d.dt 0, d.dt⟩)
  | .ldq0 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 0 v
          some (some ⟨.ldq1, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq1 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 1 v
          some (some ⟨.ldq2, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq2 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 2 v
          some (some ⟨.ldq3, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq3 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 3 v
          some (some ⟨.ldq4, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq4 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 4 v
          some (some ⟨.ldq5, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq5 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 5 v
          some (some ⟨.ldq6, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq6 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 6 v
          some (some ⟨.ldq7, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq7 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 7 v
          some (some ⟨.ldq8, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq8 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 8 v
          some (some ⟨.ldq9, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq9 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 9 v
          some (some ⟨.ldq10, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq10 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 10 v
          some (some ⟨.ldq11, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq11 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 11 v
          some (some ⟨.ldq12, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq12 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 12 v
          some (some ⟨.ldq13, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq13 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 13 v
          some (some ⟨.ldq14, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq14 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 14 v
          some (some ⟨.ldq15, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq15 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 15 v
          some (some ⟨qSite L g dt' 1, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq16 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 16 v
          some (some ⟨.ldq17, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq17 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 17 v
          some (some ⟨.ldq18, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq18 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 18 v
          some (some ⟨.ldq19, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq19 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 19 v
          some (some ⟨.ldq20, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq20 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 20 v
          some (some ⟨.ldq21, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq21 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 21 v
          some (some ⟨.ldq22, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq22 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 22 v
          some (some ⟨.ldq23, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq23 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 23 v
          some (some ⟨.ldq24, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq24 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 24 v
          some (some ⟨.ldq25, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq25 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 25 v
          some (some ⟨.ldq26, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq26 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 26 v
          some (some ⟨.ldq27, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq27 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 27 v
          some (some ⟨.ldq28, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq28 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 28 v
          some (some ⟨.ldq29, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq29 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 29 v
          some (some ⟨.ldq30, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq30 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 30 v
          some (some ⟨.ldq31, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq31 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 31 v
          some (some ⟨qSite L g dt' 2, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq32 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 32 v
          some (some ⟨.ldq33, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq33 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 33 v
          some (some ⟨.ldq34, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq34 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 34 v
          some (some ⟨.ldq35, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq35 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 35 v
          some (some ⟨.ldq36, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq36 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 36 v
          some (some ⟨.ldq37, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq37 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 37 v
          some (some ⟨.ldq38, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq38 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 38 v
          some (some ⟨.ldq39, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq39 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 39 v
          some (some ⟨.ldq40, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq40 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 40 v
          some (some ⟨.ldq41, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq41 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 41 v
          some (some ⟨.ldq42, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq42 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 42 v
          some (some ⟨.ldq43, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq43 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 43 v
          some (some ⟨.ldq44, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq44 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 44 v
          some (some ⟨.ldq45, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq45 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 45 v
          some (some ⟨.ldq46, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq46 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 46 v
          some (some ⟨.ldq47, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq47 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 47 v
          some (some ⟨qSite L g dt' 3, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq48 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 48 v
          some (some ⟨.ldq49, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq49 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 49 v
          some (some ⟨.ldq50, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq50 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 50 v
          some (some ⟨.ldq51, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq51 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 51 v
          some (some ⟨.ldq52, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq52 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 52 v
          some (some ⟨.ldq53, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq53 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 53 v
          some (some ⟨.ldq54, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq54 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 54 v
          some (some ⟨.ldq55, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq55 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 55 v
          some (some ⟨.ldq56, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq56 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 56 v
          some (some ⟨.ldq57, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq57 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 57 v
          some (some ⟨.ldq58, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq58 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 58 v
          some (some ⟨.ldq59, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq59 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 59 v
          some (some ⟨.ldq60, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq60 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 60 v
          some (some ⟨.ldq61, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq61 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 61 v
          some (some ⟨.ldq62, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq62 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 62 v
          some (some ⟨.ldq63, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .ldq63 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v.bytes = 2 then
          let dt' := qUpd d.dt 63 v
          some (some ⟨.stq0_0, dt'⟩)
        else some none
      | .error _ => some none
    | _ => none
  | .stq0_0 =>
    some (some ⟨.stq0_1, d.dt⟩)
  | .stq0_1 =>
    some (some ⟨.stq0_2, d.dt⟩)
  | .stq0_2 =>
    some (some ⟨.stq0_3, d.dt⟩)
  | .stq0_3 =>
    some (some ⟨.stq1_0, d.dt⟩)
  | .stq1_0 =>
    some (some ⟨.stq1_1, d.dt⟩)
  | .stq1_1 =>
    some (some ⟨.stq1_2, d.dt⟩)
  | .stq1_2 =>
    some (some ⟨.stq1_3, d.dt⟩)
  | .stq1_3 =>
    some (some ⟨.stq2_0, d.dt⟩)
  | .stq2_0 =>
    some (some ⟨.stq2_1, d.dt⟩)
  | .stq2_1 =>
    some (some ⟨.stq2_2, d.dt⟩)
  | .stq2_2 =>
    some (some ⟨.stq2_3, d.dt⟩)
  | .stq2_3 =>
    some (some ⟨.stq3_0, d.dt⟩)
  | .stq3_0 =>
    some (some ⟨.stq3_1, d.dt⟩)
  | .stq3_1 =>
    some (some ⟨.stq3_2, d.dt⟩)
  | .stq3_2 =>
    some (some ⟨.stq3_3, d.dt⟩)
  | .stq3_3 =>
    some (some ⟨.stq4_0, d.dt⟩)
  | .stq4_0 =>
    some (some ⟨.stq4_1, d.dt⟩)
  | .stq4_1 =>
    some (some ⟨.stq4_2, d.dt⟩)
  | .stq4_2 =>
    some (some ⟨.stq4_3, d.dt⟩)
  | .stq4_3 =>
    some (some ⟨.stq5_0, d.dt⟩)
  | .stq5_0 =>
    some (some ⟨.stq5_1, d.dt⟩)
  | .stq5_1 =>
    some (some ⟨.stq5_2, d.dt⟩)
  | .stq5_2 =>
    some (some ⟨.stq5_3, d.dt⟩)
  | .stq5_3 =>
    some (some ⟨.stq6_0, d.dt⟩)
  | .stq6_0 =>
    some (some ⟨.stq6_1, d.dt⟩)
  | .stq6_1 =>
    some (some ⟨.stq6_2, d.dt⟩)
  | .stq6_2 =>
    some (some ⟨.stq6_3, d.dt⟩)
  | .stq6_3 =>
    some (some ⟨.stq7_0, d.dt⟩)
  | .stq7_0 =>
    some (some ⟨.stq7_1, d.dt⟩)
  | .stq7_1 =>
    some (some ⟨.stq7_2, d.dt⟩)
  | .stq7_2 =>
    some (some ⟨.stq7_3, d.dt⟩)
  | .stq7_3 =>
    some (some ⟨.fnc1, d.dt⟩)
  | .fnc1 =>
    some (some ⟨.st8, d.dt⟩)
  | .st8 =>
    some (some ⟨.st9_0, d.dt⟩)
  | .st9_0 =>
    some (some ⟨.st9_1, d.dt⟩)
  | .st9_1 =>
    some (some ⟨.bar18, d.dt⟩)
  | .bar18 =>
    some none

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
