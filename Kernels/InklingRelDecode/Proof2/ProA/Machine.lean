-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProATable
public import Kernels.InklingRelDecode.Proof.Thread.ProASiteTac

@[expose] public section

/-! # The default partition's prologue as a site machine with site families

The 128 threads of warps 0 to 3 run, from `setmaxnreg.inc` (pc 27) to `barrier.sync 1` (pc 573):

* the three request words `cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]`
  (`ld k`, pcs 34, 37, 41), from which the code computes `q_len`, `past`, `num_iters` (a signed
  division at pc 59) and the row-validity predicates;
* twelve elections, each letting one lane of warp 0 initialize an mbarrier (`el i`, `init i`),
  the proxy fence and the partition's barrier (`fnc0`, `bar2`; a signed division at pc 182 gives
  `num_pre`);
* up to three preloaded K/V blocks `b` (`pb b j` the five barriers, `arr b` lane 0's
  `mbarrier.arrive.expect_tx`, `lb b h` the two block-table loads, `psh b` the broadcast of the
  warp index, `pel b j` / `ptc b j` the four elections and tensor copies);
* the 64 guarded query loads (`ldq k`), the eight `st.shared.v4.b32` of the packed rows, one
  event per element (`stq i j`), the proxy fence (`fnc1`), the role table (`st8`), the two
  elements of `(num_pre, num_iters)` (`st9 j`) and `barrier.sync 1` (`bar18`).

`exit` (pc 574, the softmax region's first event) is the fragment's exit.

The data of a state is the prologue's `ProA.Dat` (inherited registers, loaded words, query values,
election outcomes, received words, base word), and the register table is `ProA.factsAt`, which
mirrors the code (plan rule M2). The machine follows every value whose kind fits (rule M1): a
32-bit word at the word loads (`ProA.word32`), a two-byte value at the query loads, any value at
the shuffles; another kind stops it (`some none`). Where the code has no rule it is `none`: the
`and.b32` on a received word without bits, the `add.s32` of pc 319 on a base word without an
outcome (`ProA.addOk`), and the two signed divisions (pc 59 after the third request word,
`ProA.div59`; pc 182 after `bar2`, `ProA.div182`) when they have no rule, and every load whose
bytes do not rebuild (`kill`: Core sets the thread's fault). No successor tests the content of a
returned value: what the request words are is stated in the reference invariant
(`ProA/Ref.lean`), from the read-only input source.

The successor function `next0` is the flat machine's (`Proof.ProA.next`) regrouped: `Site.old`
names the flat site of a family site, and the invariant is the flat machine's at that site, so the
flat machine's step obligations transfer (`ProA/Steps.lean`). The exception is the third request
word: the flat machine still stops there unless the words satisfy `ProA.WordsOk` (the old tree's
interface relies on it), and this machine instead follows every word and lets the division of
pc 59 decide (`stepAt_ld2`). `next` is `next0` with the loads' faults (`Code.StepAt.kill`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.ProA (Dat Inh ArgsOk factsAt valueOf word32 elDt qUpd
  qZero addOk v_p40 v_p53 v_p59 v_p63 v_p72 v_p81 v_p82 v_p83 v_p84 v_p177)

noncomputable section

/-- The flat sites of the prologue's first machine. -/
abbrev OSite := PTX.Kernels.InklingRelDecode.Proof.ProA.Site

inductive Site where
  | sMax
  /-- The request words: `cu_seqlens_q[req]`, `cu_seqlens_q[req + 1]`, `seq_lens[req]`. -/
  | ld (k : Fin 3)
  | el (i : Fin 12)
  | init (i : Fin 12)
  | fnc0
  | bar2
  /-- The five barriers of preload block `b`. -/
  | pb (b : Fin 3) (j : Fin 5)
  | arr (b : Fin 3)
  /-- The two block-table loads of block `b`. -/
  | lb (b : Fin 3) (h : Fin 2)
  | psh (b : Fin 3)
  | pel (b : Fin 3) (j : Fin 4)
  | ptc (b : Fin 3) (j : Fin 4)
  | ldq (k : Fin 64)
  | stq (i : Fin 8) (j : Fin 4)
  | fnc1
  | st8
  | st9 (j : Fin 2)
  | bar18
  | exit
  deriving DecidableEq

def elPc : Fin 12 → Nat
  | 0 => 130 | 1 => 135 | 2 => 139 | 3 => 143 | 4 => 147 | 5 => 151 | 6 => 155 | 7 => 159
  | 8 => 163 | 9 => 167 | 10 => 171 | 11 => 175
def initPc (i : Fin 12) : Nat :=
  [134, 138, 142, 146, 150, 154, 158, 162, 166, 170, 174, 178].getD i 0
def pbPc (b : Fin 3) (j : Fin 5) : Nat :=
  [[192, 201, 212, 222, 227], [236, 243, 254, 264, 269], [278, 285, 296, 306, 311]].getD b []
    |>.getD j 0
def arrPc (b : Fin 3) : Nat := [193, 237, 279].getD b 0
def lbPc (b : Fin 3) (h : Fin 2) : Nat := [[197, 220], [241, 262], [283, 304]].getD b [] |>.getD h 0
def pshPc (b : Fin 3) : Nat := [202, 244, 286].getD b 0
def pelPc : Fin 3 → Fin 4 → Nat
  | 0, 0 => 203 | 0, 1 => 213 | 0, 2 => 223 | 0, 3 => 228
  | 1, 0 => 245 | 1, 1 => 255 | 1, 2 => 265 | 1, 3 => 270
  | 2, 0 => 287 | 2, 1 => 297 | 2, 2 => 307 | 2, 3 => 312
def ptcPc (b : Fin 3) (j : Fin 4) : Nat :=
  [[211, 217, 226, 231], [253, 259, 268, 273], [295, 301, 310, 315]].getD b [] |>.getD j 0

def Site.pc : Site → Nat
  | .sMax => 27
  | .ld k => [34, 37, 41].getD k 0
  | .el i => elPc i
  | .init i => initPc i
  | .fnc0 => 179
  | .bar2 => 180
  | .pb b j => pbPc b j
  | .arr b => arrPc b
  | .lb b h => lbPc b h
  | .psh b => pshPc b
  | .pel b j => pelPc b j
  | .ptc b j => ptcPc b j
  | .ldq k => 388 + 2 * k.val
  | .stq i _ => 526 + 6 * i.val
  | .fnc1 => 569
  | .st8 => 570
  | .st9 _ => 571
  | .bar18 => 573
  | .exit => 574

/-- The element of a vector store. -/
def Site.sub : Site → Nat
  | .stq _ j => j.val
  | .st9 j => j.val
  | _ => 0

/-- The query loads done before the site. -/
def Site.qIdx : Site → Nat
  | .ldq k => k.val
  | .stq _ _ | .fnc1 | .st8 | .st9 _ | .bar18 | .exit => 64
  | _ => 0

/-- A state: the next event and the data. -/
structure D where
  site : Site
  dt : Dat

/-- The flat site of the prologue's first machine (`Proof.ProA.Site`) that a site regroups. -/
def ldqOld : List OSite :=
  [.ldq0, .ldq1, .ldq2, .ldq3, .ldq4, .ldq5, .ldq6, .ldq7, .ldq8, .ldq9, .ldq10, .ldq11, .ldq12,
    .ldq13, .ldq14, .ldq15, .ldq16, .ldq17, .ldq18, .ldq19, .ldq20, .ldq21, .ldq22, .ldq23, .ldq24,
    .ldq25, .ldq26, .ldq27, .ldq28, .ldq29, .ldq30, .ldq31, .ldq32, .ldq33, .ldq34, .ldq35, .ldq36,
    .ldq37, .ldq38, .ldq39, .ldq40, .ldq41, .ldq42, .ldq43, .ldq44, .ldq45, .ldq46, .ldq47, .ldq48,
    .ldq49, .ldq50, .ldq51, .ldq52, .ldq53, .ldq54, .ldq55, .ldq56, .ldq57, .ldq58, .ldq59, .ldq60,
    .ldq61, .ldq62, .ldq63]

def stqOld : List (List OSite) :=
  [[.stq0_0, .stq0_1, .stq0_2, .stq0_3], [.stq1_0, .stq1_1, .stq1_2, .stq1_3],
    [.stq2_0, .stq2_1, .stq2_2, .stq2_3], [.stq3_0, .stq3_1, .stq3_2, .stq3_3],
    [.stq4_0, .stq4_1, .stq4_2, .stq4_3], [.stq5_0, .stq5_1, .stq5_2, .stq5_3],
    [.stq6_0, .stq6_1, .stq6_2, .stq6_3], [.stq7_0, .stq7_1, .stq7_2, .stq7_3]]

def blockOld : List (List OSite) :=
  [[.pbA0, .pbB0, .pbC0, .pbD0, .pbE0, .arr0, .lbA0, .lbB0, .psh0, .pel0_0, .pel0_1, .pel0_2,
      .pel0_3, .ptc0_0, .ptc0_1, .ptc0_2, .ptc0_3],
    [.pbA1, .pbB1, .pbC1, .pbD1, .pbE1, .arr1, .lbA1, .lbB1, .psh1, .pel1_0, .pel1_1, .pel1_2,
      .pel1_3, .ptc1_0, .ptc1_1, .ptc1_2, .ptc1_3],
    [.pbA2, .pbB2, .pbC2, .pbD2, .pbE2, .arr2, .lbA2, .lbB2, .psh2, .pel2_0, .pel2_1, .pel2_2,
      .pel2_3, .ptc2_0, .ptc2_1, .ptc2_2, .ptc2_3]]

def elOld : List OSite := [.el0, .el1, .el2, .el3, .el4, .el5, .el6, .el7, .el8, .el9, .el10, .el11]
def inOld : List OSite := [.in0, .in1, .in2, .in3, .in4, .in5, .in6, .in7, .in8, .in9, .in10, .in11]

def Site.old : Site → OSite
  | .sMax => .sMax
  | .ld k => ([.ldCu0, .ldCu1, .ldSk] : List OSite).getD k .sMax
  | .el i => elOld.getD i .sMax
  | .init i => inOld.getD i .sMax
  | .fnc0 => .fnc0
  | .bar2 => .bar2
  | .pb b j => (blockOld.getD b []).getD j .sMax
  | .arr b => (blockOld.getD b []).getD 5 .sMax
  | .lb b h => (blockOld.getD b []).getD (6 + h.val) .sMax
  | .psh b => (blockOld.getD b []).getD 8 .sMax
  | .pel b j => (blockOld.getD b []).getD (9 + j.val) .sMax
  | .ptc b j => (blockOld.getD b []).getD (13 + j.val) .sMax
  | .ldq k => ldqOld.getD k .sMax
  | .stq i j => (stqOld.getD i []).getD j .sMax
  | .fnc1 => .fnc1
  | .st8 => .st8
  | .st9 0 => .st9_0
  | .st9 1 => .st9_1
  | .bar18 => .bar18
  | .exit => .bar18

/-- The family site of a flat site. -/
def Site.ofOld : OSite → Site
  | .sMax => .sMax
  | .ldCu0 => .ld 0
  | .ldCu1 => .ld 1
  | .ldSk => .ld 2
  | .el0 => .el 0
  | .in0 => .init 0
  | .el1 => .el 1
  | .in1 => .init 1
  | .el2 => .el 2
  | .in2 => .init 2
  | .el3 => .el 3
  | .in3 => .init 3
  | .el4 => .el 4
  | .in4 => .init 4
  | .el5 => .el 5
  | .in5 => .init 5
  | .el6 => .el 6
  | .in6 => .init 6
  | .el7 => .el 7
  | .in7 => .init 7
  | .el8 => .el 8
  | .in8 => .init 8
  | .el9 => .el 9
  | .in9 => .init 9
  | .el10 => .el 10
  | .in10 => .init 10
  | .el11 => .el 11
  | .in11 => .init 11
  | .fnc0 => .fnc0
  | .bar2 => .bar2
  | .pbA0 => .pb 0 0
  | .pbB0 => .pb 0 1
  | .pbC0 => .pb 0 2
  | .pbD0 => .pb 0 3
  | .pbE0 => .pb 0 4
  | .arr0 => .arr 0
  | .lbA0 => .lb 0 0
  | .lbB0 => .lb 0 1
  | .psh0 => .psh 0
  | .pel0_0 => .pel 0 0
  | .ptc0_0 => .ptc 0 0
  | .pel0_1 => .pel 0 1
  | .ptc0_1 => .ptc 0 1
  | .pel0_2 => .pel 0 2
  | .ptc0_2 => .ptc 0 2
  | .pel0_3 => .pel 0 3
  | .ptc0_3 => .ptc 0 3
  | .pbA1 => .pb 1 0
  | .pbB1 => .pb 1 1
  | .pbC1 => .pb 1 2
  | .pbD1 => .pb 1 3
  | .pbE1 => .pb 1 4
  | .arr1 => .arr 1
  | .lbA1 => .lb 1 0
  | .lbB1 => .lb 1 1
  | .psh1 => .psh 1
  | .pel1_0 => .pel 1 0
  | .ptc1_0 => .ptc 1 0
  | .pel1_1 => .pel 1 1
  | .ptc1_1 => .ptc 1 1
  | .pel1_2 => .pel 1 2
  | .ptc1_2 => .ptc 1 2
  | .pel1_3 => .pel 1 3
  | .ptc1_3 => .ptc 1 3
  | .pbA2 => .pb 2 0
  | .pbB2 => .pb 2 1
  | .pbC2 => .pb 2 2
  | .pbD2 => .pb 2 3
  | .pbE2 => .pb 2 4
  | .arr2 => .arr 2
  | .lbA2 => .lb 2 0
  | .lbB2 => .lb 2 1
  | .psh2 => .psh 2
  | .pel2_0 => .pel 2 0
  | .ptc2_0 => .ptc 2 0
  | .pel2_1 => .pel 2 1
  | .ptc2_1 => .ptc 2 1
  | .pel2_2 => .pel 2 2
  | .ptc2_2 => .ptc 2 2
  | .pel2_3 => .pel 2 3
  | .ptc2_3 => .ptc 2 3
  | .ldq0 => .ldq 0
  | .ldq1 => .ldq 1
  | .ldq2 => .ldq 2
  | .ldq3 => .ldq 3
  | .ldq4 => .ldq 4
  | .ldq5 => .ldq 5
  | .ldq6 => .ldq 6
  | .ldq7 => .ldq 7
  | .ldq8 => .ldq 8
  | .ldq9 => .ldq 9
  | .ldq10 => .ldq 10
  | .ldq11 => .ldq 11
  | .ldq12 => .ldq 12
  | .ldq13 => .ldq 13
  | .ldq14 => .ldq 14
  | .ldq15 => .ldq 15
  | .ldq16 => .ldq 16
  | .ldq17 => .ldq 17
  | .ldq18 => .ldq 18
  | .ldq19 => .ldq 19
  | .ldq20 => .ldq 20
  | .ldq21 => .ldq 21
  | .ldq22 => .ldq 22
  | .ldq23 => .ldq 23
  | .ldq24 => .ldq 24
  | .ldq25 => .ldq 25
  | .ldq26 => .ldq 26
  | .ldq27 => .ldq 27
  | .ldq28 => .ldq 28
  | .ldq29 => .ldq 29
  | .ldq30 => .ldq 30
  | .ldq31 => .ldq 31
  | .ldq32 => .ldq 32
  | .ldq33 => .ldq 33
  | .ldq34 => .ldq 34
  | .ldq35 => .ldq 35
  | .ldq36 => .ldq 36
  | .ldq37 => .ldq 37
  | .ldq38 => .ldq 38
  | .ldq39 => .ldq 39
  | .ldq40 => .ldq 40
  | .ldq41 => .ldq 41
  | .ldq42 => .ldq 42
  | .ldq43 => .ldq 43
  | .ldq44 => .ldq 44
  | .ldq45 => .ldq 45
  | .ldq46 => .ldq 46
  | .ldq47 => .ldq 47
  | .ldq48 => .ldq 48
  | .ldq49 => .ldq 49
  | .ldq50 => .ldq 50
  | .ldq51 => .ldq 51
  | .ldq52 => .ldq 52
  | .ldq53 => .ldq 53
  | .ldq54 => .ldq 54
  | .ldq55 => .ldq 55
  | .ldq56 => .ldq 56
  | .ldq57 => .ldq 57
  | .ldq58 => .ldq 58
  | .ldq59 => .ldq 59
  | .ldq60 => .ldq 60
  | .ldq61 => .ldq 61
  | .ldq62 => .ldq 62
  | .ldq63 => .ldq 63
  | .stq0_0 => .stq 0 0
  | .stq0_1 => .stq 0 1
  | .stq0_2 => .stq 0 2
  | .stq0_3 => .stq 0 3
  | .stq1_0 => .stq 1 0
  | .stq1_1 => .stq 1 1
  | .stq1_2 => .stq 1 2
  | .stq1_3 => .stq 1 3
  | .stq2_0 => .stq 2 0
  | .stq2_1 => .stq 2 1
  | .stq2_2 => .stq 2 2
  | .stq2_3 => .stq 2 3
  | .stq3_0 => .stq 3 0
  | .stq3_1 => .stq 3 1
  | .stq3_2 => .stq 3 2
  | .stq3_3 => .stq 3 3
  | .stq4_0 => .stq 4 0
  | .stq4_1 => .stq 4 1
  | .stq4_2 => .stq 4 2
  | .stq4_3 => .stq 4 3
  | .stq5_0 => .stq 5 0
  | .stq5_1 => .stq 5 1
  | .stq5_2 => .stq 5 2
  | .stq5_3 => .stq 5 3
  | .stq6_0 => .stq 6 0
  | .stq6_1 => .stq 6 1
  | .stq6_2 => .stq 6 2
  | .stq6_3 => .stq 6 3
  | .stq7_0 => .stq 7 0
  | .stq7_1 => .stq 7 1
  | .stq7_2 => .stq 7 2
  | .stq7_3 => .stq 7 3
  | .fnc1 => .fnc1
  | .st8 => .st8
  | .st9_0 => .st9 0
  | .st9_1 => .st9 1
  | .bar18 => .bar18

/-- The state of the flat machine a state regroups. -/
def D.old (d : D) : PTX.Kernels.InklingRelDecode.Proof.ProA.D := ⟨d.site.old, d.dt⟩

/-- The successor after event `e` before the loads' faults: the flat machine's, at the flat site,
regrouped; the third request word is recorded whatever it is, and the division of pc 59 decides;
the last barrier enters the exit. -/
def next0 (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .ld 2 =>
    match e.kind with
    | .rd _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match word32 v with
        | some x =>
          if Proof.ProA.div59 L g { d.dt with sk := x } = true then
            some (some ⟨.el 0, { d.dt with sk := x }⟩)
          else none
        | none => some none
      | .error _ => none
    | _ => none
  | .bar18 => some (some ⟨.exit, d.dt⟩)
  | .exit => none
  | s => (PTX.Kernels.InklingRelDecode.Proof.ProA.next L g ⟨s.old, d.dt⟩ e).map
      (Option.map fun d' => ⟨Site.ofOld d'.site, d'.dt⟩)

/-- The load sites: the request words, the block-table words and the query loads. -/
def Site.isLoad : Site → Bool
  | .ld _ | .lb _ _ | .ldq _ => true
  | _ => false

/-- A load whose bytes do not rebuild (`BYTES`): Core sets the thread's fault (rule M1: the
machine dies there, `none`). -/
def kill (d : D) (e : Event) : Bool :=
  d.site.isLoad && match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .error _ => true
      | .ok _ => false
    | _ => false

/-- **The successor after event `e`**: `none` at a load whose bytes do not rebuild, else
`next0`. No successor reads the content of a returned value; another kind of value stops the
machine (`some none`): a word load's value that is not one 32-bit word, a query load's that is
not two bytes. -/
def next (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  if kill d e then none else next0 L g d e

/-- The invariant: the flat machine's (`Proof.ProA.Inv`: the inherited registers are `ArgsOk`'s,
the guard of the site's instruction holds, the
query values of the loads to come are the zero of a masked load, every query value has two
bytes). -/
abbrev Inv (L : Launch) (g : Nat) (d : D) : Prop :=
  PTX.Kernels.InklingRelDecode.Proof.ProA.Inv L g d.old

/-- The first state, from the inherited registers and the base word register's value `w`. -/
def init (P : Inh) (w : Value := b32 P.tm) : D :=
  ⟨.sMax, PTX.Kernels.InklingRelDecode.Proof.ProA.Dat.start P w⟩

/-- The prologue as a code machine from its `setmaxnreg.inc` before the loads' faults
(`next0`), with the inherited registers `P` (their base word `P.tm`). -/
@[reducible] def code0 (L : Launch) (g : Nat) (P : Inh) (w : Value := b32 P.tm) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := init P w
  pc := (·.site.pc)
  facts := fun d => factsAt L g d.site.pc d.dt
  sub := (·.site.sub)
  inv := Inv L g
  next := next0 L g

/-- **The prologue as a code machine** from its `setmaxnreg.inc`, with the inherited registers `P`
and the base word register's value `w` (by default `b32 P.tm`). -/
@[reducible] def code (L : Launch) (g : Nat) (P : Inh) (w : Value := b32 P.tm) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := init P w
  pc := (·.site.pc)
  facts := fun d => factsAt L g d.site.pc d.dt
  sub := (·.site.sub)
  inv := Inv L g
  next := next L g

end
end PTX.Kernels.InklingRelDecode.Proof2.ProA
