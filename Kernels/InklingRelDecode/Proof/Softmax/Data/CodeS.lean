-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Derived
public import Lemmas.Flow.DataConst
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Words
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Seq
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpKinds
public import Kernels.InklingRelDecode.Proof.Softmax.Data.PkKinds
import Kernels.InklingRelDecode.Proof.Lib.Havoc
import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Kinds
import Kernels.InklingRelDecode.Proof.Softmax.Data.RoundNum
import Kernels.InklingRelDecode.Proof.Softmax.Data.NumExp

@[expose] public section

/-! # The softmax value machine with the launch's constants

The entry's constants (`startF`): the words past the first token (register 482, the prologue's
`r21`), their quotient by 128 (register 484, `r23`), the blocks past the bias (483, `r22`) and the
bias default (199), at every state. The constants the setup
code derives (`derF`, `Data/Derived`) are added from the state that follows them: the preloads
have `keysB`, the loop `keysC`. The pairs of scores (`pF`) are the facts of the wait of the score
load. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The register that holds the words past the first token. -/
abbrev pastReg : Nat := 482

/-- The signed quotient of the words past the first token by 128 (as the prologue computes it). -/
def pastDiv (p : BitVec 64) : BitVec 64 :=
  Arith32.shrs (Arith32.add32 p (Arith32.shru (Arith32.shrs p 31) 25)) 7

/-- The blocks that hold no bias (as the prologue computes it, register 483 = `r22`). -/
def pastBlocks (p : BitVec 64) : BitVec 64 :=
  let x := Arith32.addi p (-1023)
  Arith32.shru (if Arith32.scmpi .gt .s x 0 then Arith32.r32 x else 0) 7

/-- **The constants of the entry**: registers 482, 484 and 483, and the bias words' default
(register 199, a 16-bit zero, set at pc 386). -/
def startF (e : Entry) : List (Nat × Value) :=
  [(482, e.prior), (484, .bits 32 (pastDiv (Lib.word e.prior))),
   (483, .bits 32 (pastBlocks (Lib.word e.prior))), (199, .bits 16 0)]

/-- The destination registers of the score load (pc 1265). -/
def sRegs : List Nat := (List.range 64).map (876 + ·)

/-- **The pairs of scores**: register `2447 + m` holds the join of words `2m` and `2m + 1`. -/
def spF (s : List Value) : List (Nat × Value) :=
  (List.range 32).map fun m =>
    (2447 + m, joinValue (s.getD (2 * m) (b32 0)) (s.getD (2 * m + 1) (b32 0)))

/-- The facts of the pairs of scores: at the wait of the score load only. -/
def pF (d : D) : List (Nat × Value) := if d.c.site = .waitLd then spF d.v.s else []

/-- The facts of a state but those of the first window's result. -/
def baseF (e : Entry) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  (Control.code e L g).facts d.c ++ dF L d ++ (startF e ++ (derF e L g d.c.site ++ (pF d ++ wF d)))

/-- The running maximum the round started from: the update of pc 949 keeps the old one. -/
def m0 (d : D) : Value := if d.c.site = .bar20 ∨ d.c.site = .tmemSt then d.v.mp else d.v.m

/-- The wait of the score load that a state of the round stands for: the words and the round's
counter that the first window reads (not the words that the events of the round brought). -/
def canon (d : D) : D :=
  ⟨{ site := .waitLd, i := d.c.i }, { m := m0 d, cur := d.v.cur, ld := d.v.ld, s := d.v.s }⟩

/-- The values of the registers the first window reads, from the facts of the wait before it. -/
def w1V (e : Entry) (L : Launch) (g : Nat) (d : D) : Nat → Value :=
  lookupD (baseF e L g ⟨{(canon d).c with site := .waitLd}, (canon d).v⟩)

/-- **The sent word of the first window**: at the shuffle of pc 1838 register 1520 holds the
window's result on the registers of the wait. -/
def w1F (e : Entry) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  if d.c.site = .shfl5 then factsFrom kXin (vFin (w1V e L g d)) else []

/-- The registers of the exponent window that the later code reads: the exponentials, the
selected singles and the row sum. -/
def xKeys : List Nat := runE2.outs

/-- The registers of the pack's words after the first run, and the singles the second reads. -/
def kB20 : List Nat := runK1.outs ++ runK2.live

/-- The registers of the 32 words the probability store writes. -/
def kTm : List Nat := runK1.outs ++ runK2.outs

/-- **The registers the exponent window reads**, from the round's words: the running maximum, the
scale, the test and the maximum used (the rescale run's), the negated scale, and the scores and
predicates the first window left. -/
def xV (e : Entry) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  if r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523 then Lib.alphaVal (scaleW L) (m0 d) d.v.mx r
  else if r = 499 then derV e L g 499 else vFin (w1V e L g d) r

/-- The exponent window's registers after it. -/
def xE (e : Entry) (L : Launch) (g : Nat) (d : D) : Nat → Value := vE3 (xV e L g d)

/-- The facts of the exponent window and the pack at a site: from the shuffle of pc 2234 to the
barrier of pc 999 the exponentials; at the barrier the first pack's words and the singles; at the
store of pc 1009 the 32 words. -/
def xF0 (e : Entry) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  if inRound d.c.site then factsFrom xKeys (xE e L g d)
  else if d.c.site = .bar20 then factsFrom kB20 (vP1 (xE e L g d))
  else if d.c.site = .tmemSt then factsFrom kTm (vP2 (vP1 (xE e L g d))) else []

open Classical in
/-- **The facts of the exponent window and the pack**, when the window's inputs are typed (the
window's software `exp2` blocks are then the segments the assumptions take): none otherwise. -/
def xF (e : Entry) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  if ExpIn (xV e L g d) then xF0 e L g d else []

/-- The sites between the row sum's addition (pc 2235) and the update of the running sum
(pc 950). -/
def psB : Site → Bool
  | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL | .shfl11
  | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO => true
  | _ => false

/-- **The running sum's facts** at a site: the sum (register 1915, zero from pc 944) at every
site of the loop, and the round's row sum (register 1531) from its addition to the update. -/
def lFS (s : Site) (v : Vals) : List (Nat × Value) :=
  match s with
  | .setMaxReg | .bar0 | .pre _ | .epilogue => []
  | s => (1915, v.l) :: if psB s then [(1531, v.ps)] else []

/-- The running sum's facts of a state. -/
def lF (d : D) : List (Nat × Value) := lFS d.c.site d.v

/-- The constants of a state: the entry's, the derived ones of its site, the pairs of scores,
the bias words, the first window's result, the exponent window's and the running sum's. -/
def constF (e : Entry) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  startF e ++ (derF e L g d.c.site ++ (pF d ++ ((wF d ++ w1F e L g d ++ xF e L g d) ++ lF d)))

/-- **The softmax value machine with the constants** at every state. -/
@[reducible] def codeS (e : Entry) (L : Launch) (g : Nat) : Flow.Code kernel Assumptions.all L g :=
  (code e L g).withConst (constF e L g)

/-- A concrete state of a state of the machine with the constants is one of the machine's. -/
theorem atS_code {d : D} {t : TState} (h : (codeS e L g).AtD d t) : (code e L g).AtD d t := by
  obtain ⟨a, b, c, f, r⟩ := h
  exact ⟨a, b, c, f, ((holds_append _ _ _).mp r).1⟩

/-- The constants of a state hold at a state of the machine. -/
theorem atS_const {d : D} {t : TState} (h : (codeS e L g).AtD d t) :
    Holds t.regs (startF e) ∧ Holds t.regs (derF e L g d.c.site) := by
  obtain ⟨-, -, -, -, r⟩ := h
  have h := (holds_append _ _ _).mp ((holds_append _ _ _).mp r).2
  exact ⟨h.1, ((holds_append _ _ _).mp h.2).1⟩

/-- The facts of the constants hold wherever the machine's facts do. -/
theorem atS_holds {d : D} {R : Nat → Option Value} (h : Holds R ((codeS e L g).facts d)) :
    Holds R (startF e) ∧ Holds R (derF e L g d.c.site) ∧ Holds R (pF d) ∧
      Holds R (wF d ++ w1F e L g d ++ xF e L g d) := by
  have h1 := (holds_append _ _ _).mp ((holds_append _ _ _).mp h).2
  have h2 := (holds_append _ _ _).mp h1.2
  have h3 := (holds_append _ _ _).mp h2.2
  exact ⟨h1.1, h2.1, h3.1, ((holds_append _ _ _).mp h3.2).1⟩

/-- The running sum's facts hold wherever the machine's facts do. -/
theorem atS_lF {d : D} {R : Nat → Option Value} (h : Holds R ((codeS e L g).facts d)) :
    Holds R (lF d) := by
  have h1 := (holds_append _ _ _).mp ((holds_append _ _ _).mp h).2
  have h2 := (holds_append _ _ _).mp h1.2
  have h3 := (holds_append _ _ _).mp h2.2
  exact ((holds_append _ _ _).mp h3.2).2

/-- The facts of the bias words hold wherever the machine's facts do. -/
theorem atS_wF {d : D} {R : Nat → Option Value} (h : Holds R ((codeS e L g).facts d)) :
    Holds R (wF d) := by
  obtain ⟨-, -, -, h⟩ := atS_holds h
  exact ((holds_append _ _ _).mp ((holds_append _ _ _).mp h).1).1

/-- ... and at a state of the machine. -/
theorem atS_wFat {d : D} {t : TState} (h : (codeS e L g).AtD d t) : Holds t.regs (wF d) := by
  obtain ⟨-, -, -, -, r⟩ := h
  exact atS_wF r

/-- The facts of the pairs of scores hold wherever the machine's facts do. -/
theorem atS_pF {d : D} {R : Nat → Option Value} (h : Holds R ((codeS e L g).facts d)) :
    Holds R (pF d) := by
  obtain ⟨-, -, h, -⟩ := atS_holds h
  exact h

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
