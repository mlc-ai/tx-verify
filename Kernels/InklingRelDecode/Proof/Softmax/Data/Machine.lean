-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.Alpha
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
public import Lemmas.Flow.DataOver
public import Lemmas.Flow.DataAdvance
public import Kernels.InklingRelDecode.Gen.SoftmaxRescale

@[expose] public section

/-! # The softmax as a value machine (first part: the running maximum)

The control machine (`Control.code`) with the two words of the running maximum that the loop
carries (`Vals`): the running maximum `m` (register 1914, `-inf` from pc 945, updated at pc 949)
and the round's new maximum `mx` (register 1522, from the shuffle at pc 1838). The control step is
the control machine's. The data facts (`dF`) are the registers of the rescale factor: the scale
word (498, a function of the launch), `m` in the loop, and from the shuffle at pc 1838 to the
update the new maximum, the test and the factor. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow Control

noncomputable section

/-- The bias word of a block that has none (a 16-bit zero). -/
def dflt : Value := .bits 16 0

/-- The words the events and the straight code between them returned. -/
structure Vals where
  /-- The running maximum, register 1914. -/
  m : Value := b32 4286578688
  /-- The new maximum of the round, register 1522. -/
  mx : Value := b32 0
  /-- The running maximum the last round started from (`m` before the update of pc 949). -/
  mp : Value := b32 4286578688
  /-- The running sum, register 1915 (zero from pc 944, updated at pc 950). -/
  l : Value := b32 0
  /-- The round's row sum, register 1531 (set at pc 2235 from the shuffle of pc 2234). -/
  ps : Value := b32 0
  /-- The words the accumulator load of pc 2260 returned. -/
  ov : List Value := []
  /-- The 64 words the score load of pc 1265 returned. -/
  s : List Value := []
  /-- The bias words the loads of the phase in progress (preloads, loop) returned, by index. -/
  ld : Nat → Value := fun _ => dflt
  /-- The bias words the packs of registers 1916 to 1947 hold. -/
  cur : Nat → Value := fun _ => dflt

structure D where
  c : Control.D := {}
  v : Vals := {}

/-- The data fact the prologue hands over at the softmax entry. -/
def entryFact (L : Launch) : Nat × Value := (525, scaleVal L)

/-- The sites on a path between the shuffle of pc 1838 and the update of pc 949. -/
def inRound : Site → Bool
  | .shfl6 | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL
  | .shfl11 | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO => true
  | _ => false

/-- The sites after the first code: the loop's loads, its poll and the exit. -/
abbrev loopB (s : Site) : Prop := s = .waitS ∨ s = .nxt 0 ∨ s = .epilogue

/-- The round's row sum after an event: the shuffle of pc 2234 sets it. -/
def psOf (k : Kind) (old : Value) : Value :=
  match k with
  | .shfl _ sent _ _ recv _ => Lib.psWord sent recv
  | _ => old

/-- The words after the control step from `d` on `e` to the site `s`. -/
def record (L : Launch) (d : D) (e : Event) (s : Site) : Vals :=
  match d.c.site, e.kind with
  | .shfl5, .shfl _ sent _ _ recv _ => {d.v with mx := Lib.mxWord d.v.m sent recv}
  | .shfl6, _ | .shfl12, _ | .waitStO, _ =>
    let q := if d.c.site = .shfl6 then psOf e.kind d.v.ps else d.v.ps
    if s = .bar20 then
      {d.v with
        m := Lib.mNext (scaleW L) d.v.m d.v.mx, mp := d.v.m, ps := q,
        l := Lib.lStep d.v.l (Lib.alphaVal (scaleW L) d.v.m d.v.mx 507) q}
    else {d.v with ps := q}
  | .ldO, .tc (.ld _ vals _) => {d.v with ov := vals}
  | .ldS, .tc (.ld _ vals _) => {d.v with s := vals}
  | .bar0, _ =>
    if loopB s then
      {d.v with m := b32 4286578688, l := b32 0, cur := fun _ => dflt, ld := fun _ => dflt}
    else {d.v with ld := fun _ => dflt}
  | .pre j, .rd _ bs =>
    let ld := Function.update d.v.ld j.val (Lib.loadWord bs)
    if loopB s then {d.v with m := b32 4286578688, l := b32 0, cur := ld, ld := fun _ => dflt}
    else {d.v with ld := ld}
  | .nxt j, .rd _ bs => {d.v with ld := Function.update d.v.ld j.val (Lib.loadWord bs)}
  | .bar21, _ | .arrive, _ =>
    if s = .arrive then d.v else {d.v with cur := d.v.ld, ld := fun _ => dflt}
  | _, _ => d.v

/-- **The successor**: the control successor, with the words. -/
def succ (e : Entry) (L : Launch) (g : Nat) (d : D) (ev : Event) : Option (Option D) :=
  (Control.next e L g d.c ev).map (Option.map fun c => ⟨c, record L d ev c.site⟩)

/-! ### The data facts -/

/-- The rescale factor's registers: the new maximum, the test and the factor. -/
def alphaFacts (L : Launch) (v : Vals) : List (Nat × Value) :=
  [(1522, v.mx), (168, Lib.alphaVal (scaleW L) v.m v.mx 168),
   (507, Lib.alphaVal (scaleW L) v.m v.mx 507)]

/-- The registers before the rescale run: the round's words and the loaded accumulator words
(registers 1547 and on). -/
def rsV (L : Launch) (v : Vals) (r : Nat) : Value :=
  if 1547 ≤ r ∧ r < 1611 then v.ov.getD (r - 1547) (b32 0)
  else Lib.alphaVal (scaleW L) v.m v.mx r

/-- **The data facts** of a site, with the words of the state. -/
def dFS (L : Launch) (s : Site) (v : Vals) : List (Nat × Value) :=
  match s with
  | .setMaxReg | .bar0 => [entryFact L]
  | .pre _ => [entryFact L, (498, scaleW L)]
  | .epilogue => []
  | .waitLdO => Gen.rs_facts0 (rsV L v)
  | .bar24 | .stO => Gen.rs_facts2 (rsV L v)
  | s => [(498, scaleW L), (1914, v.m)] ++ if inRound s then alphaFacts L v else []

/-- The words of the rescale chain (the data facts' words) of two states agree. -/
def Vals.main (v w : Vals) : Prop := v.m = w.m ∧ v.mx = w.mx ∧ v.ov = w.ov

theorem dFS_congr (L : Launch) (s : Site) {v w : Vals} (h : v.main w) :
    dFS L s v = dFS L s w := by
  obtain ⟨h1, h2, h3⟩ := h
  have hr : rsV L v = rsV L w := by funext r; simp only [rsV, h1, h2, h3]
  cases s <;> simp only [dFS, alphaFacts, hr, h1, h2]

/-- **The data facts** of a state. -/
def dF (L : Launch) (d : D) : List (Nat × Value) := dFS L d.c.site d.v

/-- **The softmax as a value machine.** -/
@[reducible] def code (e : Entry) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := {}
  pc := fun d => (Control.code e L g).pc d.c
  facts := fun d => (Control.code e L g).facts d.c ++ dF L d
  sub := fun d => (Control.code e L g).sub d.c
  acc := fun d => (Control.code e L g).acc d.c
  inv := fun d => (Control.code e L g).inv d.c
  next := succ e L g

/-- **The value machine lies over the control machine.** -/
theorem over (e : Entry) (L : Launch) (g : Nat) :
    Code.Over (code e L g) (Control.code e L g) D.c (dF L) where
  pc _ := rfl
  sub _ := rfl
  acc _ := rfl
  inv _ := Iff.rfl
  facts _ := rfl
  next := by
    intro d ev d' h
    change (Control.next e L g d.c ev).map _ = _ at h
    cases hn : Control.next e L g d.c ev with
    | none => rw [hn] at h; cases h
    | some o =>
      cases o with
      | none => rw [hn] at h; cases h
      | some c =>
        rw [hn] at h
        obtain rfl := Option.some.inj (Option.some.inj h)
        exact hn
  stop := by
    intro d ev h
    change (Control.next e L g d.c ev).map _ = _ at h
    cases hn : Control.next e L g d.c ev with
    | none => exact hn
    | some o => rw [hn] at h; cases o <;> cases h

theorem erases (e : Entry) (L : Launch) (g : Nat) :
    Code.Erases (code e L g) (Control.code e L g) D.c :=
  (over e L g).erases rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
