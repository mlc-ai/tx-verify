-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Payload
public import Kernels.InklingRelDecode.Proof.Prologue.QLoadPair
public import Lemmas.Flow.DataOver
public import Lemmas.Flow.DataCarry
public import Lemmas.Flow.DataAdvance

@[expose] public section

/-! # The prologue as a value machine

The control machine (`Control.checkedCode`) with the block-table words the preload loop reads
(`Vals.pay`, from the loads `.lb b h`). The control step is the control machine's; on the data it
records the word of a block-table load. The data facts (`dF`) are the registers the tensor
copies read, named by a `Tag` and held at the sites of a preload block (`tags`): the launch
constants, the row of each loaded page (`pageRows` times the word plus the head's row offset),
and the column of the half tile (the broadcast bit, the head's column offset). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow Control

noncomputable section

/-- The words a value event returned. -/
structure Vals where
  /-- The block-table word of preload block `b`, half `h`. -/
  pay : Fin 3 → Fin 2 → Value := fun _ _ => b32 0
  /-- The half a query load returned (the zero half until the load). -/
  q : Fin 64 → Value := fun _ => .bits 16 0

structure D where
  c : Control.D := {}
  v : Vals := {}

/-- The value the bytes of a load rebuild to. -/
def loadVal (bs : List (Option Byte)) : Value := (rebuild 3 bs).toOption.getD (b32 0)

/-- The words after the control step on `e` from `d`. -/
def record (d : D) (e : Event) : Vals :=
  match d.c.site, e.kind with
  | .lb b h, .rd _ bs =>
    ⟨Function.update d.v.pay b (Function.update (d.v.pay b) h (loadVal bs)), d.v.q⟩
  | .ldq j, .rd _ bs => ⟨d.v.pay, Function.update d.v.q j (loadVal bs)⟩
  | _, _ => d.v

/-- **The successor**: the control successor, with the words. -/
def succ (Q : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  (Control.next Q L g d.c e).map (Option.map fun c => ⟨c, record d e⟩)

/-! ### The data facts -/

/-- A data fact: the strides, the head's row and column offsets, the head's origin, a row and a
column of half `h` of block `b`. -/
inductive Tag where
  | scale | stride | rows | cols | oy | ox
  | row (b : Fin 3) (h : Fin 2)
  | col (b : Fin 3) (h : Fin 2)
  /-- The zero half (register 199), a loaded half, a packed word of a query store. -/
  | zero | qh (k : Fin 64) | qw (i : Fin 8) (k : Fin 4)
  deriving DecidableEq

def Tag.reg : Tag → Nat
  | .scale => 525 | .stride => 529 | .rows => 530 | .cols => 531 | .oy => 494 | .ox => 495
  | .row b h => [684, 704, 726].getD b 0 + 5 * h.val
  | .col b h => [683, 703, 725].getD b 0 + 3 * h.val
  | .zero => 199 | .qh k => Prologue.qDst k | .qw i k => 747 + 5 * i.val + k.val

/-- The row of the box of a page word: the word times the page stride plus the head's rows. -/
def rowVal (Q : Params) (L : Launch) (g : Nat) (pay : Value) : Value :=
  u32 ((Lib.word pay).toNat * Q.pageRows + Q.headRows * (L.ctaidOf (g / L.block)).get .y)

/-- The column of half `h` of a tile: the broadcast bit, the head's column offset, 128 a half. -/
def colVal (Q : Params) (L : Launch) (g : Nat) (bc : Value) (h : Fin 2) : Value :=
  u32 (64 * ((Lib.word bc).toNat % 2) + 128 * h.val + Q.headCols * (L.ctaidOf (g / L.block)).get .y)

/-- The scale constant of the launch (parameter 15), held from the startup to the exit. -/
def scaleVal (L : Launch) : Value := .bits 32 (truncBits 32 ((L.params (param "15")).getD 0))

/-- A query half: what its load returned, or the zero half of a group whose loads are masked. -/
def qv (L : Launch) (g : Nat) (d : D) (k : Fin 64) : Value :=
  if queryOn (g % L.block) (k.val / 16) d.c = true then d.v.q k else .bits 16 0

def Tag.val (Q : Params) (L : Launch) (g : Nat) (d : D) : Tag → Value
  | .scale => scaleVal L
  | .stride => u32 Q.pageRows | .rows => u32 Q.headRows | .cols => u32 Q.headCols
  | .oy => u32 (Q.headRows * (L.ctaidOf (g / L.block)).get .y)
  | .ox => u32 (Q.headCols * (L.ctaidOf (g / L.block)).get .y)
  | .row b h => rowVal Q L g (d.v.pay b h)
  | .col _ h => colVal Q L g d.c.broadcast h
  | .zero => .bits 16 0 | .qh k => qv L g d k
  | .qw i k => joinValue (qv L g d ⟨8 * i.val + 2 * k.val, by omega⟩)
      (qv L g d ⟨8 * i.val + 2 * k.val + 1, by omega⟩)

/-- Position `(b, k)` of a site in the sites of its preload block, in instruction order. -/
def pos : Site → Option (Fin 3 × Nat)
  | .pb b j => some (b, [0, 3, 7, 11, 14].getD j 0)
  | .arr b => some (b, 1)
  | .lb b h => some (b, 2 + 8 * h.val)
  | .psh b => some (b, 4)
  | .pel b j => some (b, [5, 8, 12, 15].getD j 0)
  | .ptc b j => some (b, [6, 9, 13, 16].getD j 0)
  | _ => none

/-- The sites before the preload blocks that keep the stride words. -/
def early : Site → Bool
  | .sMax | .ld _ | .el _ | .init _ | .fnc0 | .bar2 => true
  | _ => false

/-- The facts of the query halves from `lo` below `hi`. -/
def qhs (lo hi : Nat) : List Tag :=
  ((List.finRange 64).filter fun k => lo ≤ k.val ∧ k.val < hi).map .qh

/-- The data facts of a site: from the launch before the first loaded row, then the head's origin
and a block's rows and columns while its copies read them. -/
def oldTags (s : Site) : List Tag :=
  .scale :: match pos s with
  | none => if early s then [.stride, .rows, .cols] else []
  | some (b, k) =>
    (if b = 0 ∧ k ≤ 2 then [.rows, .cols] else [.oy, .ox]) ++ [.stride] ++
    (if 3 ≤ k ∧ k ≤ 9 then [.row b 0] else []) ++ (if 6 ≤ k then [.col b 0] else []) ++
    (if 9 ≤ k then [.col b 1] else []) ++ (if 11 ≤ k then [.row b 1] else [])

/-- The scale fact the Softmax entry takes over. -/
def scaleFact (L : Launch) : Nat × Value := (525, scaleVal L)

/-- The data facts of the query sites: the zero half and the loaded halves, then the packed words
not yet stored and the halves not yet packed. -/
def qTags : Site → List Tag
  | .ldq j => [.zero] ++ qhs 0 j.val
  | .stq i j => ((List.finRange 4).filter (j.val ≤ ·.val)).map (.qw i) ++ qhs (8 * (i.val + 1)) 64
  | _ => []

def tags (s : Site) : List Tag := oldTags s ++ qTags s

/-- **The data facts** of a state. -/
def dF (Q : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  (tags d.c.site).map fun τ => (τ.reg, τ.val Q L g d)

/-- **The prologue as a value machine** (for the warp word `w`, not read). -/
@[reducible] def code (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := {}
  pc := fun d => (checkedCode Q L g w).pc d.c
  facts := fun d => (checkedCode Q L g w).facts d.c ++ dF Q L g d
  sub := fun d => (checkedCode Q L g w).sub d.c
  acc := fun d => (checkedCode Q L g w).acc d.c
  inv := fun d => (checkedCode Q L g w).inv d.c
  next := succ Q L g

/-- **The value machine lies over the control machine.** -/
theorem over (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Code.Over (code Q L g w) (checkedCode Q L g w) D.c (dF Q L g) where
  pc _ := rfl
  sub _ := rfl
  acc _ := rfl
  inv _ := Iff.rfl
  facts _ := rfl
  next := by
    intro d e d' h
    change (Control.next Q L g d.c e).map _ = _ at h
    cases hn : Control.next Q L g d.c e with
    | none => rw [hn] at h; cases h
    | some o =>
      cases o with
      | none => rw [hn] at h; cases h
      | some c =>
        rw [hn] at h
        obtain rfl := Option.some.inj (Option.some.inj h)
        exact hn
  stop := by
    intro d e h
    change (Control.next Q L g d.c e).map _ = _ at h
    cases hn : Control.next Q L g d.c e with
    | none => exact hn
    | some o => rw [hn] at h; cases o <;> cases h

theorem erases (Q : Params) (L : Launch) (g : Nat) (w : Value) :
    Code.Erases (code Q L g w) (checkedCode Q L g w) D.c :=
  (over Q L g w).erases rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
