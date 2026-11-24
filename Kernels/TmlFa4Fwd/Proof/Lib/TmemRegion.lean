-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Flow.NotCommit
public import Lemmas.Flow.Polls
public import Lemmas.Order.ElectOrdinal
public import Lemmas.Tcgen05.TcDataCell

@[expose] public section

/-! # The Tensor Memory regions of tml-fa4 and the counts that number their uses

Each CTA's Tensor Memory holds, per stage `st < 2`, the scores `S` in columns `128 st … 128 st +
127` (`InS`), the probabilities `P` over the upper half of them (`InP`), and the output accumulator
`O` in columns `256 + 128 st …` (`InO`). A score tile is numbered by the stage's S-full commits of
the MMA lane (`sCommits`), its P-full polls (`pPolls`, `p2Polls` for the second P-full object), the
S-full polls of a softmax lane (`sPolls`) and the P-full arrivals of a softmax or correction lane
(`pArr`). The role exports (`Mma/Export/Tmem`, `Softmax/Export/Tmem`, `Correction/Export/Tmem`)
state their accesses with these, the protocol layer orders them. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Flow TcMma

noncomputable section

/-- The mbarrier object at shared offset `o` of CTA `c`. -/
abbrev bar (L : Launch) (c o : Nat) : Loc := ⟨.shared, c, L.sharedBase + o⟩

/-- Stage `st`'s S-full, P-full, second P-full and O-full objects in CTA `c`. -/
abbrev sFull (L : Launch) (c st : Nat) : Loc := bar L c (80 + 8 * st)
abbrev pFull (L : Launch) (c st : Nat) : Loc := bar L c (96 + 8 * st)
abbrev p2Full (L : Launch) (c st : Nat) : Loc := bar L c (112 + 8 * st)
abbrev oFull (L : Launch) (c st : Nat) : Loc := bar L c (144 + 8 * st)

/-- A Tensor Memory cell of stage `st`'s scores. -/
def InS (st : Nat) (cell : Cell) : Prop :=
  128 * st ≤ cell.column ∧ cell.column < 128 * st + 128

/-- A Tensor Memory cell of stage `st`'s probabilities (the upper half of its scores). -/
def InP (st : Nat) (cell : Cell) : Prop :=
  128 * st + 64 ≤ cell.column ∧ cell.column < 128 * st + 128

/-- A Tensor Memory cell of stage `st`'s output accumulator. -/
def InO (st : Nat) (cell : Cell) : Prop :=
  256 + 128 * st ≤ cell.column ∧ cell.column < 384 + 128 * st

/-- A cell of the probabilities published through the second P-full object. -/
def InPHigh (st : Nat) (cell : Cell) : Prop := 128 * st + 112 ≤ cell.column

/-- Commits of lane `g` to stage `st`'s S-full object before its event `i`. -/
def sCommits (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  ((X.tr g).take i).countP (commitsTo (sFull L (g / L.block) st))

/-- Successful polls of lane `g` of stage `st`'s P-full object before event `i`. -/
def pPolls (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  okPolls (pFull L (g / L.block) st) ((X.tr g).take i)

/-- The same for the second P-full object. -/
def p2Polls (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  okPolls (p2Full L (g / L.block) st) ((X.tr g).take i)

/-- Successful polls of lane `g` of stage `st`'s S-full object before event `i`. -/
def sPolls (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  okPolls (sFull L (g / L.block) st) ((X.tr g).take i)

/-- Arrivals of lane `g` on stage `st`'s P-full object before event `i`. -/
def pArr (L : Launch) (X : Execution) (g st i : Nat) : Nat :=
  arrivals (pFull L (g / L.block) st) ((X.tr g).take i)

/-- Successful polls of lane `g` of the K/V ring's full objects before event `i`: the ring uses the
MMA lane has acquired. -/
def kvPolls (L : Launch) (X : Execution) (g i : Nat) : Nat :=
  okPolls (bar L (g / L.block) 32) ((X.tr g).take i) +
    okPolls (bar L (g / L.block) 40) ((X.tr g).take i) +
    okPolls (bar L (g / L.block) 48) ((X.tr g).take i)

/-- Commits of lane `g` to the K/V ring's empty objects before event `i`: the ring uses the MMA
lane has released. -/
def kvRels (L : Launch) (X : Execution) (g i : Nat) : Nat :=
  ((X.tr g).take i).countP (commitsTo (bar L (g / L.block) 56)) +
    ((X.tr g).take i).countP (commitsTo (bar L (g / L.block) 64)) +
    ((X.tr g).take i).countP (commitsTo (bar L (g / L.block) 72))

/-- A Tensor Memory store event. -/
def isTcSt (e : Event) : Bool := match e.kind with | .tc (.st ..) => true | _ => false

/-- Tensor Memory stores of lane `g` before event `i`. -/
def stN (X : Execution) (g i : Nat) : Nat := ((X.tr g).take i).countP isTcSt

/-- A count does not grow over events of no class. -/
theorem countP_take_eq {X : Execution} {g k w : Nat} {f : Event → Bool} (hkw : k ≤ w)
    (hw : w ≤ (X.tr g).length)
    (h : ∀ i e, k ≤ i → i < w → X.get (g, i) = some e → f e = false) :
    ((X.tr g).take w).countP f = ((X.tr g).take k).countP f := by
  induction w, hkw using Nat.le_induction with
  | base => rfl
  | succ w hkw ih =>
    have hlt : w < (X.tr g).length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.countP_append,
      ih (by omega) fun i e h1 h2 => h i e h1 (by omega)]
    have := h w _ hkw (Nat.lt_succ_self w) (List.getElem?_eq_getElem hlt)
    simp [this]

/-- Event `e` of lane `h` comes after its event `i` and is neither a `tcgen05` event nor
undefined behaviour. -/
def NonTcAfter (X : Execution) (h i e : Nat) : Prop :=
  i < e ∧ ∃ ev, X.get (h, e) = some ev ∧ (∀ tk, ev.kind ≠ .tc tk) ∧ ∀ f, ev.kind ≠ .ub f

/-- The instruction descriptor of the QK MMAs (`0x8200490`). -/
def qkDsc : Descriptor := ⟨.one, .f16 .bf16 .f32, 128, 128, false, false, false, false, false⟩

/-- The instruction descriptor of the PV MMAs (`0x8210490`): B is transposed. -/
def pvDsc : Descriptor := ⟨.one, .f16 .bf16 .f32, 128, 128, false, false, false, true, false⟩

/-- A K-major and an MN-major shared descriptor of a 128-byte-swizzled tile. -/
def kDesc (a : Nat) : TcShared.Descriptor := ⟨a, 16, 1024, 0, false, false, .b128⟩
def mnDesc (a : Nat) : TcShared.Descriptor := ⟨a, 16384, 1024, 0, false, false, .b128⟩

/-- The descriptor of step `j` of the Q stage `st`, of the K slot `n` and of the V slot `n`. -/
def qkA (L : Launch) (st : Nat) (j : Fin 8) : TcShared.Descriptor :=
  kDesc (L.sharedBase + 3072 + 32768 * st + 16384 * (j.val / 4) + 32 * (j.val % 4))
def qkB (L : Launch) (n : Nat) (j : Fin 8) : TcShared.Descriptor :=
  kDesc (L.sharedBase + 68608 + 32768 * n + 16384 * (j.val / 4) + 32 * (j.val % 4))
def pvB (L : Launch) (n : Nat) (j : Fin 8) : TcShared.Descriptor :=
  mnDesc (L.sharedBase + 68608 + 32768 * n + 2048 * j.val)

/-- **The QK MMA `j` of score tile `u` of stage `st`** at event `k` of lane `g`: it writes stage
`st`'s scores, reads A and B from shared memory, accumulates except at `j = 0`, and follows the
`u`-th S-full commit and the P-full polls of the tiles before `u`. -/
structure Qk (L : Launch) (X : Execution) (g k st u : Nat) (j : Fin 8) : Prop where
  issue : ∃ pc da db, X.get (g, k) = some ⟨pc, .tc (.mma (128 * st)
    ⟨qkDsc, da, db, g / L.block, g / L.block, none, {}⟩ (j.val != 0) [0, 0, 0, 0])⟩
  /-- The operands: the Q stage, and the K slot of ring use `2 u`. -/
  descs : ∀ {d s acc mask}, X.MmaIssue (g, k) d s acc mask →
    s.a = qkA L st j ∧ s.b = qkB L (2 * u % 3) j
  com : sCommits L X g st k = u
  p : pPolls L X g st k = u
  p2 : p2Polls L X g st k = u
  /-- The K slot of ring use `2 u` is acquired and not released. -/
  kv : kvPolls L X g k = 2 * u + 1
  rel : kvRels L X g k ≤ 2 * u
  /-- The Q stage is acquired and not released. -/
  q : okPolls (bar L (g / L.block) (8 * st)) ((X.tr g).take k) = 1
  qrel : ((X.tr g).take k).countP (commitsTo (bar L (g / L.block) (16 + 8 * st))) = 0
  el : elections X g k + 1 = 8 * u + (if st = 0 then (if u = 0 then 2 else 0) else 4)

/-- **The PV MMA `j` of tile `u` of stage `st`** at event `k` of lane `g`: it reads A from stage
`st`'s probabilities, accumulates into the stage's output accumulator except at `u = j = 0`, and
follows the S-full commit of tile `u`, the P-full poll of tile `u` and, from `j = 6`, the second
P-full poll of tile `u`. -/
structure Pv (L : Launch) (X : Execution) (g k st u : Nat) (j : Fin 8) : Prop where
  issue : ∃ pc db, X.get (g, k) = some ⟨pc, .tc (.mma (256 + 128 * st)
    ⟨pvDsc, db, db, g / L.block, g / L.block, some (128 * st + 64 + 8 * j.val), {}⟩
    (j.val != 0 || u != 0) [0, 0, 0, 0])⟩
  /-- The B operand: the V slot of ring use `2 u + 1`. -/
  descs : ∀ {d s acc mask}, X.MmaIssue (g, k) d s acc mask → s.b = pvB L ((2 * u + 1) % 3) j
  com : sCommits L X g st k = u + 1
  p : pPolls L X g st k = u + 1
  p2 : p2Polls L X g st k = u + (if 5 < j.val then 1 else 0)
  /-- The V slot of ring use `2 u + 1` is acquired and not released. -/
  kv : 2 * u + 2 ≤ kvPolls L X g k ∧ kvPolls L X g k ≤ 2 * u + 2 + st
  rel : kvRels L X g k ≤ 2 * u + 1
  /-- The stage's final O commit is later. -/
  oc : ((X.tr g).take k).countP (commitsTo (oFull L (g / L.block) st)) = 0
  el : st = 1 → elections X g k = 8 * u + 9

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
