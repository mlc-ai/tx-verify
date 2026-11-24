-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Classes
public import Core.Tc.TcMmaConflicts

@[expose] public section

/-! # Tensor Memory races from an item order

A proof skeleton, generic over the kernel, for ERR-TMEM-RACE (`TcMma.WritesUnsafe`,
`TcMma.ReadsUnsafe`). As for the shared-memory regions of `Lemmas/Kernel/Safety/Handoff.lean`, the
accesses of the cells are numbered by **items** (a function of the issuing event, in practice a
count of its state's ledger: the round of a ring, the stage of a tile): writes of one item are one
operation or ordered one way or the other, a write of an earlier item is ordered before every
access of a later item, and a read of an earlier item before every write of a later item
(`TmemItemOrder`). Then every two writes of a cell are ordered (`TmemItemOrder.writesSafe`) and
every read of the race check is ordered with every write of its cell
(`TmemItemOrder.readsSafe`); the orders themselves (`WriteBefore`: an observed commit or a
pipelined pair; `ReadBefore`: the reader's completion or a pipelined pair) are the kernel's
hand-offs.

Every write and race read of a cell is issued by a `tcgen05` event (`tmemWrite_event`,
`raceRead_event`), so for a thread of a role table it is fired from a followed state with that
state's shape (`RoleTable.tmemWrite_at`, `RoleTable.raceRead_at`): the item is read off that
state. -/

namespace PTX.Frame

open PTX PTX.Flow PTX.TcMma

noncomputable section

variable {L : Launch} {X : Execution}

/-- **The item order of Tensor Memory accesses.** -/
structure TmemItemOrder (L : Launch) (X : Execution) (item : EvId → Nat) : Prop where
  /-- Two writes of one item of a cell are one operation or ordered. -/
  wsame : ∀ x y cell, TmemWrite L X x cell → TmemWrite L X y cell → item x = item y →
    x = y ∨ WriteBefore L X x y ∨ WriteBefore L X y x
  /-- A write of an earlier item is ordered before a write of a later item of the cell. -/
  wlater : ∀ x y cell, TmemWrite L X x cell → TmemWrite L X y cell → item x < item y →
    WriteBefore L X x y
  /-- A read and a write of one item of a cell are one operation or ordered. -/
  rsame : ∀ k r w cell, RaceRead X k r cell → TmemWrite L X w cell → item r = item w →
    r = w ∨ WriteBefore L X w r ∨ ReadBefore L X k r w
  /-- A write of an earlier item is ordered before a read of a later item of the cell. -/
  rafter : ∀ k r w cell, RaceRead X k r cell → TmemWrite L X w cell → item w < item r →
    WriteBefore L X w r
  /-- A read of an earlier item is ordered before a write of a later item of the cell. -/
  rbefore : ∀ k r w cell, RaceRead X k r cell → TmemWrite L X w cell → item r < item w →
    ReadBefore L X k r w

variable {item : EvId → Nat}

/-- **Every two Tensor Memory writes of a cell are ordered.** -/
theorem TmemItemOrder.writesSafe (h : TmemItemOrder L X item) : WritesSafe L X := by
  intro x y cell hx hy
  rcases Nat.lt_trichotomy (item x) (item y) with hlt | heq | hgt
  · exact .inr (.inl (h.wlater x y cell hx hy hlt))
  · exact h.wsame x y cell hx hy heq
  · exact .inr (.inr (h.wlater y x cell hy hx hgt))

/-- **Every race read is ordered with every write of its cell.** -/
theorem TmemItemOrder.readsSafe (h : TmemItemOrder L X item) : ReadsSafe L X := by
  intro k r w cell hr hw
  rcases Nat.lt_trichotomy (item r) (item w) with hlt | heq | hgt
  · exact .inr (.inr (h.rbefore k r w cell hr hw hlt))
  · exact h.rsame k r w cell hr hw heq
  · exact .inr (.inl (h.rafter k r w cell hr hw hgt))

/-- **ERR-TMEM-RACE from an item order.** -/
theorem TmemItemOrder.safe (h : TmemItemOrder L X item) :
    ¬ WritesUnsafe L X ∧ ¬ ReadsUnsafe L X :=
  ⟨fun hu => hu h.writesSafe, fun hu => hu h.readsSafe⟩

/-- A Tensor Memory write is issued by a `tcgen05` event. -/
theorem tmemWrite_event {x : EvId} {cell : Cell} (h : TmemWrite L X x cell) :
    ∃ pc op, X.get x = some ⟨pc, .tc op⟩ := by
  rcases h with ⟨_, _, _, _, _, _, ⟨pc, he⟩, -⟩ | ⟨_, _, _, _, ⟨pc, he⟩, -⟩ |
    ⟨_, _, _, _, ⟨pc, he⟩, -⟩ | ⟨_, ⟨pc, he⟩, -⟩
  all_goals exact ⟨pc, _, he⟩

/-- A read of the race check is issued by a `tcgen05` event. -/
theorem raceRead_event {k : TmemRead} {r : EvId} {cell : Cell} (h : RaceRead X k r cell) :
    ∃ pc op, X.get r = some ⟨pc, .tc op⟩ := by
  cases k
  · exact h.elim
  · obtain ⟨_, _, _, _, _, ⟨pc, he⟩, -⟩ := h; exact ⟨pc, _, he⟩
  · obtain ⟨_, _, _, _, _, _, ⟨pc, he⟩, -⟩ := h; exact ⟨pc, _, he⟩
  · obtain ⟨_, ⟨pc, he⟩, -⟩ := h; exact ⟨pc, _, he⟩

variable {K : Kernel} {A : List Assumption} {mem0 : Mem0} {C : (g : Nat) → Code K A L g}
  {T : RoleTable C} {S : Nat → Prop}

section
variable (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X) (hT : T.ShapeOk S)
  (hF : T.Followed X S)
include hC hX hT hF

/-- A `tcgen05` event of a thread of `S` is fired from a followed state with its shape. -/
theorem RoleTable.tc_at {i : EvId} {pc : Nat} {op : TcKind} (he : X.get i = some ⟨pc, .tc op⟩)
    (hg : S i.1) :
    ∃ d, stateAt C X i.1 i.2 = some (some d) ∧ T.J i.1 d ∧ (C i.1).inv d ∧
      T.Ev i.1 d ⟨pc, .tc op⟩ :=
  RoleTable.ev_of_ne_ub hC hX hT hF hg he (fun _ h => by cases h)

/-- **The issuing state of a Tensor Memory write of a thread of `S`**: followed, with its
shape (the item of the write is read off it). -/
theorem RoleTable.tmemWrite_at {x : EvId} {cell : Cell} (h : TmemWrite L X x cell)
    (hg : S x.1) :
    ∃ d e, stateAt C X x.1 x.2 = some (some d) ∧ T.J x.1 d ∧ (C x.1).inv d ∧ T.Ev x.1 d e ∧
      X.get x = some e := by
  obtain ⟨pc, op, he⟩ := tmemWrite_event h
  obtain ⟨d, hσ, hJ, hi, hev⟩ := RoleTable.tc_at hC hX hT hF he hg
  exact ⟨d, _, hσ, hJ, hi, hev, he⟩

/-- **The issuing state of a race read of a thread of `S`.** -/
theorem RoleTable.raceRead_at {k : TmemRead} {r : EvId} {cell : Cell} (h : RaceRead X k r cell)
    (hg : S r.1) :
    ∃ d e, stateAt C X r.1 r.2 = some (some d) ∧ T.J r.1 d ∧ (C r.1).inv d ∧ T.Ev r.1 d e ∧
      X.get r = some e := by
  obtain ⟨pc, op, he⟩ := raceRead_event h
  obtain ⟨d, hσ, hJ, hi, hev⟩ := RoleTable.tc_at hC hX hT hF he hg
  exact ⟨d, _, hσ, hJ, hi, hev, he⟩

end

end

end PTX.Frame
