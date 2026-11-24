-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderSound
public import Kernels.FlashAttn4Fwd.Proof.Bars
public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Kernels.FlashAttn4Fwd.Proof.Interface.Schedule
public import Lemmas.Flow.Polls
public import Lemmas.Flow.RunInv
public import Lemmas.Flow.ElectLead

@[expose] public section

/-! # The loader's counts along its run (statement)

The loader's ledger of counts (`Ledger`, part of its run invariant `Counts`), with exact counts
as closed formulas in the item `i` and the trip `t` of its state. The KV uses of the cluster's
items are numbered in order, `2n` per item (the last K and V tiles, then K and V of each trip;
even uses are K tiles, odd ones V tiles), and continue through the drain's six polls; use `U` is
on slot `U % 6`. The state's ring registers are those of the next K use (`ring`). The loader's
successful polls of KV slot `s`'s empty barrier are the uses polled so far on that slot
(`slotCount`), those of the Q slot `st`'s empty barrier one per item (plus the drain's poll of
slot 1). Along a trace whose elections all returned the thread's lane (`ElectLead`) the leader
CTA's arrivals on its full barriers are the uses whose arrival is done, each expecting the bytes
of both CTAs' copies (32768 for a KV use, 65536 for a Q half), with one more arrival on Q slot 1
at the tail (none on the odd CTA); and every CTA's copies complete on the full barriers of the
even CTA of its pair, two per K tile and Q half and one per V tile. Along a trace whose
elections never returned the lane (`ElectNonLead`) there is no arrival and no copy.

Every tensor copy the loader issues is the copy `j` of a use of an item (`CopyId`): its map
parameter, its four coordinates (head-dimension offset, row, head, batch: the item's
`FastDivmod` split `coordsOf (workOf i)`, the KV block `n - 1 - t`, the CTA's rank), its
destination (the use's slot region plus the box offset, in the CTA's own window), its
completion barrier (the even CTA's full barrier of the use's slot) and its bytes (those the
tensor map's box holds, `copyBytes` of the barrier) are those of `CopyIs`, which also names its
descriptor (the launch's map at the map address), tile mode, `.shared::cluster` barrier address
and CTA group 2; and the copies
issued before it on its barrier number `copies` per earlier round of the barrier plus `j`
(`CopyId.before`), so its position among the barrier's copies names its use. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow Work

noncomputable section

/-- The uses `U < P` on slot `s` of a ring of six. -/
def slotCount (P s : Nat) : Nat := (P + 5 - s) / 6

/-- The first KV use of item `i`. -/
def uB (L : Launch) (i : Nat) : Nat := 2 * n L * i

theorem uB_succ (L : Launch) (i : Nat) : uB L (i + 1) = uB L i + 2 * n L := by
  unfold uB; rw [Nat.mul_succ]

theorem uB_even (L : Launch) (i : Nat) : uB L i % 2 = 0 := by
  unfold uB; rw [Nat.mul_assoc]; exact Nat.mul_mod_right 2 _

/-- The use of the state's ring registers: the item's last K tile, or the trip's K tile. -/
def kvB (L : Launch) (g : Nat) (d : D) : Nat :=
  match d.site with
  | .setMaxReg => 0
  | .drain _ | .drainQ | .elTail | .arriveTail | .exit => uB L (T L g)
  | .wait .k | .elA .k | .arrive .k | .elC .k _ | .copy .k _
  | .wait .v | .elA .v | .arrive .v | .elC .v _ | .copy .v _ => uB L d.i + 2 + 2 * d.t
  | _ => uB L d.i

/-- The items whose Q parity flip is done, plus one. -/
def qB (L : Launch) (g : Nat) (d : D) : Nat :=
  match d.site with
  | .drain _ | .drainQ | .elTail | .arriveTail | .exit => T L g + 1
  | .wait .v0 | .elA .v0 | .arrive .v0 | .elC .v0 _ | .copy .v0 _
  | .wait .k | .elA .k | .arrive .k | .elC .k _ | .copy .k _
  | .wait .v | .elA .v | .arrive .v | .elC .v _ | .copy .v _ => d.i
  | _ => d.i + 1

/-- The KV polls done at state `d`. -/
def kvPolled (L : Launch) (g : Nat) (d : D) : Nat :=
  match d.site with
  | .setMaxReg => 0
  | .drain k => uB L (T L g) + k.val
  | .drainQ | .elTail | .arriveTail | .exit => uB L (T L g) + 6
  | .head | .wait .k0 => uB L d.i
  | .elA .v0 | .arrive .v0 | .elC .v0 _ | .copy .v0 _ => uB L d.i + 2
  | .wait .k => uB L d.i + 2 + 2 * d.t
  | .elA .k | .arrive .k | .elC .k _ | .copy .k _ | .wait .v => uB L d.i + 3 + 2 * d.t
  | .elA .v | .arrive .v | .elC .v _ | .copy .v _ => uB L d.i + 4 + 2 * d.t
  | _ => uB L d.i + 1

/-- The KV arrivals done at state `d` (leader CTA, leading lane). -/
def kvArrived (L : Launch) (g : Nat) (d : D) : Nat :=
  match d.site with
  | .drain _ | .drainQ | .elTail | .arriveTail | .exit => uB L (T L g)
  | .elA .k0 | .arrive .k0 => uB L d.i
  | .elA .v0 | .arrive .v0 => uB L d.i + 1
  | .elA .k | .arrive .k => uB L d.i + 2 + 2 * d.t
  | .elA .v | .arrive .v => uB L d.i + 3 + 2 * d.t
  | _ => kvPolled L g d

/-- The KV uses whose copies are all issued at state `d` (leading lane). -/
def kvDone (L : Launch) (g : Nat) (d : D) : Nat :=
  match d.site with
  | .setMaxReg => 0
  | .drain _ | .drainQ | .elTail | .arriveTail | .exit => uB L (T L g)
  | .head | .wait .k0 | .elA .k0 | .arrive .k0 | .elC .k0 _ | .copy .k0 _ => uB L d.i
  | .wait .k | .elA .k | .arrive .k | .elC .k _ | .copy .k _ => uB L d.i + 2 + 2 * d.t
  | .wait .v | .elA .v | .arrive .v | .elC .v _ | .copy .v _ => uB L d.i + 3 + 2 * d.t
  | _ => uB L d.i + 1

/-- The copies of use `kvDone` issued at state `d`. -/
def kvPart (d : D) : Nat :=
  if d.site = .elC .k0 1 ∨ d.site = .copy .k0 1 ∨ d.site = .elC .k 1 ∨ d.site = .copy .k 1 then 1
  else 0

/-- The copies issued on slot `s` at state `d`: two per K tile (even slots), one per V tile. -/
def kvIssued (L : Launch) (g : Nat) (d : D) (s : Nat) : Nat :=
  slotCount (kvDone L g d) s + (if s % 2 = 0 then slotCount (kvDone L g d) s else 0) +
    if kvDone L g d % 6 = s then kvPart d else 0

/-- The Q polls of stage `st` done at state `d`. -/
def qPolled (L : Launch) (g : Nat) (d : D) (st : Nat) : Nat :=
  match d.site with
  | .setMaxReg => 0
  | .drain _ | .drainQ => T L g
  | .elTail | .arriveTail | .exit => T L g + if st = 1 then 1 else 0
  | .head | .wait .k0 | .elA .k0 | .arrive .k0 | .elC .k0 _ | .copy .k0 _ | .wait .q0 => d.i
  | .elA .q0 | .arrive .q0 | .elC .q0 _ | .copy .q0 _ | .wait .q1 =>
    d.i + if st = 0 then 1 else 0
  | _ => d.i + 1

/-- The Q arrivals of stage `st` done at state `d` (leader CTA, leading lane). -/
def qArrived (L : Launch) (g : Nat) (d : D) (st : Nat) : Nat :=
  match d.site with
  | .setMaxReg => 0
  | .drain _ | .drainQ | .elTail | .arriveTail => T L g
  | .exit => T L g + if st = 1 then 1 else 0
  | .head | .wait .k0 | .elA .k0 | .arrive .k0 | .elC .k0 _ | .copy .k0 _ | .wait .q0
  | .elA .q0 | .arrive .q0 => d.i
  | .elC .q0 _ | .copy .q0 _ | .wait .q1 | .elA .q1 | .arrive .q1 =>
    d.i + if st = 0 then 1 else 0
  | _ => d.i + 1

/-- The Q copies of stage `st` issued at state `d` (leading lane): two per item. -/
def qIssued (L : Launch) (g : Nat) (d : D) (st : Nat) : Nat :=
  match d.site with
  | .setMaxReg => 0
  | .drain _ | .drainQ | .elTail | .arriveTail | .exit => 2 * T L g
  | .head | .wait .k0 | .elA .k0 | .arrive .k0 | .elC .k0 _ | .copy .k0 _ | .wait .q0
  | .elA .q0 | .arrive .q0 | .elC .q0 0 | .copy .q0 0 => 2 * d.i
  | .elC .q0 1 | .copy .q0 1 => 2 * d.i + if st = 0 then 1 else 0
  | .wait .q1 | .elA .q1 | .arrive .q1 | .elC .q1 0 | .copy .q1 0 =>
    2 * d.i + if st = 0 then 2 else 0
  | .elC .q1 1 | .copy .q1 1 => 2 * d.i + if st = 0 then 2 else 1
  | _ => 2 * d.i + 2

/-- The even CTA of the thread's pair, whose full barriers the copies complete on. -/
abbrev evenCta (L : Launch) (g : Nat) : Nat := 2 * (ctaOf L g / 2)

/-- A tensor copy of the loader: copy `j` of use `u` in item `i`, at trip `t` of the item's KV
loop (`t` is the trip of a `k` or `v` use and `0` otherwise). -/
structure CopyId where
  u : UseK
  j : Fin 2
  i : Nat
  t : Nat

namespace CopyId

/-- The KV use number of a KV copy: the item's `2n` uses in order, the last K and V tiles and
then K and V of each trip; `0` for a Q copy. -/
def use (L : Launch) (c : CopyId) : Nat :=
  match c.u with
  | .k0 => uB L c.i
  | .v0 => uB L c.i + 1
  | .k => uB L c.i + 2 + 2 * c.t
  | .v => uB L c.i + 3 + 2 * c.t
  | .q0 | .q1 => 0

/-- The Q stage of a Q copy (`0` for a KV copy). -/
def stage (c : CopyId) : Nat := if c.u = .q1 then 1 else 0

/-- The full barrier the copy completes on: the Q stage's, or the KV slot `use % 6`'s. -/
def bar (L : Launch) (c : CopyId) : FBar :=
  match c.u with
  | .q0 => .qFull 0
  | .q1 => .qFull 1
  | _ => .kvFull ⟨c.use L % 6, Nat.mod_lt _ (by decide)⟩

/-- The KV block (of `128` rows) of a KV copy: the last one for the item's first K and V
tiles, then `n - 2 - t` for trip `t`. -/
def block (L : Launch) (c : CopyId) : Nat :=
  match c.u with
  | .k0 | .v0 => n L - 1
  | _ => n L - 2 - c.t

/-- The name of the tensor-map parameter the copy reads: Q, K or V (`param_4` .. `param_6`). -/
def map (c : CopyId) : String :=
  match c.u with
  | .q0 | .q1 => param "4"
  | .k0 | .k => param "5"
  | .v0 | .v => param "6"

/-- The copy's coordinates in the map's dimension order: head-dimension offset, row, head,
batch. A Q or K copy's `j` selects the 64-column half; a V copy's box is the CTA's half
(`64 * rank`). The row of a Q box is the CTA's half of the stage's 256 rows of the item's
query block, of a K box the CTA's half of the block. -/
def coords (L : Launch) (g : Nat) (c : CopyId) : List Nat :=
  match c.u with
  | .q0 | .q1 =>
    [64 * c.j.val, 512 * (coordsOf L (workOf L g c.i)).2.2 + 128 * rank L g + 256 * c.stage,
      (coordsOf L (workOf L g c.i)).2.1, (coordsOf L (workOf L g c.i)).1]
  | .k0 | .k =>
    [64 * c.j.val, 128 * c.block L + 64 * rank L g, (coordsOf L (workOf L g c.i)).2.1,
      (coordsOf L (workOf L g c.i)).1]
  | .v0 | .v =>
    [64 * rank L g, 128 * c.block L, (coordsOf L (workOf L g c.i)).2.1,
      (coordsOf L (workOf L g c.i)).1]

/-- The destination of the copy's box, as a byte offset from the shared base: the slot's
region plus the box offset (16384 per Q box, 8192 per K box). -/
def dst (L : Launch) (c : CopyId) : Nat :=
  match c.u with
  | .q0 | .q1 => 68608 + 32768 * c.stage + 16384 * c.j.val
  | .k0 | .k => 134144 + 16384 * (c.use L % 6) + 8192 * c.j.val
  | .v0 | .v => 134144 + 16384 * (c.use L % 6)

/-- The round of the copy's barrier it belongs to: the item for a Q stage, `use / 6` for a KV
slot. -/
def round (L : Launch) (c : CopyId) : Nat :=
  match c.u with
  | .q0 | .q1 => c.i
  | _ => c.use L / 6

/-- The copies issued on the copy's barrier before it: the barrier's copies per use for each
earlier round, plus `j`. -/
def before (L : Launch) (c : CopyId) : Nat := (c.bar L).copies * c.round L + c.j.val

end CopyId

/-- The copy `c` is the tensor copy event `(a, sp)` of thread `g`: it reads the map parameter
whose address is `a`, whose rank is 3, from the origin of its four coordinates, into the
thread's own CTA's shared window at its destination, completing on its barrier of the even CTA
of the pair, with the bytes of the map's box. -/
structure CopyIs (L : Launch) (g : Nat) (c : CopyId) (a : Nat) (sp : TensorCopy.Spec) : Prop where
  /-- The map operand is the parameter object `c.map`. -/
  map : ∃ decl, L.paramObjects c.map = some (decl, a)
  /-- The map is of rank 4 (outer rank 3). -/
  outer : sp.outer = 3
  /-- The box origin: the copy's four coordinates. -/
  origin : ∀ k : Fin (sp.outer + 1), sp.origin k = ((c.coords L g).getD k.val 0 : Nat)
  /-- The data destination: the thread's own CTA's window. -/
  dst : sp.sharedBase = ⟨.shared, ctaOf L g, L.sharedBase + c.dst L⟩
  /-- The completion barrier: the even CTA's full barrier. -/
  mbar : sp.mbar = (c.bar L).loc L (evenCta L g)
  /-- The bytes of the copy: the barrier's copy bytes. -/
  bytes : TensorTransfer.bytes sp.descriptor = (c.bar L).copyBytes
  /-- The descriptor: the launch's tensor map at the map address, in tile mode. -/
  desc : L.tensorMaps a = some ⟨sp.outer, sp.descriptor⟩
  /-- A tile-mode copy has no row coordinates. -/
  rows : sp.rows = none
  /-- The barrier is named by a `.shared::cluster` address. -/
  cluster : sp.clusterAddress = true
  /-- A `cta_group::2` copy. -/
  group : sp.group = .two

/-- The loader's ledger of counts at state `d` after the events `es` (the part of `Counts` that
the site step lemmas keep). -/
structure Ledger (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop where
  /-- The ring registers are those of use `kvB` and of the Q parity `qB`. -/
  ring : d.s = kvB L g d % 6 ∧ d.ph = (kvB L g d / 6 + 1) % 2 ∧ d.qp = qB L g d % 2
  /-- Successful polls of each KV slot's empty barrier. -/
  kvPoll : ∀ s : Fin 6,
    okPolls (FBar.loc L (ctaOf L g) (.kvEmpty s)) es = slotCount (kvPolled L g d) s
  /-- Successful polls of each Q slot's empty barrier. -/
  qPoll : ∀ st : Fin 2, okPolls (FBar.loc L (ctaOf L g) (.qEmpty st)) es = qPolled L g d st
  /-- The leader CTA's arrivals on the KV full barriers. -/
  kvArr : ElectLead L g es → ∀ s : Fin 6, arrivals (FBar.loc L (ctaOf L g) (.kvFull s)) es =
    if rank L g = 0 then slotCount (kvArrived L g d) s else 0
  /-- The leader CTA's arrivals on the Q full barriers. -/
  qArr : ElectLead L g es → ∀ st : Fin 2, arrivals (FBar.loc L (ctaOf L g) (.qFull st)) es =
    if rank L g = 0 then qArrived L g d st else 0
  /-- Every arrival expects the bytes of both CTAs' copies of its use. -/
  arrTx : ∀ e ∈ es, ∀ m tx c rel sc, e.kind = .arrive m tx c rel sc →
    (tx = 32768 ∧ ∃ s : Fin 6, m = FBar.loc L (ctaOf L g) (.kvFull s)) ∨
      (tx = 65536 ∧ ∃ st : Fin 2, m = FBar.loc L (ctaOf L g) (.qFull st))
  /-- The copies completing on the even CTA's KV full barriers. -/
  kvIss : ElectLead L g es → ∀ s : Fin 6,
    es.countP (issuesTo (FBar.loc L (evenCta L g) (.kvFull s))) = kvIssued L g d s
  /-- The copies completing on the even CTA's Q full barriers. -/
  qIss : ElectLead L g es → ∀ st : Fin 2,
    es.countP (issuesTo (FBar.loc L (evenCta L g) (.qFull st))) = qIssued L g d st
  /-- Every tensor copy is the copy `j` of a use of an item (`CopyIs`), and the copies before it
  on its barrier, when every election returned the lane, number `CopyId.before`. -/
  copy : ∀ k e, es[k]? = some e → ∀ a sp, e.kind = .tensorIssue a sp →
    ∃ c : CopyId, CopyIs L g c a sp ∧
      (ElectLead L g (es.take k) → (es.take k).countP (issuesTo sp.mbar) = c.before L)
  /-- A lane no election returned neither arrives nor copies. -/
  quiet : ElectNonLead L g es → ∀ m, arrivals m es = 0 ∧ es.countP (issuesTo m) = 0
  /-- At an arrival or a copy (or the tail's arrival) the last election returned the lane. -/
  elect : (∃ u, d.site = .arrive u) ∨ (∃ u j, d.site = .copy u j) ∨ d.site = .arriveTail →
    ¬ ElectNonLead L g es
  /-- The role starts at item 0. -/
  start : d.site = .setMaxReg → d.i = 0 ∧ d.t = 0 ∧ d.s = 0 ∧ d.ph = 1 ∧ d.qp = 1

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Loader
