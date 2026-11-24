-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorTransfer
public import Mathlib.Data.Fintype.Prod
public import Core.Data.Value
public import Core.Tmem.CtaPair

@[expose] public section

namespace PTX

/-- The global address of byte `slot` of the elements a tensor transfer with descriptor `d`
selects at `origin` (four-row mode: tensor rows `rows`): its element's address when the element
is within the tensor, otherwise none. -/
def TensorTransfer.globalAddress {outer : Nat} (d : TensorDescriptor.Descriptor outer)
    (origin : Fin (outer + 1) → Int) (rows : Option (Fin 4 → Int))
    (slot : TensorTransfer.Slot d) : Option Nat :=
  TensorAddress.lookup (TensorDescriptor.geometry d) (TensorTransfer.coord d origin rows slot)
    slot.2.2.val

/-- The global byte that selected byte `(x, y, k)` is read from, as a one-byte location: none when
the slot is out of range or its element is outside the tensor. A tensor load's source read and
a prefetch's read have this footprint. -/
def TensorTransfer.sourceLoc {outer : Nat} (d : TensorDescriptor.Descriptor outer)
    (origin : Fin (outer + 1) → Int) (rows : Option (Fin 4 → Int)) (x y k : Nat) :
    Option Loc := do
  let slot ← TensorTransfer.slotAt d x y k
  let address ← TensorTransfer.globalAddress d origin rows slot
  some ⟨.global, 0, address⟩

/-- The tensor box of one tensor load or store: the descriptor of its transfer (four-row modes:
the map's with four rows, `Descriptor.fourRows`), the signed origin, the shared base and, in
four-row mode, the tensor row of each box row (EXT-TMA-GATHER4, EXT-TMA-SCATTER4). -/
structure TensorBox where
  /-- Rank minus one (`.1d` .. `.5d`). -/
  outer : Nat
  descriptor : TensorDescriptor.Descriptor outer
  origin : Fin (outer + 1) → Int
  sharedBase : Loc
  rows : Option (Fin 4 → Int) := none

/-- The shared location of a slot of the box: its tile layout (row pitch and swizzle,
THREAD-TENSOR-TILE-SHARED) at the shared base. A load writes it and a store reads it. -/
def TensorBox.sharedLoc (b : TensorBox) (slot : TensorTransfer.Slot b.descriptor) : Loc :=
  { b.sharedBase with
    addr := TensorTile.sharedByte b.descriptor.box b.descriptor.format.bytes b.descriptor.swizzle
      b.sharedBase.addr slot.1.val slot.2.1.val slot.2.2.val }

/-- The global address of a slot's byte: its element's address when the element is within the
tensor, otherwise none (a load then fills the byte, a store skips it). -/
def TensorBox.globalAddress (b : TensorBox) (slot : TensorTransfer.Slot b.descriptor) :
    Option Nat :=
  TensorTransfer.globalAddress b.descriptor b.origin b.rows slot

/-- The bounding box's global start is 16-byte aligned (§5.5.3.1, EXT-TMA-BOX-ALIGN), checked once
when the thread issues a tensor load, store, reduction or prefetch: a box whose start is not aligned
is undefined behaviour (`misaligned`), so no issue event records such a box. The check takes the
descriptor and origin that a `TensorBox` or the elements of a prefetch record. -/
def requireBoxAligned {outer : Nat} (d : TensorDescriptor.Descriptor outer)
    (origin : Fin (outer + 1) → Int) : Exec Unit :=
  unless TensorDescriptor.BoxAligned d origin do throw .misaligned

/-- The box-alignment check succeeds exactly for an aligned box. -/
theorem requireBoxAligned_eq_ok {outer : Nat} (d : TensorDescriptor.Descriptor outer)
    (origin : Fin (outer + 1) → Int) :
    requireBoxAligned d origin = .ok () ↔ TensorDescriptor.BoxAligned d origin := by
  unfold requireBoxAligned
  by_cases h : TensorDescriptor.BoxAligned d origin <;>
    simp [h, pure, throw, throwThe, MonadExceptOf.throw, Except.pure]

/-- The box-alignment check reports `misaligned` exactly for a misaligned box. -/
theorem requireBoxAligned_eq_error {outer : Nat} (d : TensorDescriptor.Descriptor outer)
    (origin : Fin (outer + 1) → Int) :
    requireBoxAligned d origin = .error .misaligned ↔ ¬ TensorDescriptor.BoxAligned d origin := by
  unfold requireBoxAligned
  by_cases h : TensorDescriptor.BoxAligned d origin <;>
    simp [h, pure, throw, throwThe, MonadExceptOf.throw, Except.pure]

namespace TensorCopy
noncomputable section

/-! ## DEP-TENSOR-LOAD-EFFECTS — independent tensor byte effects and completion
Statement: A tensor load writes each selected byte with the byte it read from global memory when
  the element is in bounds, and with the fill of the descriptor when it is out of bounds. Its
  completion notification requires every selected byte to be written, and it signals exactly the
  number of selected bytes to the mbarrier that the instruction names.

Defs: TensorTransfer.globalAddress, TensorTransfer.sourceLoc, TensorBox, TensorBox.sharedLoc,
  TensorBox.globalAddress, requireBoxAligned, requireBoxAligned_eq_ok,
  requireBoxAligned_eq_error, TensorCopy.Spec, TensorCopy.Content, TensorCopy.Effects,
  TensorCopy.source, TensorCopy.CopyOk, TensorCopy.Completion, TensorCopy.Extends,
  TensorCopy.RoutingOk, TensorCopy.Observation, TensorCopy.Observation.Extends,
  TensorCopy.SnapshotExtends

Source:
- §9.7.10.28.1 (asynchronous operations)
- §9.7.10.28.5.3 (tensor copy and mbarrier completion)
- §5.5.3.3 (OOB fill)
- §5.5.3.1: "The address of the bounding Box must also be aligned to 16 bytes."

Direction: reading

Applies: One 1D–5D tiled or 2D `.tile::gather4` global-to-shared tensor load, without data multicast

Premises: An actual issuing instruction supplies a valid descriptor and shared/mbarrier locations.
  Source read values are constrained separately by memory consistency.

Effect: Operation-local effect validity and monotone observations. The data destination and
  completion location are distinct fields: a group-2 copy may signal its peer CTA without writing
  the peer CTA's data. CTA-group routing, allocation, proxy visibility and mbarrier phase
  attachment remain execution checks. Content retains symbolic typed fill bytes until the
  scalar-value adapter interprets them; OOB-NaN is not given a real value. Execution.tensor stores
  these records; TensorOk ties each record to its actual issue. Memory/effect adapters remain
  separate. The alignment of the bounding box (reading EXT-TMA-BOX-ALIGN of §5.5.3.1) is checked
  once for every tensor load, store, reduction and prefetch by `requireBoxAligned`, when the thread
  issues the instruction (THREAD-TENSOR-ISSUE, THREAD-TENSOR-STORE, THREAD-TENSOR-PREFETCH). A
  misaligned box is an undefined-behaviour event, so no issue event records one.
-/
/-- A tensor load: its box, the mbarrier it signals, whether its addresses are cluster addresses,
and its CTA group. -/
structure Spec extends TensorBox where
  mbar : Loc
  clusterAddress : Bool := true
  group : CtaGroup := .one

/-- The destination and the mbarrier of the load are placed as its CTA group requires for the
issuing CTA. -/
def RoutingOk (L : Launch) (issuerCta : Nat) (s : Spec) : Prop :=
  TensorRoute L issuerCta s.clusterAddress s.group s.sharedBase s.mbar

/-- The value written to a destination byte: a byte copied from the source read, or a symbolic fill
of the given mode, format and byte. -/
inductive Content where
  | copied (byte : Byte)
  | filled (mode : TensorDescriptor.Fill) (format : TensorDescriptor.Format) (byte : Nat)

/-- The recorded effects of one tensor load: the source read and the destination write of each slot,
and whether the completion notification has occurred. -/
structure Effects (s : Spec) where
  read : TensorTransfer.Slot s.descriptor → Option Byte := fun _ => none
  write : TensorTransfer.Slot s.descriptor → Option Content := fun _ => none
  notified : Bool := false

/-- The source of a slot: its global address when its element is in bounds, otherwise the fill of
the descriptor. -/
def source (s : Spec) (slot : TensorTransfer.Slot s.descriptor) : TensorTransfer.Source :=
  match s.globalAddress slot with
  | some address => .global address
  | none => .fill s.descriptor.fill s.descriptor.format slot.2.2.val

/-- The effects obey the rules of a tensor load: only in-bounds slots are read, each write copies
its read or carries the fill, and a notification implies that every slot is written. -/
structure CopyOk (s : Spec) (e : Effects s) : Prop where
  reads : ∀ slot byte, e.read slot = some byte → ∃ address, source s slot = .global address
  writes : ∀ slot value, e.write slot = some value →
    match source s slot with
    | .global _ => ∃ byte, e.read slot = some byte ∧ value = .copied byte
    | .fill mode format byte => value = .filled mode format byte
  complete : e.notified = true → ∀ slot, ∃ value, e.write slot = some value

/-- The notification of the copy has occurred, it targets the mbarrier of the copy, and it signals
the number of bytes of the transfer. -/
def Completion (s : Spec) (e : Effects s) (mbar : Loc) (count : Nat) : Prop :=
  e.notified = true ∧ mbar = s.mbar ∧ count = TensorTransfer.bytes s.descriptor

/-- The effects `b` extend the effects `a` of the same copy: nothing recorded in `a` is lost in `b`.
-/
def Extends {s : Spec} (a b : Effects s) : Prop :=
  (∀ slot value, a.read slot = some value → b.read slot = some value) ∧
  (∀ slot value, a.write slot = some value → b.write slot = some value) ∧
  (a.notified = true → b.notified = true)

/-- The spec is frozen with the effects of one actual instruction instance. -/
structure Observation where
  spec : Spec
  effects : Effects spec

/-- The observation `b` extends `a`: the same specification, with extended effects. -/
def Observation.Extends (a b : Observation) : Prop :=
  ∃ h : a.spec = b.spec, TensorCopy.Extends (h ▸ a.effects) b.effects

/-- Every observation of `a` is also in `b` as an extended observation of the same issue. -/
def SnapshotExtends {ι : Type} (a b : ι → Option Observation) : Prop :=
  ∀ i old, a i = some old → ∃ newer, b i = some newer ∧ old.Extends newer

/-! ## CORRECT-TENSOR-SIZE — count the independent effects of one tensor copy
Statement: The effects of a tensor load are counted as one for each recorded read, one for each
  recorded write and one for a completion notification. The count only measures progress and adds
  no permitted or forbidden behavior.

Defs: TensorCopy.Effects.readSlots, TensorCopy.Effects.writeSlots, TensorCopy.Effects.size

Source:
- none (finite progress measure)

Direction: representation

Applies: A snapshot of the independent effects of one tensor load

Premises: Selected slots are the finite byte slots of that operation's descriptor.

Effect: A progress measure; no additional permitted or forbidden memory behavior. Each selected
  byte contributes at most one source read and one destination write; the operation contributes one
  completion notification. OOB fill need not read global memory. This counts recorded effects,
  including typed fill content that has no scalar byte.
-/

def Effects.readSlots {s : Spec} (e : Effects s) : Finset (TensorTransfer.Slot s.descriptor) :=
  Finset.univ.filter fun slot => (e.read slot).isSome

def Effects.writeSlots {s : Spec} (e : Effects s) : Finset (TensorTransfer.Slot s.descriptor) :=
  Finset.univ.filter fun slot => (e.write slot).isSome

def Effects.size {s : Spec} (e : Effects s) : Nat :=
  e.readSlots.card + e.writeSlots.card + if e.notified then 1 else 0

end
end TensorCopy
end PTX
