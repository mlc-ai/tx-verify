-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Classes
public import Lemmas.Order.ReadLast

@[expose] public section

/-! # Source of a returned value: a protected read over a role table

A proof tool, generic over the kernel. A thread reads a word that one declared writer stored
before a declared hand-off (a barrier, an mbarrier unit hand-off, program order, or Core's
allocation-result hand-off): the read returns the stored bytes (`RoleTable.protected_read`).

The order facts are the kernel's declaration:

* the writer `w` is before the read `r` at every byte (`modelCausality`; from a hand-off it is
  `modelCausality.of_base` of `Frame.Handoff`'s base causality);
* every other write of the read's bytes is classified at its issuing state, which the role
  table gives (`RoleTable.write_class`): it is a thread's write (a store or an atomic with a result,
  `ThreadWrite`), and it is `w` itself, before `w`, or after `r` in base causality. A kernel
  states this once per shape, reading the state's ledger counts against the hand-off's uses.

The classification covers the writes of the threads `S` of the table at followed positions
(`hfa`: every position when the table follows `S`, `RoleTable.protected_read_of_followed`; inside a
following induction it comes from a coarser table whose invariant does not depend on the value
read, since a write after the read is no predecessor of it and `followedAt_of_noBad` does not
reach it); a write issued by another
thread (a role not migrated yet) is classified by the kernel directly (`hout`), which is vacuous
when `S` is every launched thread. Asynchronous writes (copies, tensor loads and stores, a cluster
launch control response) are excluded by the per-shape classification: their issuing event is no
thread write (`memWrites_async_issuer`).

The value of the read then follows from `read_of_last_write` (`Lemmas/Order/ReadLast.lean`). -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

/-- **A thread's write event**: a store, or an atomic that writes a result. -/
def ThreadWrite (e : Event) : Prop :=
  match e.kind with
  | .wr _ _ => True
  | .rmw _ _ (some _) => True
  | _ => False

/-- **An asynchronous write's issuing event names the footprint and is no thread write.** -/
theorem memWrites_async_issuer {X : Execution} {i : EvId} {p : AsyncCopy.Part} {a : Acc}
    {bs : List Byte} (hw : X.MemWrites (.async i p) a bs) :
    ∃ e, X.get i = some e ∧ WriteOf e a ∧ ¬ ThreadWrite e := by
  obtain ⟨e, he, hwo⟩ := memWrites_writeOf hw
  refine ⟨e, he, hwo, ?_⟩
  cases p
  all_goals try exact hw.elim
  case writeCopy =>
    obtain ⟨s, ⟨pc, he'⟩, -⟩ := hw
    change X.get i = some e at he; rw [he] at he'; cases he'; simp [ThreadWrite]
  case writeElem j =>
    obtain ⟨s, ⟨pc, he'⟩, -⟩ := hw
    change X.get i = some e at he; rw [he] at he'; cases he'; simp [ThreadWrite]
  case writeLoad x y k =>
    obtain ⟨o, addr, b, -, ⟨pc, he'⟩, -⟩ := hw
    change X.get i = some e at he; rw [he] at he'; cases he'; simp [ThreadWrite]
  case writeStore x y k =>
    obtain ⟨o, addr, b, -, ⟨pc, he'⟩, -⟩ := hw
    change X.get i = some e at he; rw [he] at he'; cases he'; simp [ThreadWrite]
  case writeCta c =>
    obtain ⟨s, targets, ⟨pc, he'⟩, -⟩ := hw
    change X.get i = some e at he; rw [he] at he'; cases he'; simp [ThreadWrite]

/-- A thread's memory write is fired by a thread write event. -/
theorem memWrites_thread_issuer {X : Execution} {i : EvId} {a : Acc} {bs : List Byte}
    (hw : X.MemWrites (.thread i) a bs) : ∃ e, X.get i = some e ∧ WriteOf e a ∧ ThreadWrite e := by
  rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
  · exact ⟨_, he, by simp only [WriteOf], trivial⟩
  · exact ⟨_, he, by simp only [WriteOf], trivial⟩

variable {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop} {X : Execution}

/-- **The writes of a region classified at their issuing states.** For a region `R` of bytes, a
declared writer `w` and a read `r`: every write that covers a byte of `R` and is fired from a
followed state of a thread of `S` is a thread write, and it is `w`, before `w` or after `r` in
base causality. The per-shape form of the protected read's classification. -/
def RoleTable.WriteClass (T : RoleTable C) (S : Nat → Prop) (X : Execution) (R : Loc → Prop)
    (w r : EvId) : Prop :=
  ∀ g j d e, S g → stateAt C X g j = some (some d) → T.J g d → (C g).inv d → T.Ev g d e →
    X.get (g, j) = some e → ∀ dst, WriteOf e dst → (∃ l, dst.Covers l ∧ R l) →
      ThreadWrite e ∧ ((g, j) = w ∨ baseCausality L X (g, j) w ∨ baseCausality L X r (g, j))

section
variable (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X) (hT : T.ShapeOk S)
include hC hX hT

/-- **An event that is no undefined behaviour, at a followed position of a thread of `S`, is
fired from a state of the table with its shape** (`RoleTable.ev_of_ne_ub` at one position). -/
theorem RoleTable.ev_of_followedAt {g k : Nat} {e : Event} (hg : S g)
    (hfa : FollowedAt C T.J X g k) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    ∃ d, stateAt C X g k = some (some d) ∧ T.J g d ∧ (C g).inv d ∧ T.Ev g d e := by
  rcases fired (C := C) hC hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
  · cases σ with
    | none => exact absurd hσ hfa.1
    | some d =>
      have hJ := hfa.2 d hσ
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := fired_site hC hX he hσ
      exact ⟨d, hσ, hJ, hi, hT.shape g hg d t ins e o hJ hat hi hc hf⟩
  · exact absurd rfl (hub f)

/-- The issuing state of a write of a region by a thread of `S` at a followed position: with its
shape, and classified. -/
theorem RoleTable.write_class_at {R : Loc → Prop} {w r : EvId} (hcls : T.WriteClass S X R w r)
    {ref : AsyncCopy.Ref} {dst : Acc} {bs : List Byte} (hm : X.MemWrites ref dst bs)
    (hg : S ref.issuer.1) (hfa : FollowedAt C T.J X ref.issuer.1 ref.issuer.2) {l : Loc}
    (hc : dst.Covers l) (hl : R l) :
    ∃ e, X.get ref.issuer = some e ∧ ThreadWrite e ∧
      (ref.issuer = w ∨ baseCausality L X ref.issuer w ∨ baseCausality L X r ref.issuer) := by
  obtain ⟨e, he, hwo⟩ := memWrites_writeOf hm
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, k⟩ := e
    rintro f rfl
    simp only [WriteOf] at hwo
  obtain ⟨d, hσ, hJ, hi, hev⟩ := RoleTable.ev_of_followedAt hC hX hT hg hfa he hub
  exact ⟨e, he, hcls _ _ d e hg hσ hJ hi hev he dst hwo ⟨l, hc, hl⟩⟩

/-- **No asynchronous write of a classified region is issued at a followed position of a thread
of `S`.** -/
theorem RoleTable.write_class_async {R : Loc → Prop} {w r : EvId}
    (hcls : T.WriteClass S X R w r) {i : EvId} {p : AsyncCopy.Part} {dst : Acc}
    {bs : List Byte} (hm : X.MemWrites (.async i p) dst bs) (hg : S i.1)
    (hfa : FollowedAt C T.J X i.1 i.2) {l : Loc} (hc : dst.Covers l) (hl : R l) : False := by
  obtain ⟨e, he, htw, -⟩ := RoleTable.write_class_at hC hX hT hcls hm hg hfa hc hl
  obtain ⟨e', he', -, hntw⟩ := memWrites_async_issuer hm
  simp only [AsyncCopy.Ref.issuer] at he
  rw [he] at he'
  cases he'
  exact hntw htw

/-- **Every thread write of a classified region at a followed position of a thread of `S`** is
the declared writer, before it, or after the read, in base causality. -/
theorem RoleTable.write_class {R : Loc → Prop} {w r : EvId} (hcls : T.WriteClass S X R w r)
    {i : EvId} {dst : Acc} {bs : List Byte} (hm : X.MemWrites (.thread i) dst bs) (hg : S i.1)
    (hfa : FollowedAt C T.J X i.1 i.2) {l : Loc} (hc : dst.Covers l) (hl : R l) :
    i = w ∨ baseCausality L X i w ∨ baseCausality L X r i := by
  obtain ⟨-, -, -, h⟩ := RoleTable.write_class_at hC hX hT hcls hm hg hfa hc hl
  exact h

/-- **A protected read returns its declared writer's bytes.** The read `r` and the store `w` have
the same footprint; `w` is before `r` at every byte (`hv`: the declared hand-off, or Core's
allocation-result order); every write of the read's bytes by a thread of `S` is at a followed
position (`hfa`; all of them when the table follows `S`, `protected_read_of_followed`) and is
classified at its issuing state (`hcls`); every other write is classified by the kernel (`hout`).

Inside a following induction a kernel takes `hfa` from a coarser table (one whose invariant does
not depend on the value read: an earlier stage of `followed_stages`, risk R4 in
`Lemmas/DECISIONS.md`). -/
theorem RoleTable.protected_read {r w : EvId} {a dst : Acc} {bs : List (Option Byte)}
    {written : List Byte} (hr : X.MemReads (.thread r) a bs)
    (hw : X.MemWrites (.thread w) dst written) (hloc : dst.loc = a.loc) (hsize : dst.size = a.size)
    (hlen : written.length = a.size)
    (hv : ∀ k < a.size, modelCausality L X (a.loc.at k) (.thread w) (.thread r))
    (hcls : T.WriteClass S X (fun l => ∃ k < a.size, l = a.loc.at k) w r)
    (hfa : ∀ ref dst' bytes, X.MemWrites ref dst' bytes → S ref.issuer.1 →
      (∃ k < a.size, dst'.Covers (a.loc.at k)) → FollowedAt C T.J X ref.issuer.1 ref.issuer.2)
    (hout : ∀ ref dst' bytes, X.MemWrites ref dst' bytes → ¬ S ref.issuer.1 →
      ∀ k < a.size, dst'.Covers (a.loc.at k) →
        ref = .thread w ∨ modelCausality L X (a.loc.at k) ref (.thread w) ∨
          modelCausality L X (a.loc.at k) (.thread r) ref) :
    bs = written.map some := by
  refine read_of_last_write hX hr hw hloc hsize hlen hv fun k hk ref dst' bytes hm hc => ?_
  by_cases hg : S ref.issuer.1
  · have hf := hfa ref dst' bytes hm hg ⟨k, hk, hc⟩
    rcases ref with i | ⟨i, p⟩
    · rcases RoleTable.write_class hC hX hT hcls hm hg hf hc ⟨k, hk, rfl⟩ with h | h | h
      · exact .inl (by rw [h])
      · exact .inr (.inl (.inl h))
      · exact .inr (.inr (.inl h))
    · exact (RoleTable.write_class_async hC hX hT hcls hm hg hf hc ⟨k, hk, rfl⟩).elim
  · exact hout ref dst' bytes hm hg k hk hc

/-- **A protected read returns its declared writer's bytes** when the table follows the threads
`S` at every position. -/
theorem RoleTable.protected_read_of_followed (hF : T.Followed X S) {r w : EvId} {a dst : Acc}
    {bs : List (Option Byte)} {written : List Byte} (hr : X.MemReads (.thread r) a bs)
    (hw : X.MemWrites (.thread w) dst written) (hloc : dst.loc = a.loc) (hsize : dst.size = a.size)
    (hlen : written.length = a.size)
    (hv : ∀ k < a.size, modelCausality L X (a.loc.at k) (.thread w) (.thread r))
    (hcls : T.WriteClass S X (fun l => ∃ k < a.size, l = a.loc.at k) w r)
    (hout : ∀ ref dst' bytes, X.MemWrites ref dst' bytes → ¬ S ref.issuer.1 →
      ∀ k < a.size, dst'.Covers (a.loc.at k) →
        ref = .thread w ∨ modelCausality L X (a.loc.at k) ref (.thread w) ∨
          modelCausality L X (a.loc.at k) (.thread r) ref) :
    bs = written.map some :=
  RoleTable.protected_read hC hX hT hr hw hloc hsize hlen hv hcls
    (fun _ _ _ _ hg _ => hF _ hg _) hout

end

end

end PTX.Frame
