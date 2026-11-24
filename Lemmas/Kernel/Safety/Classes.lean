-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Table

@[expose] public section

/-! # Classes of `Unsafe` from a role table

A proof skeleton, generic over the kernel: classes of Core's `Unsafe` discharged by the role
table of `Lemmas/Kernel/Safety/Table.lean` (`RoleTable.Ok`, `RoleTable.Followed`) and one
per-shape fact per class. The threads `S` are those the table follows; with `S` every launched
thread the class is closed, otherwise the conclusion covers the events of `S` and the kernel keeps
the rest as a premise.

* **ERR-UNDEFINED-INSTRUCTION** (`HasUb`): `RoleTable.noHasUb`, from `safe` (`ref_safe`) and
  `death` alone.
* **The write frame** (`WriteOf`, `memWrites_writeOf`, `RoleTable.write_frame`): every memory
  write of the execution (`MemWrites`: a thread's store or atomic, the destination of a linear
  copy, a tensor load's tile, a tensor store's global bytes, a cluster launch control response)
  is a footprint its issuing event names (`WriteOf`), and that event is fired from a followed
  state of its thread. So a frame `W g a` stated per shape ("this role writes only these
  locations") holds of every write. `RoleTable.noWriteIn` is the corollary for a region no frame
  covers (the read-only inputs of a kernel's assumption). The frame is the basis of the race and
  lifetime classes, which add the order between a region's writers and readers.
* **The object frame** (`MbarOf`, `usesMbar_mbarOf`, `RoleTable.mbar_frame`): every mbarrier
  use names an object its event names, so a frame of objects per shape holds of every use (the
  basis of the initialization and lifetime classes).
* **The Tensor Memory frame** (`TmemOf`, `tmemAccess_tmemOf`, `RoleTable.tmem_frame`): the same
  for the cells of `Tmem.Pair.Access` (the basis of the Tensor Memory classes).
* **The access frame** (`intent_issuer`, `RoleTable.intent_at`): every access of the execution
  (`Intent`, thread or asynchronous) is made or issued by an event that names its footprint, fired
  from a followed state with that state's shape at the event's position; the race classes read the
  accessors of a region and their items off it (`Lemmas/Kernel/Safety/Handoff.lean`).
* **ERR-UNALLOCATED-ACCESS** (`RoleTable.noUnalloc`): thread accesses inside the allocation
  (`RoleTable.threadTouches_alloc`, from the footprints of the shapes, `AccessOf`), the footprints
  of the asynchronous operations they issue (`AsyncOf`, `asyncFootprint_asyncOf`,
  `RoleTable.asyncTouches_alloc`) and the objects they name (`RoleTable.mbar_alloc`).
* **ERR-TENSOR-FILL-VALUE**, **ERR-TENSOR-LARGE-OOB** for roles without tensor loads:
  `RoleTable.noTensorIssue`, `RoleTable.noTensorUnsafe`, `RoleTable.noTensorBacking`. -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

/-- **The footprints an event writes, itself or through the asynchronous operation it issues**:
a store's or an atomic's footprint, a linear copy's destination (whole or an element), a byte of a
tensor load's tile or of a tensor store's global box, a cluster launch control response in a
target CTA. -/
def WriteOf : Event → Acc → Prop
  | ⟨_, .wr a' _⟩, a => a = a'
  | ⟨_, .rmw a' _ (some _)⟩, a => a = a'
  | ⟨_, .copy s⟩, a => (s.writes = .whole ∧ s.dst = a) ∨ ∃ j : Nat, s.elems[j]? = some a
  | ⟨_, .tensorIssue _ s⟩, a => ∃ x y k, TensorCopy.writeLoc s x y k = some a.loc
  | ⟨_, .tensorStore _ s⟩, a => ∃ x y k, TensorStore.writeLoc s x y k = some a.loc
  | ⟨_, .clcIssue s targets⟩, a =>
    ∃ c ∈ targets, a = { loc := { s.response with cta := c }, size := 16 }
  | _, _ => False

/-- **Every memory write is a footprint its issuing event names.** -/
theorem memWrites_writeOf {X : Execution} {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte}
    (hw : X.MemWrites w a bs) : ∃ e, X.get w.issuer = some e ∧ WriteOf e a := by
  rcases w with i | ⟨i, part⟩
  · rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
    · exact ⟨_, he, by simp only [WriteOf]⟩
    · exact ⟨_, he, by simp only [WriteOf]⟩
  · cases part
    all_goals try exact hw.elim
    case writeCopy =>
      obtain ⟨s, ⟨pc, he⟩, hwh, hd, -⟩ := hw
      exact ⟨_, he, by simp only [WriteOf]; exact .inl ⟨hwh, hd⟩⟩
    case writeElem j =>
      obtain ⟨s, ⟨pc, he⟩, hel, -⟩ := hw
      exact ⟨_, he, by simp only [WriteOf]; exact .inr ⟨j, hel⟩⟩
    case writeLoad x y k =>
      obtain ⟨o, addr, b, -, ⟨pc, he⟩, hloc, -⟩ := hw
      exact ⟨_, he, by simp only [WriteOf]; exact ⟨x, y, k, hloc⟩⟩
    case writeStore x y k =>
      obtain ⟨o, addr, b, -, ⟨pc, he⟩, hloc, -⟩ := hw
      exact ⟨_, he, by simp only [WriteOf]; exact ⟨x, y, k, hloc⟩⟩
    case writeCta c =>
      obtain ⟨s, targets, ⟨pc, he⟩, hc, -, r, -, rfl, -⟩ := hw
      exact ⟨_, he, by simp only [WriteOf]; exact ⟨c, hc, rfl⟩⟩

/-- **The mbarrier objects an event names** (`UsesMbar` read off the event): an arrive's, a
linear copy's completion object, a `cp.async.mbarrier.arrive`'s, a target of a `tcgen05.commit`,
a poll's, an invalidation's, a tensor load's, the object of a target CTA of a cluster launch
control request, an initialization's. -/
def MbarOf : Event → Loc → Prop
  | ⟨_, .arrive m' _ _ _ _⟩, m | ⟨_, .asyncArrive m' _⟩, m | ⟨_, .wait m' _ _ _ _⟩, m
  | ⟨_, .mbInval m'⟩, m | ⟨_, .mbInit m' _⟩, m => m = m'
  | ⟨_, .copy s⟩, m => s.completion = .mbarrier m
  | ⟨_, .tc (.commit s)⟩, m => ∃ rank, TcCommit.target s rank = some m
  | ⟨_, .tensorIssue _ s⟩, m => s.mbar = m
  | ⟨_, .clcIssue s targets⟩, m => ∃ c ∈ targets, m = { s.mbar with cta := c }
  | _, _ => False

/-- **Every use of an mbarrier names it at its event** (`MbarOf`). -/
theorem usesMbar_mbarOf {X : Execution} {i : EvId} {m : Loc} (h : X.UsesMbar i m) :
    ∃ e, X.get i = some e ∧ MbarOf e m := by
  rcases h with ⟨tx, c, r, sc, pc, he⟩ | ⟨s, ⟨pc, he⟩, hc⟩ | ⟨n, pc, he⟩ |
    ⟨s, rank, ⟨pc, he⟩, ht⟩ | ⟨pc, q, ok, acq, sc, he⟩ | ⟨pc, he⟩ | ⟨addr, s, ⟨pc, he⟩, hm⟩ |
    ⟨s, targets, c, ⟨pc, he⟩, hc, hm⟩ | ⟨c, pc, he⟩
  · exact ⟨_, he, by simp only [MbarOf]⟩
  · exact ⟨_, he, by simp only [MbarOf]; exact hc⟩
  · exact ⟨_, he, by simp only [MbarOf]⟩
  · exact ⟨_, he, by simp only [MbarOf]; exact ⟨rank, ht⟩⟩
  · exact ⟨_, he, by simp only [MbarOf]⟩
  · exact ⟨_, he, by simp only [MbarOf]⟩
  · exact ⟨_, he, by simp only [MbarOf]; exact hm⟩
  · exact ⟨_, he, by simp only [MbarOf]; exact ⟨c, hc, hm⟩⟩
  · exact ⟨_, he, by simp only [MbarOf]⟩

/-- The footprint of a thread's memory operation: a read, an `nc` read, a write or an atomic. -/
def AccessOf : Event → Acc → Prop
  | ⟨_, .rd a' _⟩, a | ⟨_, .nc a' _⟩, a | ⟨_, .wr a' _⟩, a | ⟨_, .rmw a' _ _⟩, a => a = a'
  | _, _ => False

/-- **The Tensor Memory cells an event of thread `g` accesses**, itself or through the
asynchronous operation it issues (`Tmem.Pair.Access` read off the event): an MMA's written,
accumulated and A-operand cells, a load's or a store's cells, a copy's cells, a shift's written and
read cells. -/
def TmemOf (L : Launch) (g : Nat) : Event → TcMma.Cell → Prop
  | ⟨_, .tc (.mma d s _ mask)⟩, cell =>
    (∃ row col, TcMma.writeCell s d mask row col = some cell) ∨
      (∃ row col, TcMma.resultCell s d row col = some cell) ∨
      ∃ index b, TcMma.aCell s index = some (cell, b)
  | ⟨_, .tc (.ld a vals shape)⟩, cell | ⟨_, .tc (.st a vals shape)⟩, cell =>
    ∃ j < vals.length, cell = tcDataCell L g shape a j
  | ⟨_, .tc (.cp c)⟩, cell => ∃ cta index lane, cta ∈ c.ctas ∧ index < c.shape.sourceBytes ∧
    lane ∈ c.shape.lanes (index / c.shape.rowBytes) ∧
    cell = TcCopy.cell c.shape c.address cta lane index
  | ⟨_, .tc (.shift s)⟩, cell => s.Writes cell ∨ s.Reads cell
  | _, _ => False

/-- **Every Tensor Memory access is a cell its issuing event names.** -/
theorem tmemAccess_tmemOf {X : Execution} {i : EvId} {cell : TcMma.Cell}
    (h : Tmem.Pair.Access L X i cell) : ∃ e, X.get i = some e ∧ TmemOf L i.1 e cell := by
  rcases h with ((⟨d, s, ac, mask, row, col, ⟨pc, he⟩, hc⟩ | ⟨d, s, mask, row, col, ⟨pc, he⟩, hc⟩ |
      ⟨d, s, ac, mask, index, b, ⟨pc, he⟩, hc⟩) | ⟨j, a, vals, shape, ⟨pc, he⟩, hj, hc⟩ |
      ⟨a, vals, shape, j, ⟨pc, he⟩, hj, hc⟩ | ⟨c, cta, index, lane, ⟨pc, he⟩, h1, h2, h3, hc⟩ |
      ⟨s, ⟨pc, he⟩, hc⟩ | ⟨s, ⟨pc, he⟩, hc⟩)
  · exact ⟨_, he, by simp only [TmemOf]; exact .inl ⟨row, col, hc⟩⟩
  · exact ⟨_, he, by simp only [TmemOf]; exact .inr (.inl ⟨row, col, hc⟩)⟩
  · exact ⟨_, he, by simp only [TmemOf]; exact .inr (.inr ⟨index, b, hc⟩)⟩
  · exact ⟨_, he, by simp only [TmemOf]; exact ⟨j, hj, hc⟩⟩
  · exact ⟨_, he, by simp only [TmemOf]; exact ⟨j, hj, hc⟩⟩
  · exact ⟨_, he, by simp only [TmemOf]; exact ⟨cta, index, lane, h1, h2, h3, hc⟩⟩
  · exact ⟨_, he, by simp only [TmemOf]; exact .inl hc⟩
  · exact ⟨_, he, by simp only [TmemOf]; exact .inr hc⟩

/-- **The footprints of the asynchronous operation an event issues** (`AsyncFootprint` read off
the issue): the bytes an MMA or a `tcgen05.cp` reads from shared memory, a tensor store's or a
tensor load's read and written bytes, a tensor prefetch's source bytes, a CLC response, a linear
copy's source, destination and elements, a bulk prefetch's footprint. -/
def AsyncOf : Event → Acc → Prop
  | ⟨_, .tc (.mma _ s _ _)⟩, a =>
    a.size = 1 ∧ ∃ isB : Bool, ∃ index, s.byteLoc (if isB then .b else .a) index = some a.loc
  | ⟨_, .tc (.cp c)⟩, a =>
    a.size = 1 ∧ ∃ k : Nat, ∃ cta index, c.ctas[k]? = some cta ∧
      TcCopy.byteLoc c.shape c.src cta index = some a.loc
  | ⟨_, .tensorStore _ s⟩, a => a.size = 1 ∧ ∃ x y k,
    TensorStore.readLoc s x y k = some a.loc ∨ TensorStore.writeLoc s x y k = some a.loc
  | ⟨_, .tensorIssue _ s⟩, a => a.size = 1 ∧ ∃ x y k,
    TensorCopy.readLoc s x y k = some a.loc ∨ TensorCopy.writeLoc s x y k = some a.loc
  | ⟨_, .tensorPrefetch _ s⟩, a => a.size = 1 ∧ ∃ x y k,
    TensorTransfer.sourceLoc s.descriptor s.origin s.rows x y k = some a.loc
  | ⟨_, .clcIssue s targets⟩, a =>
    ∃ c ∈ targets, a = { loc := { s.response with cta := c }, size := 16 }
  | ⟨_, .copy s⟩, a => s.src = a ∨ s.dst = a ∨ ∃ j : Nat, s.elems[j]? = some a
  | ⟨_, .bulkPrefetch a'⟩, a => a = a'
  | _, _ => False

/-- **Every footprint of an asynchronous stage is one its issuing event names.** -/
theorem asyncFootprint_asyncOf {X : Execution} {i : EvId} {p : AsyncCopy.Part} {a : Acc}
    (h : X.AsyncFootprint i p a) : ∃ e, X.get i = some e ∧ AsyncOf e a := by
  rcases p with sl | sl | sl | t | _ | _ | _ | r | ⟨isB, index⟩ | _ | _
  · -- read stages
    rcases sl with _ | ⟨x, y, k⟩ | ⟨x, y, k⟩ | c | ⟨x, y, k⟩ | j
    · rcases h with ⟨s, ⟨pc, he⟩, hsrc⟩ | ⟨pc, he⟩
      · exact ⟨_, he, by simp only [AsyncOf]; exact .inl hsrc⟩
      · exact ⟨_, he, by simp only [AsyncOf]⟩
    · obtain ⟨s, addr, ⟨pc, he⟩, hl, hs⟩ := h
      exact ⟨_, he, by simp only [AsyncOf]; exact ⟨hs, x, y, k, .inl hl⟩⟩
    · obtain ⟨s, addr, ⟨pc, he⟩, hl, hs⟩ := h
      exact ⟨_, he, by simp only [AsyncOf]; exact ⟨hs, x, y, k, .inl hl⟩⟩
    · exact h.elim
    · obtain ⟨s, addr, ⟨pc, he⟩, hl, hs⟩ := h
      exact ⟨_, he, by simp only [AsyncOf]; exact ⟨hs, x, y, k, hl⟩⟩
    · exact h.elim
  · -- write stages
    rcases sl with _ | ⟨x, y, k⟩ | ⟨x, y, k⟩ | c | ⟨x, y, k⟩ | j
    · obtain ⟨s, ⟨pc, he⟩, -, hd⟩ := h
      exact ⟨_, he, by simp only [AsyncOf]; exact .inr (.inl hd)⟩
    · obtain ⟨s, addr, ⟨pc, he⟩, hl, hs⟩ := h
      exact ⟨_, he, by simp only [AsyncOf]; exact ⟨hs, x, y, k, .inr hl⟩⟩
    · obtain ⟨s, addr, ⟨pc, he⟩, hl, hs⟩ := h
      exact ⟨_, he, by simp only [AsyncOf]; exact ⟨hs, x, y, k, .inr hl⟩⟩
    · obtain ⟨s, targets, ⟨pc, he⟩, hc, rfl⟩ := h
      exact ⟨_, he, by simp only [AsyncOf]; exact ⟨c, hc, rfl⟩⟩
    · exact h.elim
    · obtain ⟨s, ⟨pc, he⟩, hj⟩ := h
      exact ⟨_, he, by simp only [AsyncOf]; exact .inr (.inr ⟨j, hj⟩)⟩
  · -- old-value reads
    rcases sl with _ | ⟨x, y, k⟩ | ⟨x, y, k⟩ | c | ⟨x, y, k⟩ | j
    · exact h.elim
    · exact h.elim
    · obtain ⟨s, addr, ⟨pc, he⟩, -, hl, hs⟩ := h
      exact ⟨_, he, by simp only [AsyncOf]; exact ⟨hs, x, y, k, .inr hl⟩⟩
    · exact h.elim
    · exact h.elim
    · obtain ⟨s, r, ⟨pc, he⟩, -, hj⟩ := h
      exact ⟨_, he, by simp only [AsyncOf]; exact .inr (.inr ⟨j, hj⟩)⟩
  · exact h.elim
  · exact h.elim
  · exact h.elim
  · exact h.elim
  · exact h.elim
  · obtain ⟨hs, ⟨d, s, ac, mask, ⟨pc, he⟩, hl⟩ | ⟨c, k, cta, ⟨pc, he⟩, -, hk, -, hl⟩⟩ := h
    · exact ⟨_, he, by simp only [AsyncOf]; exact ⟨hs, isB, index, hl⟩⟩
    · exact ⟨_, he, by simp only [AsyncOf]; exact ⟨hs, k, cta, _, hk, hl⟩⟩
  · exact h.elim
  · exact h.elim

/-- **The access an event makes or issues** (`Intent` read off the issuing event): a thread
access is the footprint of its event (`AccessOf`), an asynchronous stage one of the footprints of
the operation its event issues (`AsyncOf`). -/
theorem intent_issuer {X : Execution} {ref : AsyncCopy.Ref} {a : Acc} {w : Bool}
    (h : X.Intent ref a w) : ∃ e, X.get ref.issuer = some e ∧ (AccessOf e a ∨ AsyncOf e a) := by
  rcases ref with i | ⟨i, p⟩
  · rcases h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
    · exact ⟨_, he, .inl (by simp only [AccessOf])⟩
    · exact ⟨_, he, .inl (by simp only [AccessOf])⟩
    · exact ⟨_, he, .inl (by simp only [AccessOf])⟩
  · obtain ⟨e, he, ha⟩ := asyncFootprint_asyncOf h.2
    exact ⟨e, he, .inr ha⟩

variable {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop} {X : Execution}

/-- **ERR-UNDEFINED-INSTRUCTION**: no event is undefined behaviour when the table follows every
launched thread. -/
theorem RoleTable.noHasUb (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X) (hT : T.Ok S) (hF : T.Followed X S)
    (hall : ∀ g < L.threads, S g) : ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  exact RoleTable.noUb hC hX hT hF (hall g (lt_of_get hX he)) he f rfl

variable (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X) (hT : T.ShapeOk S)
  (hF : T.Followed X S)
include hC hX hT hF

/-- **A per-shape relation holds of every event of a thread of `S` it relates** when the relation
holds of no undefined behaviour: the form of every frame below (the shape obligation alone). -/
theorem RoleTable.forall_rel {α : Type} {R : Nat → Event → α → Prop} {Q : Nat → α → Prop}
    (hR : ∀ g e x, R g e x → ∀ f, e.kind ≠ .ub f)
    (hQ : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ x, R g e x → Q g x)
    {g k : Nat} {e : Event} {x : α} (hg : S g) (he : X.get (g, k) = some e) (hx : R g e x) :
    Q g x :=
  RoleTable.forall_kind hC hX hT hF (P := fun e => ∃ x, R g e x) (Q := fun g' e => g' = g →
      ∀ x, R g e x → Q g' x)
    (fun e ⟨x, h⟩ => hR g e x h)
    (fun g' hg' d e hJ hi hev _ hgg x hx => by subst hgg; exact hQ g' hg' d e hJ hi hev x hx)
    hg he ⟨x, hx⟩ rfl x hx

/-- **The issuing state of every access of a thread of `S`**: an access (`Intent`) whose issuing
event is a thread of `S`'s is made or issued by an event fired from a followed state, with the
state's shape, at the event's position (the frame of the race classes: which roles reach a
region, and the item of each access, read off the issuing state's counts). -/
theorem RoleTable.intent_at {ref : AsyncCopy.Ref} {a : Acc} {w : Bool} (h : X.Intent ref a w)
    (hg : S ref.issuer.1) :
    ∃ d e, stateAt C X ref.issuer.1 ref.issuer.2 = some (some d) ∧ T.J _ d ∧
      (C ref.issuer.1).inv d ∧ T.Ev _ d e ∧ X.get ref.issuer = some e ∧
      (AccessOf e a ∨ AsyncOf e a) := by
  obtain ⟨e, he, hae⟩ := intent_issuer h
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, k⟩ := e
    rintro f rfl
    rcases hae with h | h <;> simp only [AccessOf, AsyncOf] at h
  obtain ⟨d, hσ, hJ, hi, hev⟩ := RoleTable.ev_of_ne_ub hC hX hT hF hg he hub
  exact ⟨d, e, hσ, hJ, hi, hev, he, hae⟩

/-- **The write frame**: when every shape's written footprints are in the frame `W` of its
thread, every memory write issued by a thread of `S` is in the frame. -/
theorem RoleTable.write_frame {W : Nat → Acc → Prop}
    (hW : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ a, WriteOf e a → W g a)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs)
    (hg : S w.issuer.1) : W w.issuer.1 a := by
  obtain ⟨e, he, hwo⟩ := memWrites_writeOf hw
  exact RoleTable.forall_rel hC hX hT hF (R := fun _ => WriteOf)
    (fun _ e a h f hf => by obtain ⟨pc, k⟩ := e; simp only at hf; subst hf; exact h) hW hg he hwo

/-- **No write covers a region that no frame covers** (a kernel's read-only inputs, say). -/
theorem RoleTable.noWriteIn {W : Nat → Acc → Prop} {R : Loc → Prop}
    (hW : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ a, WriteOf e a → W g a)
    (hR : ∀ g a l, W g a → a.Covers l → ¬ R l)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} {l : Loc} (hw : X.MemWrites w a bs)
    (hg : S w.issuer.1) (hl : a.Covers l) : ¬ R l :=
  hR _ a l (RoleTable.write_frame hC hX hT hF hW hw hg) hl

/-- **Thread accesses inside the allocation** (the thread part of ERR-UNALLOCATED-ACCESS): when
every shape's access footprint covers only allocated bytes, so does every memory operation of a
thread of `S`. -/
theorem RoleTable.threadTouches_alloc
    (hA : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ a, AccessOf e a →
      ∀ l, a.Covers l → mem0 l ≠ none)
    {i : EvId} {a : Acc} {l : Loc} (hm : X.MemTouches (.thread i) a) (hg : S i.1)
    (hl : a.Covers l) : mem0 l ≠ none := by
  have hacc : ∃ e, X.get i = some e ∧ AccessOf e a := by
    rcases hm with ⟨w, hw⟩ | ⟨j, bs, hj, pc, he⟩
    · rcases hw with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
      · exact ⟨_, he, by simp only [AccessOf]⟩
      · exact ⟨_, he, by simp only [AccessOf]⟩
      · exact ⟨_, he, by simp only [AccessOf]⟩
    · cases hj
      exact ⟨_, he, by simp only [AccessOf]⟩
  obtain ⟨e, he, hae⟩ := hacc
  exact RoleTable.forall_rel hC hX hT hF (R := fun _ => AccessOf)
    (Q := fun _ a => ∀ l, a.Covers l → mem0 l ≠ none)
    (fun _ e a h f hf => by obtain ⟨pc, k⟩ := e; simp only at hf; subst hf; exact h) hA hg he hae
    l hl

/-- **The object frame**: when every shape names only mbarrier objects of the frame `O` of its
thread, every mbarrier use by a thread of `S` is of an object in the frame (the basis of the
initialization and lifetime classes: the frame's objects are the ones the startup initializes and
publishes). -/
theorem RoleTable.mbar_frame {O : Nat → Loc → Prop}
    (hO : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ m, MbarOf e m → O g m)
    {i : EvId} {m : Loc} (hu : X.UsesMbar i m) (hg : S i.1) : O i.1 m := by
  obtain ⟨e, he, hm⟩ := usesMbar_mbarOf hu
  exact RoleTable.forall_rel hC hX hT hF (R := fun _ => MbarOf)
    (fun _ e m h f hf => by obtain ⟨pc, k⟩ := e; simp only at hf; subst hf; exact h) hO hg he hm

/-- **The objects of the threads of `S` are allocated** (the object part of
ERR-UNALLOCATED-ACCESS), when every object of the frame is. -/
theorem RoleTable.mbar_alloc {O : Nat → Loc → Prop}
    (hO : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ m, MbarOf e m → O g m)
    (hA : ∀ g m l, O g m → Acc.Covers { loc := m, size := 8 } l → mem0 l ≠ none)
    {i : EvId} {m : Loc} {l : Loc} (hu : X.UsesMbar i m) (hg : S i.1)
    (hl : Acc.Covers { loc := m, size := 8 } l) : mem0 l ≠ none :=
  hA _ m l (RoleTable.mbar_frame hC hX hT hF hO hu hg) hl

/-- **The footprints of the asynchronous operations issued by threads of `S` are allocated**,
when every shape's `AsyncOf` footprints are. -/
theorem RoleTable.asyncTouches_alloc
    (hB : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ a, AsyncOf e a →
      ∀ l, a.Covers l → mem0 l ≠ none)
    {i : EvId} {p : AsyncCopy.Part} {a : Acc} {l : Loc} (hm : X.MemTouches (.async i p) a)
    (hg : S i.1) (hl : a.Covers l) : mem0 l ≠ none := by
  have hf : X.AsyncFootprint i p a := by
    rcases hm with ⟨w, -, hf⟩ | ⟨j, bs, hj, -⟩
    · exact hf
    · cases hj
  obtain ⟨e, he, hae⟩ := asyncFootprint_asyncOf hf
  exact RoleTable.forall_rel hC hX hT hF (R := fun _ => AsyncOf)
    (Q := fun _ a => ∀ l, a.Covers l → mem0 l ≠ none)
    (fun _ e a h f hf => by obtain ⟨pc, k⟩ := e; simp only at hf; subst hf; exact h) hB hg he hae
    l hl

/-- **ERR-UNALLOCATED-ACCESS**, when the table follows every launched thread: from the shapes'
thread footprints (`AccessOf`), asynchronous footprints (`AsyncOf`) and objects (`MbarOf`, with
the object frame inside the allocation). -/
theorem RoleTable.noUnalloc (hall : ∀ g < L.threads, S g) {O : Nat → Loc → Prop}
    (hA : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ a, AccessOf e a →
      ∀ l, a.Covers l → mem0 l ≠ none)
    (hB : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ a, AsyncOf e a →
      ∀ l, a.Covers l → mem0 l ≠ none)
    (hO : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ m, MbarOf e m → O g m)
    (hOA : ∀ g m l, O g m → Acc.Covers { loc := m, size := 8 } l → mem0 l ≠ none) :
    ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, hm, hl, h0⟩ | ⟨i, m, l, hu, hl, h0⟩)
  · rcases e with i | ⟨i, p⟩
    · have hg : S i.1 := by
        rcases hm with ⟨w, hw⟩ | ⟨j, bs, hj, pc, he⟩
        · rcases hw with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩ <;>
            exact hall _ (lt_of_get hX he)
        · cases hj; exact hall _ (lt_of_get hX he)
      exact RoleTable.threadTouches_alloc hC hX hT hF hA hm hg hl h0
    · have hf : X.AsyncFootprint i p a := by
        rcases hm with ⟨w, -, hf⟩ | ⟨j, bs, hj, -⟩
        · exact hf
        · cases hj
      obtain ⟨e, he, -⟩ := asyncFootprint_asyncOf hf
      exact RoleTable.asyncTouches_alloc hC hX hT hF hB hm (hall _ (lt_of_get hX he)) hl h0
  · obtain ⟨e, he, -⟩ := usesMbar_mbarOf hu
    exact RoleTable.mbar_alloc hC hX hT hF hO hOA hu (hall _ (lt_of_get hX he)) hl h0

/-- **The Tensor Memory frame**: when every shape's cells are in the frame `M` of its thread,
every Tensor Memory access by a thread of `S` is (the basis of the Tensor Memory classes: the
frame's cells are those of the role's allocation, and its hand-offs order the accesses of a
cell). -/
theorem RoleTable.tmem_frame {M : Nat → TcMma.Cell → Prop}
    (hM : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ cell, TmemOf L g e cell →
      M g cell)
    {i : EvId} {cell : TcMma.Cell} (ha : Tmem.Pair.Access L X i cell) (hg : S i.1) :
    M i.1 cell := by
  obtain ⟨e, he, hc⟩ := tmemAccess_tmemOf ha
  exact RoleTable.forall_rel hC hX hT hF (R := TmemOf L)
    (fun _ e c h f hf => by obtain ⟨pc, k⟩ := e; simp only at hf; subst hf; exact h) hM hg he hc

/-- **No tensor load is issued by a thread of `S`** when no shape is one. -/
theorem RoleTable.noTensorIssue
    (hN : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ addr s, e.kind ≠
      .tensorIssue addr s)
    {i : EvId} {addr : Nat} {s : TensorCopy.Spec} (hi : X.TensorIssue i addr s) (hg : S i.1) :
    False := by
  obtain ⟨pc, he⟩ := hi
  exact RoleTable.forall_kind hC hX hT hF (P := fun e => ∃ addr s, e.kind = .tensorIssue addr s)
    (Q := fun _ e => ∀ addr s, e.kind ≠ .tensorIssue addr s)
    (fun _ ⟨_, _, h⟩ f hf => by rw [h] at hf; cases hf)
    (fun g hg d e hJ hi hev _ => hN g hg d e hJ hi hev) hg he ⟨addr, s, rfl⟩ addr s rfl

/-- **ERR-TENSOR-FILL-VALUE** for the tensor loads of the threads of `S`: they issue none. -/
theorem RoleTable.noTensorUnsafe
    (hN : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ addr s, e.kind ≠
      .tensorIssue addr s)
    {i : EvId} {o : TensorCopy.Observation} (ho : X.tensor i = some o) (hg : S i.1) : False := by
  obtain ⟨⟨addr, hi⟩, -⟩ := hX.tensor i o ho
  exact RoleTable.noTensorIssue hC hX hT hF hN hi hg

/-- **ERR-TENSOR-LARGE-OOB** for the tensor loads of the threads of `S`: they issue none. -/
theorem RoleTable.noTensorBacking
    (hN : ∀ g, S g → ∀ d e, T.J g d → (C g).inv d → T.Ev g d e → ∀ addr s, e.kind ≠
      .tensorIssue addr s)
    {i : EvId} {addr : Nat} {s : TensorCopy.Spec} (hi : X.TensorIssue i addr s) (hg : S i.1) :
    ¬ TensorBackingMissing L mem0 s.descriptor s.origin s.rows :=
  (RoleTable.noTensorIssue hC hX hT hF hN hi hg).elim

end

end PTX.Frame
