-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Tracked
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Direct
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProtocolLib
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Direct
public import Kernels.FlashKdaFwd.Proof.Ref.Store.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Contract
public import Kernels.FlashKdaFwd.Proof.Ref.Source.Main

@[expose] public section

/-!
# What an event of the kernel does to memory

Seven fields of `DirectFacts` (`Proof/Top/Wire.lean`) and the premise `TensorSources` are about
the memory operations of an execution: the accesses of thread events and the stages of the
asynchronous operations (tensor loads and tensor stores) that thread events issue. This file
classifies every event of a thread that is not undefined behaviour, once, by a case split over
the seven phases of the thread's run (`Assembly.Stage`); `Direct.lean` reads the fields off the
classification.

**Words.** The *window* of a thread is the first 98304 bytes of the shared memory of its own
thread block (`InWin`): the data part, in front of the eleven mbarrier objects. A *launch input
byte* is a byte of global memory that the launch allocates and that is no byte of the output
array and no byte of the final state (`Input`). A *footprint* is an address range `Acc` with
its size. A tensor copy (a load or a store) is issued by one thread event and consists of
*stages*, one read and one write per byte of its box (`AsyncCopy.Part`); a *reference*
(`AsyncCopy.Ref`) names a thread event or one stage of the operation it issued.

**`MemEv P L mem0 X g k e`**: the event `e` of thread `g` at trace position `k` is

* `quiet`: no access and no tensor copy (barriers, polls, arrivals, fences, matrix events,
  elections, shuffles, group commits and waits, the `ret`);
* `rdWin`, `wrWin`: a read, a write of a footprint in the thread's window;
* `rdIn`: a read of launch input bytes (the 21 loads of the offsets array);
* `wrElem`: a write of global memory at a state of the Store phase (an element store of a
  partial last tile);
* `load`: a tensor load, of the initial state or of a tile, whose every source byte is a
  launch input byte and whose every destination byte is in the window;
* `tile`: a tensor store at a state of the Store phase (a full tile);
* `final`: a tensor store of a thread in the epilogue (the final state).

`memEv` proves it for every event that is not undefined behaviour, from the closed-form events
of the phases: `Startup.event_at`, `Conversion.event_at`, `CarryLoad.event_at`,
`Compute.Proto.ev_at`, `Producer.producer_good`, `Store.store_good`, `Epilogue.event_at`.

**The generic part** (no phase): `footprint_cases` says which event issued a stage with a
footprint and which stage it is; `intent_thread` is the same for a thread access.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Direct
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Footprints and stages, for any execution -/

/-- **Which event issued an asynchronous stage with a footprint**: a tensor load (the stage is
the read or the write of one byte of its box), a tensor store (the read, the write, or the
old-value read of a reduction), or an event that is neither. -/
theorem footprint_cases {i : EvId} {p : AsyncCopy.Part} {a : Acc}
    (h : X.AsyncFootprint i p a) :
    (∃ pc al sp x y z, X.get i = some ⟨pc, .tensorIssue al sp⟩ ∧ a.size = 1 ∧
      ((p = .read (.load x y z) ∧ TensorCopy.readLoc sp x y z = some a.loc) ∨
        (p = .write (.load x y z) ∧ TensorCopy.writeLoc sp x y z = some a.loc))) ∨
    (∃ pc al sp x y z, X.get i = some ⟨pc, .tensorStore al sp⟩ ∧ a.size = 1 ∧
      ((p = .read (.store x y z) ∧ TensorStore.readLoc sp x y z = some a.loc) ∨
        (p = .write (.store x y z) ∧ TensorStore.writeLoc sp x y z = some a.loc) ∨
        (p = .old (.store x y z) ∧ sp.reduce.isSome))) ∨
    ∃ e, X.get i = some e ∧ (∀ al sp, e.kind ≠ .tensorIssue al sp) ∧
      ∀ al sp, e.kind ≠ .tensorStore al sp := by
  rcases p with sl | sl | sl | t | _ | _ | _ | r | ⟨isB, index⟩ | _ | _
  · rcases sl with _ | ⟨x, y, k⟩ | ⟨x, y, k⟩ | c | ⟨x, y, k⟩ | j
    · rcases h with ⟨s, ⟨pc, he⟩, hsrc⟩ | ⟨pc, he⟩
      · exact .inr (.inr ⟨_, he, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩)
      · exact .inr (.inr ⟨_, he, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩)
    · obtain ⟨s, addr, ⟨pc, he⟩, hl, hs⟩ := h
      exact .inl ⟨pc, addr, s, x, y, k, he, hs, .inl ⟨rfl, hl⟩⟩
    · obtain ⟨s, addr, ⟨pc, he⟩, hl, hs⟩ := h
      exact .inr (.inl ⟨pc, addr, s, x, y, k, he, hs, .inl ⟨rfl, hl⟩⟩)
    · exact h.elim
    · obtain ⟨s, addr, ⟨pc, he⟩, hl, hs⟩ := h
      exact .inr (.inr ⟨_, he, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩)
    · exact h.elim
  · rcases sl with _ | ⟨x, y, k⟩ | ⟨x, y, k⟩ | c | ⟨x, y, k⟩ | j
    · obtain ⟨s, ⟨pc, he⟩, -, hd⟩ := h
      exact .inr (.inr ⟨_, he, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩)
    · obtain ⟨s, addr, ⟨pc, he⟩, hl, hs⟩ := h
      exact .inl ⟨pc, addr, s, x, y, k, he, hs, .inr ⟨rfl, hl⟩⟩
    · obtain ⟨s, addr, ⟨pc, he⟩, hl, hs⟩ := h
      exact .inr (.inl ⟨pc, addr, s, x, y, k, he, hs, .inr (.inl ⟨rfl, hl⟩)⟩)
    · obtain ⟨s, targets, ⟨pc, he⟩, hc, rfl⟩ := h
      exact .inr (.inr ⟨_, he, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩)
    · exact h.elim
    · obtain ⟨s, ⟨pc, he⟩, hj⟩ := h
      exact .inr (.inr ⟨_, he, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩)
  · rcases sl with _ | ⟨x, y, k⟩ | ⟨x, y, k⟩ | c | ⟨x, y, k⟩ | j
    · exact h.elim
    · exact h.elim
    · obtain ⟨s, addr, ⟨pc, he⟩, hred, hl, hs⟩ := h
      exact .inr (.inl ⟨pc, addr, s, x, y, k, he, hs, .inr (.inr ⟨rfl, hred⟩)⟩)
    · exact h.elim
    · exact h.elim
    · obtain ⟨s, r, ⟨pc, he⟩, -, hj⟩ := h
      exact .inr (.inr ⟨_, he, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩)
  · exact h.elim
  · exact h.elim
  · exact h.elim
  · exact h.elim
  · exact h.elim
  · obtain ⟨hs, ⟨d, s, ac, mask, ⟨pc, he⟩, hl⟩ | ⟨c, k, cta, ⟨pc, he⟩, -, hk, -, hl⟩⟩ := h
    · exact .inr (.inr ⟨_, he, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩)
    · exact .inr (.inr ⟨_, he, fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩)
  · exact h.elim
  · exact h.elim

/-- **A thread access is the footprint of its event**: a read, a write, or an atomic
read-modify-write. -/
theorem intent_thread {i : EvId} {a : Acc} {w : Bool} (h : X.Intent (.thread i) a w) :
    (∃ pc bs, X.get i = some ⟨pc, .rd a bs⟩ ∧ w = false) ∨
      (∃ pc bs, X.get i = some ⟨pc, .wr a bs⟩ ∧ w = true) ∨
      ∃ pc old new, X.get i = some ⟨pc, .rmw a old new⟩ := by
  rcases h with ⟨bs, ⟨pc, he⟩, hw⟩ | ⟨bs, ⟨pc, he⟩, hw⟩ | ⟨old, new, pc, he⟩
  · exact .inl ⟨pc, bs, he, hw⟩
  · exact .inr (.inl ⟨pc, bs, he, hw⟩)
  · exact .inr (.inr ⟨pc, old, new, he⟩)

/-! ### The classes -/

/-- **The window of thread `g`**: `n` bytes at `l` lie in the data part (the first 98304
bytes) of the shared memory of the thread's own block. -/
def InWin (P : Params) (L : Launch) (g : Nat) (l : Loc) (n : Nat) : Prop :=
  l.space = .shared ∧ l.cta = g / L.block ∧ P.sharedBase ≤ l.addr ∧
    l.addr + n ≤ P.sharedBase + 98304

/-- **A launch input byte**: allocated at launch, no byte of the output array and no byte of
the final state. -/
def Input (P : Params) (mem0 : Mem0) (l : Loc) : Prop :=
  mem0 l ≠ none ∧ ¬ P.OutputByte l ∧ ¬ P.StateByte l

/-- **An event that touches no memory and issues no tensor copy.** -/
def Quiet (e : Event) : Prop :=
  (∀ a, ¬ AccessOf e a) ∧ (∀ a, ¬ AsyncOf e a) ∧ (∀ al sp, e.kind ≠ .tensorIssue al sp) ∧
    ∀ al sp, e.kind ≠ .tensorStore al sp

/-- Close `Quiet e` for an event `e` written out with a kind that has no footprint. -/
macro "direct_quiet" : tactic =>
  `(tactic| exact ⟨fun _ h => h, fun _ h => h, fun _ _ h => (by cases h),
    fun _ _ h => (by cases h)⟩)

/-- **What the event `e` of thread `g` at trace position `k` does to memory**: see the file
header. -/
inductive MemEv (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) (g k : Nat) :
    Event → Prop where
  /-- No access, no tensor copy. -/
  | quiet {e : Event} (h : Quiet e) : MemEv P L mem0 X g k e
  /-- A read in the window. -/
  | rdWin {pc : Nat} {a : Acc} {bs : List (Option Byte)} (h : InWin P L g a.loc a.size) :
      MemEv P L mem0 X g k ⟨pc, .rd a bs⟩
  /-- A read of launch input bytes. -/
  | rdIn {pc : Nat} {a : Acc} {bs : List (Option Byte)} (hs : a.loc.space = .global)
      (h : ∀ l, a.Covers l → Input P mem0 l) : MemEv P L mem0 X g k ⟨pc, .rd a bs⟩
  /-- A write in the window. -/
  | wrWin {pc : Nat} {a : Acc} {bs : List Byte} (h : InWin P L g a.loc a.size) :
      MemEv P L mem0 X g k ⟨pc, .wr a bs⟩
  /-- A write of global memory, at a state of the Store phase. -/
  | wrElem {pc : Nat} {a : Acc} {bs : List Byte} {s : D} (hσ : At (code L) X g k s)
      (hI : Store.Inv P X g k s) (hs : a.loc.space = .global) :
      MemEv P L mem0 X g k ⟨pc, .wr a bs⟩
  /-- A tensor load: of the initial state or of a tile; its source bytes are launch input
  bytes, its destination bytes are in the window. -/
  | load {pc al : Nat} {sp : TensorCopy.Spec}
      (hsh : (∃ j < 16, sp = Startup.stateSpec P L g j) ∨
        ∃ tt < Producer.tilesOf P g, ∃ p < 70, sp = Producer.tileLoad P L g tt p)
      (hrd : ∀ x y z l, TensorCopy.readLoc sp x y z = some l → Input P mem0 l)
      (hwr : ∀ x y z l, TensorCopy.writeLoc sp x y z = some l → InWin P L g l 1) :
      MemEv P L mem0 X g k ⟨pc, .tensorIssue al sp⟩
  /-- A tensor store at a state of the Store phase. -/
  | tile {pc al : Nat} {sp : TensorStore.Spec} {s : D} (hσ : At (code L) X g k s)
      (hI : Store.Inv P X g k s) : MemEv P L mem0 X g k ⟨pc, .tensorStore al sp⟩
  /-- A tensor store of a thread in the epilogue, which it entered at position `j0`. -/
  | final {pc al : Nat} {sp : TensorStore.Spec} {j0 : Nat} (hE : Epilogue.Entered P L X g j0)
      (hj : j0 ≤ k) : MemEv P L mem0 X g k ⟨pc, .tensorStore al sp⟩

/-! ### The classification, by stage -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- The startup phase. -/
theorem startup_mem {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : Startup.InvE P X g k s) : MemEv P L mem0 X g k e := by
  rcases Startup.event_at hpre hX hg he hσ with ⟨pos, hr, -, hev⟩ | h
  · rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Startup.Ev] at hev
    · obtain ⟨inst, ld, rfl⟩ := hev
      exact .quiet (by direct_quiet)
    · obtain ⟨v, ok, rfl⟩ := hev
      exact .quiet (by direct_quiet)
    · subst hev
      exact .quiet (by direct_quiet)
    · subst hev
      exact .quiet (by direct_quiet)
    · subst hev
      exact .quiet (by direct_quiet)
    · obtain ⟨i, hi, bs, hbs, rfl⟩ := hev
      exact .rdIn rfl fun l hc => Startup.offsets_frame hpre hi hc
    · subst hev
      exact .quiet (by direct_quiet)
    · subst hev
      refine .load (.inl ⟨j.val, j.isLt, rfl⟩) (fun x y z l h => ?_) fun x y z l h => ?_
      · obtain ⟨k', hk', rfl⟩ := (Source.stateSource hpre g hg j.val j.isLt).2 x y z l h
        exact Startup.initial_frame hpre hk'
      · obtain ⟨hsp, hc, hlo, hhi⟩ := writeLoc_range h
        have h8 : mapBytes 8 = 4096 := rfl
        have := j.isLt
        exact ⟨hsp, hc, by omega, by omega⟩
    · obtain ⟨ok, rfl⟩ := hev
      exact .quiet (by direct_quiet)
  · exact absurd h hI.inv.not_left

/-- The Conversion phase. -/
theorem conversion_mem {j0 k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : Conversion.Inv P X g j0 k s)
    (hne : ∀ f, e.kind ≠ .ub f) : MemEv P L mem0 X g k e := by
  obtain ⟨pos, hr, -, -, hev⟩ := Conversion.event_at hpre hX hg he hσ hI
  have hwin : ∀ a, AccessOf e a → InWin P L g a.loc a.size := fun a ha => by
    rcases Conversion.touch_conversion hpre hX hg he hσ hI (.inl ha) with
      ⟨el, hel, rfl⟩ | ⟨el, hel, -, rfl⟩
    · obtain ⟨h1, h2, -, -⟩ := Conversion.rdAddr_frame hpre hel
      exact ⟨rfl, (block_div hpre).symm, by simp only; omega, by simp only; omega⟩
    · obtain ⟨h1, h2, -, -⟩ := Conversion.wrAddr_frame hpre hel
      exact ⟨rfl, (block_div hpre).symm, by simp only; omega, by simp only; omega⟩
  cases pos with
  | fence =>
    rw [show e = _ from hev]
    exact .quiet (by direct_quiet)
  | ld j u =>
    obtain ⟨bs, -, rfl⟩ := hev
    exact .rdWin (hwin _ rfl)
  | st j u =>
    rcases hev with ⟨v', -, rfl⟩ | ⟨f, -, rfl⟩
    · exact .wrWin (hwin _ rfl)
    · exact absurd rfl (hne f)
  | bar j =>
    rw [show e = _ from hev]
    exact .quiet (by direct_quiet)

/-- The CarryLoad phase. -/
theorem carryLoad_mem {j0 k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : CarryLoad.Inv P X g j0 k s) : MemEv P L mem0 X g k e := by
  obtain ⟨pos, hr, hev, -⟩ := CarryLoad.event_at hpre hX hg he hσ hI
  cases pos with
  | ld j =>
    obtain ⟨bs, -, rfl⟩ := hev
    obtain ⟨f1, f2, -⟩ := CarryLoad.ldAddr_frame hpre hr.pos.1 j.isLt
    exact .rdWin ⟨rfl, (block_div hpre).symm, by simp only; omega, by simp only; omega⟩
  | fence =>
    rw [show e = _ from hev]
    exact .quiet (by direct_quiet)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
omit hpre hX hg in
/-- The class of the address of each accessing position of a tile: a row of 16 bytes at a
register of the bfloat16 state copy, of the input stage or of the output stage; a gate logit
(2 bytes at `%r1642` plus 36864 or 36880); a decay factor (4 bytes at `%r1708` plus a multiple
of 4 from 49280 to 49760). -/
theorem addr_class : ∀ n < 268, (Compute.Proto.addrOf n).2.2 ≠ 0 →
    ((Compute.Proto.addrOf n).2.1 = 0 ∧ (Compute.Proto.addrOf n).2.2 = 16 ∧
      ((Compute.Proto.addrOf n).1 ∈ Compute.accRegs ∨
        (Compute.Proto.addrOf n).1 ∈ Compute.inRegs ∨
        (Compute.Proto.addrOf n).1 ∈ Compute.outRegs)) ∨
    ((Compute.Proto.addrOf n).1 = 1948 ∧
      ((Compute.Proto.addrOf n).2.1 = 36864 ∨ (Compute.Proto.addrOf n).2.1 = 36880) ∧
      (Compute.Proto.addrOf n).2.2 = 2) ∨
    ((Compute.Proto.addrOf n).1 = 2014 ∧ 49280 ≤ (Compute.Proto.addrOf n).2.1 ∧
      (Compute.Proto.addrOf n).2.1 ≤ 49760 ∧ (Compute.Proto.addrOf n).2.1 % 4 = 0 ∧
      (Compute.Proto.addrOf n).2.2 = 4) := by
  decide +kernel

omit hX hg in
/-- **The footprint of an accessing position of a tile lies in the first 95104 bytes of the
window**: the bfloat16 state copy, the three input stages and the two output stages. -/
theorem acc_frame (hc : tid g < 128) {t n : Nat} (hn : n < 268)
    (ha : (Compute.Proto.addrOf n).2.2 ≠ 0) :
    P.sharedBase ≤ Compute.regVal P g t (Compute.Proto.addrOf n).1 +
        (Compute.Proto.addrOf n).2.1 ∧
      Compute.regVal P g t (Compute.Proto.addrOf n).1 + (Compute.Proto.addrOf n).2.1 +
        (Compute.Proto.addrOf n).2.2 ≤ P.sharedBase + 95104 := by
  have b3 : t % 3 < 3 := Nat.mod_lt _ (by decide)
  have b2 : t % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases addr_class n hn ha with ⟨h0, h16, hr | hr | hr⟩ | ⟨h1, hcc, h2⟩ | ⟨h1, h2, h3, h4, h5⟩
  · have := Compute.acc_addr hpre hc (t := t) hr
    omega
  · have := Compute.in_addr hpre hc (t := t) hr
    omega
  · have := Compute.out_addr hpre hc (t := t) hr
    omega
  · have := Compute.gate_addr hpre hc (t := t) hcc
    rw [h1, h2]
    omega
  · have := Compute.decay_addr hpre hc (t := t) h2 h3 h4
    rw [h1, h5]
    omega

omit hg in
/-- The Compute phase. -/
theorem compute_mem {j0 k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : Compute.Inv P L X g j0 k s)
    (hne : ∀ f, e.kind ≠ .ub f) : MemEv P L mem0 X g k e := by
  obtain ⟨pos, hR, -⟩ := hI
  have hev := Compute.Proto.ev_at hpre hX hR hσ he
  cases pos with
  | entry =>
    rw [show e = _ from hev]
    exact .quiet (by direct_quiet)
  | tile t n =>
    have hn : n < 268 := hR.facts.pos
    rcases Compute.Proto.pos_cases hn with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h2, h264⟩
    · obtain ⟨ok, rfl⟩ := Compute.Proto.evAt_0.mp hev
      exact .quiet (by direct_quiet)
    · obtain ⟨ok, rfl⟩ := Compute.Proto.evAt_1.mp hev
      exact .quiet (by direct_quiet)
    · rw [Compute.Proto.evAt_264.mp hev]
      exact .quiet (by direct_quiet)
    · rw [Compute.Proto.evAt_265.mp hev]
      exact .quiet (by direct_quiet)
    · rw [Compute.Proto.evAt_266.mp hev]
      exact .quiet (by direct_quiet)
    · rw [Compute.Proto.evAt_267.mp hev]
      exact .quiet (by direct_quiet)
    · rw [Compute.Proto.evAt_body h2 h264] at hev
      obtain ⟨pc, kd⟩ := e
      by_cases ha : (Compute.Proto.addrOf n).2.2 = 0
      · rw [ite_eq_left ha] at hev
        rcases hev with ⟨op, own, recv, h⟩ | ⟨f, h⟩
        · simp only at h
          subst h
          exact .quiet (by direct_quiet)
        · exact absurd h (hne f)
      · rw [ite_eq_right ha] at hev
        have hfr := acc_frame hpre (Compute.Proto.refAt_compute hR) (t := t) hn ha
        have hwin : InWin P L g (Compute.Proto.accOf P L g t n).loc
            (Compute.Proto.accOf P L g t n).size :=
          ⟨rfl, rfl, hfr.1, by simp only [Compute.Proto.accOf]; omega⟩
        rcases hev with ⟨bs, h, -⟩ | ⟨bs, h, -⟩
        · simp only at h
          subst h
          exact .rdWin hwin
        · simp only at h
          subst h
          exact .wrWin hwin

/-- The Producer phase. -/
theorem producer_mem (hw : warp g = 4) {k : Nat} {s : D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : At (code L) X g k s)
    (hI : Producer.Inv P L X g k s) : MemEv P L mem0 X g k e := by
  obtain ⟨pos, w, p, x, rfl, hr, hl, hev, -⟩ := Producer.producer_good hpre hX hg hw he hσ hI
  obtain ⟨pc, kd⟩ := e
  cases pos with
  | entry =>
    cases hev
    exact .quiet (by direct_quiet)
  | poll c u =>
    obtain ⟨ok, h⟩ := hev
    cases h
    exact .quiet (by direct_quiet)
  | arrive c u =>
    cases hev
    exact .quiet (by direct_quiet)
  | tail j =>
    obtain ⟨ok, h⟩ := hev
    cases h
    exact .quiet (by direct_quiet)
  | load c u i =>
    have hk := hev
    simp only [Producer.Ev, Event.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    obtain ⟨tt, j, htt, hj, -, -, hsp, -⟩ := Producer.issue_shape hr hl hev
    rw [hsp]
    refine .load (.inr ⟨tt, htt, j, hj, rfl⟩) (fun x y z l h => ?_) fun x y z l h => ?_
    · exact Source.tileSource hpre g hg tt htt j hj x y z l h
    · obtain ⟨⟨hsp', hc, -, -⟩, hlo, hhi, -⟩ := Producer.tileLoad_writeLoc hpre hj h
      have h3 : tt % 3 < 3 := Nat.mod_lt _ (by decide)
      have hd := Producer.dstAbs_form j hj
      have hb : Protocol.loadBytes j ≤ 512 := by
        unfold Protocol.loadBytes
        split_ifs <;> decide
      refine ⟨hsp', hc, ?_, ?_⟩
      · split_ifs at hd <;> omega
      · simp only [Protocol.loadBytes] at hhi
        split_ifs at hd hhi <;> omega

/-- The Store phase. -/
theorem store_mem {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : Store.Inv P X g k s) (hne : ∀ f, e.kind ≠ .ub f) :
    MemEv P L mem0 X g k e := by
  obtain ⟨pos, hr, -, hev, -⟩ := Store.store_good hpre hX hg he hσ hI
  have hrd : ∀ {t row c m : Nat}, Store.Row P g t row c s → m < 4 →
      InWin P L g (Store.rdAcc P g t row c m).loc (Store.rdAcc P g t row c m).size := by
    intro t row c m hrow hm
    obtain ⟨hpart, hr16, hc, -⟩ := hrow
    have h2 : t % 2 < 2 := Nat.mod_lt _ (by decide)
    exact ⟨rfl, (block_div hpre).symm, by simp only [Store.rdAcc]; omega,
      by simp only [Store.rdAcc]; omega⟩
  cases pos with
  | entry =>
    rw [show e = _ from hev]
    exact .quiet (by direct_quiet)
  | wait t =>
    obtain ⟨ok, rfl⟩ := hev
    exact .quiet (by direct_quiet)
  | ts t i =>
    rw [show e = _ from hev]
    exact .tile hσ hI
  | commit t =>
    rw [show e = _ from hev]
    exact .quiet (by direct_quiet)
  | ld0 t row c =>
    obtain ⟨bs, -, rfl⟩ := hev
    exact .rdWin (hrd hr.pos.2 (by decide))
  | ld1 t row c v0 =>
    obtain ⟨bs, -, rfl⟩ := hev
    exact .rdWin (hrd hr.pos.2 (by decide))
  | ld2 t row c v0 v1 =>
    obtain ⟨bs, -, rfl⟩ := hev
    exact .rdWin (hrd hr.pos.2 (by decide))
  | ld3 t row c v0 v1 v2 =>
    obtain ⟨bs, -, rfl⟩ := hev
    exact .rdWin (hrd hr.pos.2 (by decide))
  | gst t row c j =>
    rcases hev with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩
    · exact .wrElem hσ hI rfl
    · exact absurd rfl (hne f)
  | bwait t =>
    rw [show e = _ from hev]
    exact .quiet (by direct_quiet)
  | arrive t =>
    rw [show e = _ from hev]
    exact .quiet (by direct_quiet)

/-- The epilogue. -/
theorem epilogue_mem {j0 k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hE : Epilogue.Entered P L X g j0) (hj : j0 ≤ k)
    (hI : Epilogue.Inv P L X g j0 k s) (hne : ∀ f, e.kind ≠ .ub f) :
    MemEv P L mem0 X g k e := by
  obtain ⟨pos, hr, hon, -, -, -, hex⟩ := Epilogue.event_at hpre hX hg he hσ hI
  cases pos with
  | st j =>
    rcases hex with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩
    · have hbd := Epilogue.stAddr_bounds hpre hon j
      exact .wrWin ⟨rfl, rfl, by simp only [Epilogue.stAcc]; omega,
        by simp only [Epilogue.stAcc]; omega⟩
    · exact absurd rfl (hne f)
  | ts i =>
    rw [show e = _ from hex]
    exact .final hE hj
  | bar7 =>
    rw [show e = _ from hex]
    exact .quiet (by direct_quiet)
  | fence =>
    rw [show e = _ from hex]
    exact .quiet (by direct_quiet)
  | bar8 =>
    rw [show e = _ from hex]
    exact .quiet (by direct_quiet)
  | commit =>
    rw [show e = _ from hex]
    exact .quiet (by direct_quiet)
  | bwait =>
    rw [show e = _ from hex]
    exact .quiet (by direct_quiet)
  | bar9 =>
    rw [show e = _ from hex]
    exact .quiet (by direct_quiet)
  | exit =>
    rw [show e = _ from hex]
    exact .quiet (by direct_quiet)

omit hg in
/-- **Every event of a thread that is not undefined behaviour is classified.** -/
theorem memEv {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hne : ∀ f, e.kind ≠ .ub f) :
    MemEv P L mem0 X g k e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he hne
  cases hst with
  | startup hI => exact startup_mem hpre hX hg he hσ hI
  | conversion _ _ hI => exact conversion_mem hpre hX hg he hσ hI hne
  | carryLoad _ _ hI => exact carryLoad_mem hpre hX hg he hσ hI
  | compute _ _ _ _ hI => exact compute_mem hpre hX he hσ hI hne
  | producer hr _ _ _ hI => exact producer_mem hpre hX hg hr he hσ hI
  | store _ _ _ _ hI _ => exact store_mem hpre hX hg he hσ (hI hub) hne
  | epilogue past hj _ hI =>
    exact epilogue_mem hpre hX hg he hσ ⟨_, past.state, past.into⟩ hj (hI hub) hne

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.Direct
