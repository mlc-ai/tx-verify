-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Async
public import Lemmas.Flow.Local
public import Lemmas.Flow.Vector
public import Lemmas.Flow.UbStop
public import Lemmas.Flow.Events
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # Where a thread continues after an event

A proof tool: the state after events whose continuation is fixed by the instruction.

* An arrival that writes its state register (`mbarrier.arrive … state, [a]`) continues with
  that register cleared (`fires_arrive_state`, `At.clear_state`).
* `vote.sync.ballot` votes the thread's predicate and writes the ballot (`fires_vote`).
* `tcgen05.wait::st` (`fires_tcWaitSt`), and `bar.sync`/`bar.arrive` with immediate barrier and
  count (`fires_barImm`), continue at the next instruction.
* An element of a vector store continues at the next element or instruction
  (`fires_stv_after`).
* At a `tcgen05.ld` an assumption selects with `tcLdWait`, sub-step 0 loads, writes the
  destinations and stays at the instruction with sub-step 1 (`fires_tcLd_load`, for the shapes
  other than `.pack::16b`, which load two words per register), and sub-step 1 is the implicit
  `tcgen05.wait::ld`, continuing at the next instruction's first sub-step (`fires_tcLd_wait`).
  The destinations hold the loaded values (`setRegs_get`, `holds_setRegs`) and every other
  register keeps its value (`setRegs_other`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {pc : Nat} {e : Event}

/-- After an arrival with a state destination the thread is in `next` of the state with the
destination cleared, and the event is an arrival on the object its address evaluates to. -/
theorem fires_arrive_state {base : Nat} {off : Int} {tx count : Opnd} {cluster release : Bool}
    {scope : MbarScope} {state : Option Nat}
    (hf : Fires pc (eventTmpl A L g t
      (.mbarArrive base off tx count cluster release scope state)) e (some u)) :
    u = PTX.next (mbarStateDest t state) ∧
      ∃ m tx' c rel sc, e.kind = .arrive m tx' c rel sc ∧
        ((if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) = .ok m) ∧
        ∃ b, readBits L g t 32 tx = .ok b ∧ tx' = b.toNat := by
  simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure] at hf
  cases hm : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) with
  | error f =>
    cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
      simp only [Bool.false_eq_true, ↓reduceIte, hm, ofExec, widenMbarScope, ite_self,
        Fires] at hf <;> simp at hf
  | ok m =>
    cases hb : readBits L g t 32 tx with
    | error f =>
      cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
        simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, ofExec, widenMbarScope, ite_self,
          Fires] at hf <;> simp at hf
    | ok bytes =>
      cases hn : readBits L g t 32 count with
      | error f =>
        cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
          simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, hn, ofExec, widenMbarScope,
            ite_self, Fires] at hf <;> simp at hf
      | ok n =>
        cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
          simp only [Bool.false_eq_true, ↓reduceIte, hm, hb, hn, ofExec] at hf <;>
          cases release <;> cases scope <;> simp only [widenMbarScope] at hf <;>
          split_ifs at hf <;>
          exact ⟨Option.some.inj hf.2, _, _, _, _, _, by rw [hf.1], by simp,
            bytes, rfl, rfl⟩

/-- Clearing a register no fact names keeps the facts. -/
theorem At.clear_state {pc r : Nat} {F : List (Nat × Value)} (h : At t pc F)
    (hr : ∀ p ∈ F, p.1 ≠ r) : At (PTX.next (mbarStateDest t (some r))) (pc + 1) F :=
  ⟨congrArg (· + 1) h.1, h.2.1, h.2.2.1, h.2.2.2.1, holds_update h.2.2.2.2 hr⟩

/-- A `vote.sync.ballot` that continues fired a vote of the thread's predicate and writes the
ballot to its destination. -/
theorem fires_vote {d a : Nat} {neg : Bool} {mask : Opnd} {pv : Bool} {ty : Option DType}
    (hp : readPred L g t (.reg a) = .ok pv)
    (hf : Fires pc (eventTmpl A L g t
      (.warp ⟨.vote .ballot neg, ty, [some d], [.reg a], some mask⟩)) e (some u)) :
    ∃ m b, e = ⟨pc, .vote m (pv != neg) b⟩ ∧
      u = PTX.next (setReg t d (.bits 32 (BitVec.ofNat 64 b.toNat))) := by
  simp only [eventTmpl, warpTmpl_vote, voteTmpl] at hf
  cases hm : readBits L g t 32 mask with
  | error f => simp [hm, Fires] at hf
  | ok m =>
    rw [hm, hp] at hf
    simp only at hf
    split_ifs at hf
    · obtain ⟨b, h1, h2⟩ := hf
      exact ⟨_, b, h1, Option.some.inj h2⟩
    · simp [Fires] at hf

/-- `tcgen05.wait::st` fires its wait and continues at the next instruction. -/
theorem fires_tcWaitSt (hf : Fires pc (eventTmpl A L g t .tcWaitSt) e (some u)) :
    u = PTX.next t ∧ e = ⟨pc, .tc .waitSt⟩ := by
  simp only [eventTmpl, tcTmpl] at hf
  split_ifs at hf
  · simp only [ofExec, pure, Except.pure, Fires] at hf
    exact ⟨Option.some.inj hf.2, hf.1⟩
  · simp [ofExec, Fires, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hf

/-- A named barrier with an immediate barrier `id` and thread count `n` (a multiple of the warp
size, neither zero nor the block) fires `bar id n` and continues at the next instruction. -/
theorem fires_barTmpl_imm {id n : Nat} {mode : BarMode} (hid : id < 16) (hn : n < 2 ^ 31)
    (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (hnb : n ≠ L.block)
    (hf : Fires pc (barTmpl L g t (.imm id) (some (.imm n)) mode) e (some u)) :
    e = ⟨pc, .bar id (some n) mode⟩ ∧ u = PTX.next t := by
  have hid' : (truncBits 32 (BitVec.ofInt 64 (id : Int))).toNat = id := by
    simp [truncBits]; omega
  have hn' : (truncBits 32 (BitVec.ofInt 64 (n : Int))).toNat = n := by
    simp [truncBits]; omega
  simp only [barTmpl, readBits, pure, Except.pure, hid', hn'] at hf
  simp only [show ¬ 16 ≤ id by omega, ↓reduceIte, hn32, hn0, hnb, or_self, ne_eq,
    not_false_eq_true, implies_true, and_self, Fires] at hf
  exact ⟨hf.1, Option.some.inj hf.2⟩

/-- `bar.sync id, n` with immediates fires `bar id n` and continues at the next instruction. -/
theorem fires_barSync_imm {id n : Nat} {al : Bool} (hid : id < 16) (hn : n < 2 ^ 31)
    (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (hnb : n ≠ L.block)
    (hf : Fires pc (eventTmpl A L g t (.barSyncN (.imm id) (.imm n) al)) e (some u)) :
    e = ⟨pc, .bar id (some n) .sync⟩ ∧ u = PTX.next t :=
  fires_barTmpl_imm (g := g) hid hn hn32 hn0 hnb hf

/-- `bar.arrive id, n` with immediates fires `bar id n` (arrive) and continues at the next
instruction. -/
theorem fires_barArrive_imm {id n : Nat} {al : Bool} (hid : id < 16) (hn : n < 2 ^ 31)
    (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (hnb : n ≠ L.block)
    (hf : Fires pc (eventTmpl A L g t (.barArrive (.imm id) (.imm n) al)) e (some u)) :
    e = ⟨pc, .bar id (some n) .arrive⟩ ∧ u = PTX.next t :=
  fires_barTmpl_imm (g := g) hid hn hn32 hn0 hnb hf

/-- An element of a vector store that continues fired a write and continues at the next
element, or past the instruction after the last. -/
theorem fires_stv_after {sp : StateSpace} {ty : DType} {bw base : Nat} {off : Int}
    {srcs : List Opnd} {lsp : Space}
    (hr : MemAccess.rule
      ({ kind := .store, space := some sp, sem := .weak, elem := ty, vec := srcs.length,
         addr := ⟨.reg base bw, off⟩, srcs := srcs } : MemAccess) = some .threadAccess)
    (hs : MemAccess.locSpace?
      ({ kind := .store, space := some sp, sem := .weak, elem := ty, vec := srcs.length,
         addr := ⟨.reg base bw, off⟩, srcs := srcs } : MemAccess) = some lsp)
    (hf : Fires pc (eventTmpl A L g t
      (.mem { kind := .store, space := some sp, sem := .weak, elem := ty, vec := srcs.length,
              addr := ⟨.reg base bw, off⟩, srcs := srcs })) e (some u)) :
    u = afterStore t srcs ∧ ∃ a bs, e = ⟨pc, .wr a bs⟩ := by
  simp only [eventTmpl] at hf
  rw [memTmpl_store hr hs rfl rfl (by simp)] at hf
  simp only [storeTmpl] at hf
  repeat' split at hf
  all_goals simp only [Fires, reduceCtorEq, and_false] at hf
  exact ⟨Option.some.inj hf.2, _, _, hf.1⟩

/-- A `tcgen05.st` from the address its register holds stores there and continues at the next
instruction; a `.pack::16b` store stores the half-words of its sources (`TcPack16.unpack`). -/
theorem fires_tcSt {ta a : Nat} {ss : List Opnd} {sh : TcShape} (hr : t.regs ta = some (b32 a))
    (ha : a < 2 ^ 32) (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e (some u))
    (hwait : A.any (·.tcStWaitLd t.pc) = false := by hooks_off) :
    (∃ vals, e = ⟨pc, .tc (.st a vals sh)⟩) ∧ u = PTX.next t := by
  have htr : (truncBits 32 (BitVec.ofNat 64 a)).toNat = a := by
    simp only [truncBits, BitVec.toNat_ofNat]
    omega
  rw [eventTmpl_tcSt_noWait hwait] at hf
  cases sh <;> simp only [tcTmpl, readBits_b32' hr] at hf
  all_goals
    simp only [ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf
    split_ifs at hf <;> try (simp only [Fires, reduceCtorEq, and_false] at hf)
    cases hm : ss.mapM (readValue L g t 32) with
    | error f => simp [hm] at hf
    | ok vals =>
      simp only [hm] at hf
      split_ifs at hf <;> try (simp only [reduceCtorEq, and_false] at hf)
      rw [htr] at hf
      exact ⟨⟨_, hf.1⟩, Option.some.inj hf.2⟩

/-- A fired event is at the instruction's program counter. -/
theorem fires_pc {m : Tmpl} {o : Option TState} (h : Fires pc m e o) : e.pc = pc := by
  cases m <;> simp only [Fires] at h <;> aesop

/-- An arrival with a state destination names the object, byte count and arrival count its
operands evaluate to. -/
theorem fires_arrive_state_at {base : Nat} {off : Int} {tx count : Opnd} {cluster rel : Bool}
    {sc : MbarScope} {state : Option Nat} {o : Option TState} {m : Loc} {bytes n : BitVec 64}
    (hm : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) = .ok m)
    (hb : readBits L g t 32 tx = .ok bytes) (hn : readBits L g t 32 count = .ok n)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count cluster rel sc state)) e o) :
    ∃ rel' sc', e = ⟨pc, .arrive m bytes.toNat n.toNat rel' sc'⟩ := by
  cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
    simp only [eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hm, hb, hn, bind,
      Except.bind, pure, Except.pure, ofExec] at hf <;>
  cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
  exact ⟨_, _, hf.1⟩

/-- A named barrier whose operands read as a barrier `id < 16` and a count `n` (a multiple of
the warp size, neither zero nor the block) fires `bar id n`. -/
theorem fires_barTmpl_at {a b : Opnd} {id n : Nat} {mode : BarMode} {o : Option TState}
    (ha : readBits L g t 32 a = .ok (BitVec.ofNat 64 id))
    (hb : readBits L g t 32 b = .ok (BitVec.ofNat 64 n)) (hid : id < 16) (hn : n < 2 ^ 31)
    (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (hnb : n ≠ L.block)
    (hf : Fires pc (barTmpl L g t a (some b) mode) e o) : e = ⟨pc, .bar id (some n) mode⟩ := by
  have hid' : (BitVec.ofNat 64 id).toNat = id := by simp; omega
  have hn' : (BitVec.ofNat 64 n).toNat = n := by simp; omega
  simp only [barTmpl, ha, hb, hid', hn'] at hf
  simp only [show ¬ 16 ≤ id by omega, ↓reduceIte, hn32, hn0, hnb, or_self, ne_eq,
    not_false_eq_true, implies_true, and_self, Fires] at hf
  exact hf.1

/-! ### Loads with an implicit wait -/

/-- Registers outside the listed ones keep their values through a register write. -/
theorem setRegs_other (t : TState) (ds : List Nat) (vs : List Value) (r : Nat)
    (hr : r ∉ ds) : (setRegs t ds vs).regs r = t.regs r := by
  induction ds generalizing t vs with
  | nil => rfl
  | cons d ds ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      rw [setRegs, ih _ _ (by intro h; exact hr (List.mem_cons_of_mem _ h))]
      exact Function.update_of_ne (by intro h; exact hr (by simp [h])) _ _

/-- A register write keeps the thread's pc, sub-step, accumulator and fault. -/
theorem setRegs_skel : ∀ (t : TState) (ds : List Nat) (vs : List Value),
    (setRegs t ds vs).pc = t.pc ∧ (setRegs t ds vs).sub = t.sub ∧
      (setRegs t ds vs).acc = t.acc ∧ (setRegs t ds vs).fault = t.fault
  | _, [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | _, _ :: _, [] => ⟨rfl, rfl, rfl, rfl⟩
  | t, d :: ds, v :: vs => setRegs_skel (setReg t d v) ds vs

/-- The registers of a register write after `next`: those of the write. -/
theorem setRegs_next_regs : ∀ (t : TState) (ds : List Nat) (vs : List Value),
    (setRegs (PTX.next t) ds vs).regs = (setRegs t ds vs).regs
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | t, d :: ds, v :: vs => setRegs_next_regs (setReg t d v) ds vs

/-- A listed register holds the value at its position, when the registers are distinct. -/
theorem setRegs_get : ∀ (ds : List Nat) (vs : List Value) (t : TState) (p : Nat) (r : Nat)
    (v : Value), ds.Nodup → ds[p]? = some r → vs[p]? = some v →
      (setRegs t ds vs).regs r = some v
  | [], _, _, _, _, _, _, hr, _ => by simp at hr
  | _ :: _, [], _, _, _, _, _, _, hv => by simp at hv
  | d :: ds, v' :: vs, t, 0, r, v, hnd, hr, hv => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hv
    rw [← hr, ← hv]
    show (setRegs (setReg t d v') ds vs).regs d = some v'
    rw [setRegs_other (setReg t d v') ds vs d (List.nodup_cons.mp hnd).1]
    simp [setReg]
  | d :: ds, v' :: vs, t, p + 1, r, v, hnd, hr, hv => by
    simp only [List.getElem?_cons_succ] at hr hv
    exact setRegs_get ds vs (setReg t d v') p r v (List.nodup_cons.mp hnd).2 hr hv

/-- The registers a load writes hold its values: the facts of its destinations, when each
destination's value in the table is the loaded value at its position. -/
theorem holds_setRegs (t : TState) (ds : List Nat) (xs : List Value) (val : Nat → Value)
    (hnd : ds.Nodup) (hlen : xs.length = ds.length)
    (hval : ∀ p < ds.length, val (ds.getD p 0) = xs.getD p (b32 0)) :
    Holds (setRegs t ds xs).regs (Flow.factsFrom ds val) := by
  refine holds_of_pointwise fun r hr => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hr
  have hpx : p < xs.length := by omega
  have hd : ds.getD p 0 = ds[p] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  have hv := hval p hp
  rw [hd] at hv
  rw [hv]
  exact setRegs_get ds _ t p _ _ hnd (List.getElem?_eq_getElem hp)
    (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpx])

/-- At a `tcgen05.ld` of a shape other than `.pack::16b` an assumption selects with `tcLdWait`,
sub-step 0 is the load at the address its register holds: it writes the destinations and stays at
the instruction, at sub-step 1. -/
theorem fires_tcLd_load {ds : List Nat} {ta a : Nat} {sh : TcShape}
    (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : A.any (·.tcLdWait t.pc) = true)
    (hs : t.sub = 0) (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) e (some u)) :
    ∃ vals, vals.length = ds.length ∧ e = ⟨pc, .tc (.ld a vals sh)⟩ ∧
      u = { setRegs (PTX.next t) ds vals with pc := t.pc, sub := 1 } := by
  simp only [eventTmpl, tcLdTmpl, hw, ↓reduceIte, hs, tcTmpl_tcLd_none hsh,
    readBits_b32' hr] at hf
  simp only [truncBits, BitVec.toNat_ofNat, ofExec,
    bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hf
  split_ifs at hf <;> simp only [Tmpl.thenWaitLd, Fires, reduceCtorEq, and_false] at hf
  obtain ⟨vals, hl, rfl, hu⟩ := hf
  refine ⟨vals, hl, ?_, Option.some.inj hu⟩
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega)]

/-- At a `tcgen05.ld` an assumption selects with `tcLdWait`, sub-step 1 is the implicit
`tcgen05.wait::ld`, continuing at the next instruction's first sub-step. -/
theorem fires_tcLd_wait {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hw : A.any (·.tcLdWait t.pc) = true)
    (hs : t.sub ≠ 0) (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh)) e (some u)) :
    e = ⟨pc, .tc .waitLd⟩ ∧ u = { PTX.next t with sub := 0 } := by
  simp only [eventTmpl, tcLdTmpl, hw, ↓reduceIte, hs, Fires] at hf
  exact ⟨hf.1, (Option.some.inj hf.2)⟩

end
end PTX.Flow
