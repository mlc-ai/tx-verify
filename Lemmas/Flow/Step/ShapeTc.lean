-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.ShapeClasses
public import Lemmas.Flow.NotTcData
public import Lemmas.Flow.Next

@[expose] public section

/-! # Tensor Memory, named-barrier and load inversions (`site_shape`)

A proof tool, generic over the kernel (from the tml-fa4 correction lane's
`Proof2/Lib/ShapeTc.lean` and `Proof2/Lib/ShapeBar.lean`). Each gives the event of an instruction
in the form `site_shape` applies (`P e` from `P` of the event named), or undefined behaviour:

* `shape_tcLd`: a `tcgen05.ld` no assumption selects with `tcLdWait`: a load of the address
  register's word;
* `shape_tcLdLoad`, `shape_tcLdWait`: the two sub-steps of a `tcgen05.ld` an assumption selects
  with `tcLdWait`: the load at sub-step 0, the implicit wait at a later one;
* `shape_tcSt`: a `tcgen05.st` no assumption selects with `tcStWaitLd`: a store at the address
  register's word;
* `shape_tcWaitSt`, `shape_tcWaitLd`: the two waits;
* `shape_barSyncNR`: `bar.sync a, n` whose barrier id and count read as words (a count that is
  neither zero nor the block); `site_shape` tries it after `shape_barSyncN` (immediates);
* `shape_barArriveImm`: `bar.arrive id, n` with immediates; `site_shape` tries it for
  `bar.arrive`;
* `shape_tcStWait`, `shape_tcStStore`: the two sub-steps of a `tcgen05.st` an assumption selects
  with `tcStWaitLd`: the implicit wait for the thread's Tensor Memory loads at sub-step 0, the
  store at the address register's word at a later one (promoted from the tml-fa4 softmax lane's
  `Proof2/Lib/ShapeTcWait.lean`);
* `shape_barArriveR`: `bar.arrive a, b` whose barrier id and count read as words (a count that is
  neither zero nor the block); `site_shape` tries it after `shape_barArriveImm` (same source);
* `shape_ldAny`: a load, without its address: a read, or undefined behaviour (for a shared load
  whose effective address `shape_ld` cannot evaluate).

The Tensor Memory lemmas and `shape_ldAny` are applied by a kernel through the hook `shape_inv`:
which of them fits depends on the kernel's assumptions and on the sub-step. -/

namespace PTX.Flow
open PTX PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat} {e : Event}
  {o : Option TState} {P : Event → Prop}

theorem shape_tcLd {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh none)) e o) (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : A.any (·.tcLdWait t.pc) = false)
    (hP : ∀ a vals, P ⟨pc, .tc (.ld a vals sh)⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e :=
  shape_cont hf ⟨nofun, nofun⟩ (fun _ hf' => by
    obtain ⟨a, vals, -, rfl, -⟩ := fires_tcLd hsh hf' hw
    exact hP a vals) hub

theorem shape_tcLdLoad {ds : List Nat} {ta : Nat} {sh : TcShape} {x : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh none)) e o) (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : A.any (·.tcLdWait t.pc) = true) (hs : t.sub = 0) (hr : t.regs ta = some (.bits 32 x))
    (ha : x.toNat < 2 ^ 32)
    (hP : ∀ a vals, P ⟨pc, .tc (.ld a vals sh)⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  have hr' : t.regs ta = some (b32 x.toNat) := by rw [hr]; simp [b32]
  exact shape_cont hf ⟨nofun, nofun⟩ (fun _ hf' => by
    obtain ⟨vals, -, rfl, -⟩ := fires_tcLd_load hsh hw hs hr' ha hf'
    exact hP _ vals) hub

theorem shape_tcLdWait {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta sh none)) e o)
    (hw : A.any (·.tcLdWait t.pc) = true) (hs : t.sub ≠ 0)
    (hP : P ⟨pc, .tc .waitLd⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e :=
  shape_cont hf ⟨nofun, nofun⟩ (fun _ hf' => by
    rw [(fires_tcLd_wait hw hs hf').1]; exact hP) hub

theorem shape_tcSt {ta : Nat} {ss : List Opnd} {sh : TcShape} {x : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o)
    (hr : t.regs ta = some (.bits 32 x)) (ha : x.toNat < 2 ^ 32)
    (hw : A.any (·.tcStWaitLd t.pc) = false)
    (hP : ∀ a vals, P ⟨pc, .tc (.st a vals sh)⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  have hr' : t.regs ta = some (b32 x.toNat) := by rw [hr]; simp [b32]
  exact shape_cont hf ⟨nofun, nofun⟩ (fun _ hf' => by
    obtain ⟨⟨vals, rfl⟩, -⟩ := fires_tcSt hr' ha hf' hw
    exact hP _ vals) hub

theorem shape_tcWaitSt (hf : Fires pc (eventTmpl A L g t .tcWaitSt) e o)
    (hP : P ⟨pc, .tc .waitSt⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e :=
  shape_cont hf ⟨nofun, nofun⟩ (fun _ hf' => by rw [(fires_tcWaitSt hf').2]; exact hP) hub

theorem shape_tcWaitLd (hf : Fires pc (eventTmpl A L g t .tcWaitLd) e o)
    (hb : L.block % 32 = 0) (hP : P ⟨pc, .tc .waitLd⟩) : P e :=
  shape_of_eq (fires_tcWaitLd hb hf) hP

/-- `bar.sync a` (`barrier.sync a`) with the barrier from a register (or any operand) and no
thread count. -/
theorem shape_barSyncR {a : Opnd} {al : Bool} {id : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.barSync a al)) e o)
    (ha : readBits L g t 32 a = .ok id) (hid : id.toNat < 16)
    (hP : P ⟨pc, .bar id.toNat none .sync⟩) : P e := by
  simp only [eventTmpl, barTmpl, ha, show ¬ 16 ≤ id.toNat by omega, ↓reduceIte] at hf
  rw [hf.1]; exact hP

theorem shape_barSyncNR {a b : Opnd} {al : Bool} {id n : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.barSyncN a b al)) e o)
    (ha : readBits L g t 32 a = .ok id) (hid : id.toNat < 16)
    (hb : readBits L g t 32 b = .ok n) (hn32 : n.toNat % 32 = 0) (hn0 : n.toNat ≠ 0)
    (hnb : n.toNat ≠ L.block) (hP : P ⟨pc, .bar id.toNat (some n.toNat) .sync⟩) : P e := by
  simp only [eventTmpl, barTmpl, ha, hb, show ¬ 16 ≤ id.toNat by omega, ↓reduceIte, hn32, hn0,
    hnb, or_self] at hf
  rw [hf.1]; exact hP

/-- The same with the count equal to the block's size (FlashMLA request G8'): `barTmpl` then omits
the count (`.bar id none .sync`), which `shape_barSyncNR` excludes. -/
theorem shape_barSyncN_block {a b : Opnd} {al : Bool} {id n : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.barSyncN a b al)) e o)
    (ha : readBits L g t 32 a = .ok id) (hid : id.toNat < 16)
    (hb : readBits L g t 32 b = .ok n) (hn : n.toNat = L.block) (hn32 : L.block % 32 = 0)
    (hP : P ⟨pc, .bar id.toNat none .sync⟩) : P e := by
  simp only [eventTmpl, barTmpl, ha, hb, show ¬ 16 ≤ id.toNat by omega, ↓reduceIte, hn, hn32,
    or_true, true_and, reduceCtorEq, false_imp_iff] at hf
  rw [hf.1]; exact hP

theorem shape_barArriveImm {id n : Nat} {al : Bool}
    (hf : Fires pc (eventTmpl A L g t (.barArrive (.imm id) (.imm n) al)) e o) (hid : id < 16)
    (hn : n < 2 ^ 31) (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (hnb : n ≠ L.block)
    (hP : P ⟨pc, .bar id (some n) .arrive⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e :=
  shape_cont hf ⟨nofun, nofun⟩ (fun _ hf' => by
    rw [(fires_barArrive_imm hid hn hn32 hn0 hnb hf').1]; exact hP) hub

theorem shape_ldAny {a : MemAccess} (hf : Fires pc (eventTmpl A L g t (.mem a)) e o)
    (hk : a.kind = .load) (hnc : a.nc = false) (he : a.ext = .same)
    (hP : ∀ r bs, P ⟨pc, .rd r bs⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e :=
  shape_cont hf ⟨nofun, nofun⟩ (fun _ hf' => by
    obtain ⟨r, bs, rfl, -⟩ := fires_load hk hnc hf' he
    exact hP r bs) hub

theorem shape_tcStWait {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o)
    (hw : A.any (·.tcStWaitLd t.pc) = true) (hs : t.sub = 0) (hb : L.block % 32 = 0)
    (hP : P ⟨pc, .tc .waitLd⟩) : P e := by
  simp only [eventTmpl, tcStTmpl, hw, hs, hb, ↓reduceIte, Fires] at hf
  rw [hf.1]; exact hP

theorem shape_tcStStore {ta : Nat} {ss : List Opnd} {sh : TcShape} {x : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o)
    (hw : A.any (·.tcStWaitLd t.pc) = true) (hs : t.sub ≠ 0)
    (hr : t.regs ta = some (.bits 32 x)) (ha : x.toNat < 2 ^ 32)
    (hP : ∀ a vals, P ⟨pc, .tc (.st a vals sh)⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  have heq : eventTmpl A L g t (.tcSt ta ss sh) =
      eventTmpl ([] : List Assumption) L g { t with sub := 0 } (.tcSt ta ss sh) := by
    simp [eventTmpl, tcStTmpl, hw, hs]
  rw [heq] at hf
  exact shape_tcSt (A := []) (t := { t with sub := 0 }) hf hr ha rfl hP hub

theorem shape_barArriveR {a b : Opnd} {al : Bool} {id n : BitVec 64}
    (hf : Fires pc (eventTmpl A L g t (.barArrive a b al)) e o)
    (ha : readBits L g t 32 a = .ok id) (hid : id.toNat < 16)
    (hb : readBits L g t 32 b = .ok n) (hn32 : n.toNat % 32 = 0) (hn0 : n.toNat ≠ 0)
    (hnb : n.toNat ≠ L.block) (hP : P ⟨pc, .bar id.toNat (some n.toNat) .arrive⟩) : P e := by
  simp only [eventTmpl, barTmpl, ha, hb, show ¬ 16 ≤ id.toNat by omega, ↓reduceIte, hn32, hn0,
    hnb, or_self, ne_eq, not_false_eq_true, imp_self, and_self] at hf
  rw [hf.1]; exact hP

end PTX.Flow
