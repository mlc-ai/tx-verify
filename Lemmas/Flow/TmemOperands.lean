-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Alloc
public import Lemmas.Flow.Resource
public import Lemmas.Flow.Bar

@[expose] public section

/-! # The operands of the paired Tensor Memory instructions and of an immediate `bar.sync`

A proof tool. At a state whose operands evaluate, a `tcgen05.alloc` fires the request with the
address and the column count its operands hold (`fires_tcAlloc_at`), then its address store, four
bytes at that address (`fires_tcAllocStore_at`); a `tcgen05.dealloc` frees the column and the
count its operands hold (`fires_tcDealloc_at`); a `tcgen05.relinquish_alloc_permit` and a
`tcgen05.dealloc` fire their operation, as every continuing event of theirs is one
(`fires_tcRelinquish_some`, `fires_tcDealloc_some`). A `bar.sync` with an immediate barrier and
count fires the arrival on that barrier with that count (`fires_barSyncN_imm`). -/

namespace PTX.Flow
open PTX PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat} {e : Event}

/-- The allocation request names the address and the column count of its operands. -/
theorem fires_tcAlloc_at {u : TState} {group : CtaGroup} {base : Nat} {off : Int} {nc : Opnd}
    {dst : Loc} {n : BitVec 64} (hd : effAddr L g t .shared base off = .ok dst)
    (hn : readBits L g t 32 nc = .ok n) (hs : t.sub = 0)
    (hf : Fires pc (eventTmpl A L g t (.tcAlloc group base off nc)) e (some u)) :
    e.kind = .tc (.resource group (some dst) (.alloc n.toNat)) := by
  simp only [eventTmpl, tcTmpl, hd, hn, hs, bind, Except.bind, pure, Except.pure] at hf
  split_ifs at hf
  all_goals simp only [ofExec, Fires, throw, throwThe, MonadExceptOf.throw] at hf
  all_goals first
    | (simp at hf; done)
    | (obtain ⟨rfl, -⟩ := hf
       rfl)

/-- The allocation's address store writes four bytes at the address of its operands. -/
theorem fires_tcAllocStore_at {o : Option TState} {group : CtaGroup} {base : Nat} {off : Int}
    {nc : Opnd} {dst : Loc} (hd : effAddr L g t .shared base off = .ok dst) (hs : t.sub = 1)
    (hf : Fires pc (eventTmpl A L g t (.tcAlloc group base off nc)) e o)
    (hne : ∀ f, e.kind ≠ .ub f) :
    ∃ a bs, e.kind = .wr a bs ∧ a.loc = dst ∧ a.size = 4 ∧ bs.length = 4 := by
  simp only [eventTmpl, tcTmpl, hd, hs, bind, Except.bind, pure, Except.pure] at hf
  cases hn : readBits L g t 32 nc with
  | error f =>
    simp only [hn] at hf
    split_ifs at hf <;> simp only [ofExec, Fires, throw, throwThe, MonadExceptOf.throw] at hf <;>
      exact absurd (congrArg Event.kind hf.1) (hne _)
  | ok n =>
    simp only [hn] at hf
    split_ifs at hf
    all_goals simp only [ofExec, Fires, throw, throwThe, MonadExceptOf.throw] at hf
    all_goals first
      | contradiction
      | exact absurd (congrArg Event.kind hf.1) (hne _)
      | (obtain ⟨col, -, rfl, -⟩ := hf
         refine ⟨{ loc := dst, size := 4 }, _, rfl, rfl, rfl, ?_⟩
         simp [Value.toBytes, Value.bytes])

/-- The deallocation frees the column and the count of its operands. -/
theorem fires_tcDealloc_at {o : Option TState} {group : CtaGroup} {ta nc : Opnd} {a n : BitVec 64}
    (ha : readBits L g t 32 ta = .ok a) (hn : readBits L g t 32 nc = .ok n)
    (hf : Fires pc (eventTmpl A L g t (.tcDealloc group ta nc)) e o)
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (hk : e.kind = .tc (.resource grp dst act)) :
    grp = group ∧ dst = none ∧ act = .dealloc a.toNat n.toNat := by
  simp only [eventTmpl, tcTmpl, ha, hn, bind, Except.bind, pure, Except.pure] at hf
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  split_ifs at hf
  all_goals simp only [ofExec, Fires, throw, throwThe, MonadExceptOf.throw] at hf
  all_goals first
    | (simp at hf; done)
    | (simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hf
       obtain ⟨⟨-, rfl, rfl, rfl⟩, -⟩ := hf
       exact ⟨rfl, rfl, rfl⟩)

/-- A continuing event of a deallocation is its operation. -/
theorem fires_tcDealloc_some {u : TState} {group : CtaGroup} {ta nc : Opnd}
    (hf : Fires pc (eventTmpl A L g t (.tcDealloc group ta nc)) e (some u)) :
    ∃ dst act, e.kind = .tc (.resource group dst act) := by
  rcases fires_tmemTmpl tmemTmpl_dealloc hf with ⟨f, rfl⟩ | ⟨dst, act, rfl⟩
  · exfalso
    cases h : eventTmpl A L g t (.tcDealloc group ta nc) <;> rw [h] at hf <;>
      simp only [Fires] at hf <;> simp_all
  · exact ⟨dst, act, rfl⟩

/-- A continuing event of a permit relinquishment is its operation. -/
theorem fires_tcRelinquish_some {u : TState} {group : CtaGroup}
    (hf : Fires pc (eventTmpl A L g t (.tcRelinquish group)) e (some u)) :
    e.kind = .tc (.resource group none .relinquish) := by
  rcases fires_tmemTmpl tmemTmpl_relinquish hf with ⟨f, rfl⟩ | ⟨dst, act, rfl⟩
  · exfalso
    cases h : eventTmpl A L g t (.tcRelinquish group) <;> rw [h] at hf <;>
      simp only [Fires] at hf <;> simp_all
  · obtain ⟨-, rfl, rfl⟩ := fires_tcRelinquish_resource hf rfl
    rfl

/-- A `bar.sync id, n` with immediate operands, a count other than zero and the block size, fires
the arrival on `id` with count `n`. -/
theorem fires_barSyncN_imm {o : Option TState} {id n : Nat} {al : Bool} (hid : id < 16)
    (hn : n < 2 ^ 32) (hn32 : n % 32 = 0) (hn0 : n ≠ 0) (hnb : n ≠ L.block)
    (hf : Fires pc (eventTmpl A L g t (.barSyncN (.imm id) (.imm n) al)) e o) :
    e = ⟨pc, .bar id (some n) .sync⟩ := by
  have himm : ∀ x : Nat, x < 2 ^ 32 →
      readBits L g t 32 (Opnd.imm (x : Int)) = .ok (BitVec.ofNat 64 x) := by
    intro x hx
    simp only [readBits, truncBits]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
    omega
  simp only [eventTmpl, barTmpl, himm id (by omega), himm n hn, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show id < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    show ¬ 16 ≤ id by omega, ↓reduceIte, hn32, hn0, hnb, or_self] at hf
  exact hf.1

/-- A deallocation's operation frees the column and the count its operands hold. -/
theorem fires_tcDealloc_ops {o : Option TState} {group : CtaGroup} {ta nc : Opnd}
    (hf : Fires pc (eventTmpl A L g t (.tcDealloc group ta nc)) e o)
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (hk : e.kind = .tc (.resource grp dst act)) :
    ∃ a n, readBits L g t 32 ta = .ok a ∧ readBits L g t 32 nc = .ok n ∧
      act = .dealloc a.toNat n.toNat := by
  cases ha : readBits L g t 32 ta with
  | error f =>
    simp only [eventTmpl, tcTmpl, ha, bind, Except.bind] at hf
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    split_ifs at hf <;> simp [ofExec, Fires, throw, throwThe, MonadExceptOf.throw] at hf
  | ok a =>
  cases hn : readBits L g t 32 nc with
  | error f =>
    simp only [eventTmpl, tcTmpl, ha, hn, bind, Except.bind] at hf
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    subst hk
    split_ifs at hf <;> simp [ofExec, Fires, throw, throwThe, MonadExceptOf.throw] at hf
  | ok n => exact ⟨a, n, rfl, rfl, (fires_tcDealloc_at ha hn hf hk).2.2⟩

/-- A register operand reads the register's value. -/
theorem readBits_reg_congr {L' : Launch} {g' : Nat} {t' : TState} {w r : Nat}
    (h : t.regs r = t'.regs r) : readBits L g t w (.reg r) = readBits L' g' t' w (.reg r) := by
  simp [readBits, readReg, h]

end PTX.Flow
