-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TcLdTmpl

@[expose] public section

/-! # A Tensor Memory load at an address outside the issuing warp's lanes

A proof tool. A `tcgen05.ld` whose address register holds a 32-bit integer that THREAD-TC-DATA-
ADDRESS does not accept (`tcDataAddressOk` is false: the lane field leaves the warp's chunk, or a
half-split offset leaves the column field) has the template `.ub .noRule` (`tcLd_ub`), so a thread
that reaches it by local steps is dead (`tcLd_dead`). -/

namespace PTX.Flow

open PTX PTX.Proof

noncomputable section

/-- **A Tensor Memory load of an address the rule does not accept is undefined behaviour.** -/
theorem tcLd_ub {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {ds : List Nat}
    {ta : Nat} {a : Nat} {sh : TcShape} {red : Option TcLdRed}
    (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32) (hs : tcDataAddressOk L g sh a = false)
    (hw : A.any (·.tcLdWait t.pc) = false) :
    eventTmpl A L g t (.tcLd ds ta sh red) = .ub .noRule := by
  have h32 : a < 4294967296 := ha
  have h64 : a < 18446744073709551616 := by omega
  rw [eventTmpl_tcLd_noWait hw]
  by_cases hb : L.block % 32 = 0 <;> by_cases hn : sh.countOk ds.length = true <;>
  cases sh with
  | packed16 s =>
    by_cases hn' : s.countOk ds.length = true <;>
      simp [tcTmpl, hb, hn', readBits_b32' hr, truncBits, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, hs, ofExec, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw]
  | _ =>
    simp [tcTmpl, hb, hn, readBits_b32' hr, truncBits, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64, hs, ofExec, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw]

/-- **A thread at a Tensor Memory load of an address the rule does not accept is dead.** -/
theorem tcLd_dead {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta : Nat} {a : Nat} {sh : TcShape} {red : Option TcLdRed}
    (hc : K.code[t.pc]? = some ⟨none, .tcLd ds ta sh red⟩) (hf : t.fault = none)
    (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32) (hs : tcDataAddressOk L g sh a = false)
    (hw : A.any (·.tcLdWait t.pc) = false) :
    Machine.Dead (K := K) (A := A) (L := L) (g := g) t := by
  refine Machine.dead_of_ub (f := .noRule) ?_
  rw [out_event hf hc (by simp [guardHolds]; rfl) rfl, tcLd_ub hr ha hs hw]

end
end PTX.Flow
