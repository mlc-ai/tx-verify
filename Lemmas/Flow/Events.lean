-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.EventFrameSource
public import Lemmas.Execution.EventFrame
public import Lemmas.Flow.Regs
public import Lemmas.Flow.Local

@[expose] public section

/-! # Which object an mbarrier event names

A proof tool. With the operand registers known, a poll names its mbarrier object and its
parity, and an arrival its object, byte count and arrival count. Protocol proofs use these
to attribute the records of an object to the threads that issued them. A poll's template is
the wait whose continuation sets the poll's predicate to the outcome (`eventTmpl_mbarWait_next`),
so its fired event and successor are one inversion (`fires_wait_at_succ`); once a template is
known to have that form, `fires_wait_next` inverts it alone. An arrival without a state
destination continues at the next instruction (`fires_arrive_next`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- An mbarrier in the thread's own CTA, addressed by a 32-bit integer register. -/
theorem mbarLoc_b32 {L : Launch} {g : Nat} {t : TState} {base : Nat} {a : Nat}
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (h8 : a % 8 = 0) :
    mbarLoc L g t base 0 = .ok ⟨.shared, g / L.block, a⟩ := by
  have h64 : a < 18446744073709551616 := by omega
  have h32 : a < 4294967296 := ha
  simp [mbarLoc, effAddr, sharedEffAddr, readReg, hr, b32, readBits, truncBits,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, h8, bind, Except.bind,
    pure, Except.pure]

/-- A shared address of the thread's CTA held in a 32-bit register. -/
theorem effAddr_b32 {L : Launch} {g : Nat} {t : TState} {base : Nat} {a : Nat}
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) :
    effAddr L g t .shared base 0 = .ok ⟨.shared, g / L.block, a⟩ := by
  have h64 : a < 18446744073709551616 := by omega
  have h32 : a < 4294967296 := ha
  simp [effAddr, sharedEffAddr, readReg, hr, b32, readBits, truncBits,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, bind, Except.bind,
    pure, Except.pure]

/-- An mbarrier of the cluster, addressed by a 32-bit shared pointer register. -/
theorem mbarClusterLoc_ptr {L : Launch} {g : Nat} {t : TState} {base : Nat} {cta a : Nat}
    (hr : t.regs base = some (.ptr 32 false (.shared (g / L.block) cta) (BitVec.ofNat 64 a)))
    (hg : g < L.threads) (hcta : cta < L.grid)
    (hcl : L.clusterOfCta cta = L.clusterOfCta (g / L.block)) (ha : a < 2 ^ 32)
    (h8 : a % 8 = 0) :
    mbarClusterLoc L g t base 0 = .ok ⟨.shared, cta, a⟩ := by
  have h64 : a < 18446744073709551616 := by omega
  have h32 : a < 4294967296 := ha
  have hoff : (BitVec.ofNat 64 a).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]; exact ha
  have hl := readSharedAddress_ptr (gen := false) (cl :=
    true) hr (.inl rfl) hg hcta hcl (.inl rfl) (.inr rfl)
    hoff
  simp [mbarClusterLoc, sharedEffAddr, readReg, hr, hl, truncBits, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, h8, bind, Except.bind, pure, Except.pure]

/-- An mbarrier of the thread's own CTA addressed as a cluster address by a 32-bit integer
register. -/
theorem mbarClusterLoc_b32 {L : Launch} {g : Nat} {t : TState} {base : Nat} {a : Nat}
    (hr : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (h8 : a % 8 = 0) :
    mbarClusterLoc L g t base 0 = .ok ⟨.shared, g / L.block, a⟩ := by
  have h64 : a < 18446744073709551616 := by omega
  have h32 : a < 4294967296 := ha
  simp [mbarClusterLoc, sharedEffAddr, readReg, hr, b32, readBits, truncBits,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, h8, bind, Except.bind,
    pure, Except.pure]

/-- A poll names the object and parity its operands evaluate to. -/
theorem fires_wait_at {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope} {pc : Nat}
    {e : Event} {o : Option TState} {m : Loc} {q : BitVec 64}
    (hm : mbarLoc L g t base off = .ok m) (hq : readBits L g t 32 par = .ok q)
    (hf : Fires pc (eventTmpl A L g t (.mbarWait p base off par acq sc)) e o) :
    ∃ ok acq' sc', e = ⟨pc, .wait m (q.toNat % 2) ok acq' sc'⟩ ∧
      ∀ u, o = some u → u = next (setReg t p (.pred ok)) := by
  simp only [eventTmpl, tmaTmpl, hm, hq, bind, Except.bind, pure, Except.pure, ofExec] at hf
  cases acq <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
  · obtain ⟨ok, rfl, hu⟩ := hf
    exact ⟨ok, _, _, rfl, fun u h => by subst h; simpa using Option.some.inj hu⟩

/-- **The template of a poll whose object and parity evaluate**: a wait on the object with the
parity's low bit whose continuation sets the poll's predicate to the outcome and continues at the
next instruction. -/
theorem eventTmpl_mbarWait_next {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope} {m : Loc}
    {q : BitVec 64} (hm : mbarLoc L g t base off = .ok m) (hq : readBits L g t 32 par = .ok q) :
    ∃ sc', eventTmpl A L g t (.mbarWait p base off par acq sc) =
      .wait m (q.toNat % 2) (fun ok => next (setReg t p (.pred ok))) acq sc' := by
  simp only [eventTmpl, tmaTmpl, hm, hq, bind, Except.bind, pure, Except.pure, ofExec]
  cases acq <;> cases sc <;> simp only [widenMbarScope] <;> split_ifs <;> exact ⟨_, rfl⟩

/-- **A fired poll**: the wait names its object and parity, and the successor state sets the poll's
predicate to the outcome, for either outcome. -/
theorem fires_wait_at_succ {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {p base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope} {m : Loc}
    {q : BitVec 64} {pc : Nat} {e : Event}
    (hm : mbarLoc L g t base off = .ok m) (hq : readBits L g t 32 par = .ok q)
    (hf : Fires pc (eventTmpl A L g t (.mbarWait p base off par acq sc)) e (some u)) :
    ∃ ok acq' sc', e = ⟨pc, .wait m (q.toNat % 2) ok acq' sc'⟩ ∧
      u = next (setReg t p (.pred ok)) := by
  obtain ⟨sc', h⟩ := eventTmpl_mbarWait_next (A := A) hm hq
  rw [h] at hf
  obtain ⟨ok, rfl, hu⟩ := hf
  exact ⟨ok, acq, sc', rfl, Option.some.inj hu⟩

/-- **A fired poll template**: a wait whose continuation sets the poll's predicate to the outcome
fires that wait with some outcome, and the thread continues in the continuation's state. This is
the template-level inversion role proofs use once `eventTmpl_mbarWait_next` has fixed the
template's object and parity. -/
theorem fires_wait_next {t u : TState} {m : Loc} {q : Nat} {p : Nat} {acq : Bool}
    {sc : MbarScope} {pc : Nat} {e : Event}
    (hf : Fires pc (.wait m q (fun ok => next (setReg t p (.pred ok))) acq sc) e (some u)) :
    ∃ ok, e = ⟨pc, .wait m q ok acq sc⟩ ∧ u = next (setReg t p (.pred ok)) := by
  obtain ⟨ok, rfl, hu⟩ := hf
  exact ⟨ok, rfl, Option.some.inj hu⟩

/-- An arrival names the object, byte count and arrival count its operands evaluate to. -/
theorem fires_arrive_at {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {tx count : Opnd} {cluster rel : Bool} {sc : MbarScope}
    {pc : Nat} {e : Event} {o : Option TState} {m : Loc} {bytes n : BitVec 64}
    (hm : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) = .ok m)
    (hb : readBits L g t 32 tx = .ok bytes) (hn : readBits L g t 32 count = .ok n)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count cluster rel sc)) e o) :
    ∃ rel' sc', e = ⟨pc, .arrive m bytes.toNat n.toNat rel' sc'⟩ ∧ ∀ u, o = some u → u = next t :=
      by
  cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
    simp only [eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hm, hb, hn, bind,
      Except.bind, pure, Except.pure, ofExec] at hf <;>
  cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
  · obtain ⟨rfl, hu⟩ := hf
    exact ⟨_, _, rfl, fun u h => by subst h; exact Option.some.inj hu⟩

/-- **A fired arrival without a state destination**: the arrival names the object, byte count and
arrival count its operands evaluate to, and the thread continues at the next instruction. -/
theorem fires_arrive_next {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {tx count : Opnd} {cluster rel : Bool} {sc : MbarScope}
    {pc : Nat} {e : Event} {o : Option TState} {m : Loc} {bytes n : BitVec 64}
    (hm : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) = .ok m)
    (hb : readBits L g t 32 tx = .ok bytes) (hn : readBits L g t 32 count = .ok n)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count cluster rel sc none)) e o) :
    ∃ rel' sc', e = ⟨pc, .arrive m bytes.toNat n.toNat rel' sc'⟩ ∧ o = some (PTX.next t) := by
  cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
    simp only [eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hm, hb, hn, bind,
      Except.bind, pure, Except.pure, ofExec] at hf <;>
  cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
  exact ⟨_, _, hf.1, hf.2⟩

/-- A Tensor Core commit names the commit specification its operands resolve to. -/
theorem fires_tcCommit_at {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {mk : Opnd} {pc : Nat} {e : Event}
    {o : Option TState} {m : Loc} {k : BitVec 64} {s : TcCommit.Spec} (hg : g < L.threads)
    (hm : mbarClusterLoc L g t base off = .ok m) (hk : readBits L g t 16 mk = .ok k)
    (hs : TcCommit.resolve L group (g / L.block) m (BitVec.ofNat 16 k.toNat) = some s)
    (hf : Fires pc (eventTmpl A L g t (.tcCommit group base off (some mk))) e o) :
    e = ⟨pc, .tc (.commit s)⟩ ∧ ∀ u, o = some u → u = next t := by
  simp only [eventTmpl, tcCommitTmpl, hg, ↓reduceIte, hm, hk, hs, bind,
    Except.bind, pure, Except.pure, ofExec] at hf
  obtain ⟨rfl, hu⟩ := hf
  exact ⟨rfl, fun u h => by subst h; exact Option.some.inj hu⟩

end
end PTX.Flow
