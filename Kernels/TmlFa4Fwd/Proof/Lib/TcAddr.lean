-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Hooks
public import Lemmas.Flow.Regs
import Lemmas.Flow.TcLdTmpl

@[expose] public section

/-! # Tensor Memory addresses of loads and stores

Generic (lane-L candidates): a `tcgen05.ld` of shape `.32x32b` whose address register holds `a`
loads at `a`, with or without the implicit wait an assumption adds (`fires_tcLd_at`); the 32-bit
truncation is a mask (`tb32`), which `bv_decide` handles. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Flow PTX.Proof

/-- The 32-bit truncation is the low mask. -/
theorem tb32 (x : BitVec 64) : truncBits 32 x = x &&& 4294967295#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_and]
  rw [show (4294967295 : Nat) % 2 ^ 64 = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The low sixteen bits of a word, as a mask. -/
theorem low16 (x : BitVec 64) : x.toNat % 65536 = (x &&& 65535#64).toNat := by
  simp only [BitVec.toNat_and]
  rw [show (65535#64).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- **A `.32x32b` Tensor Memory load's data event** is the load at the address its register holds,
with or without an implicit wait. -/
theorem fires_tcLd_at {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta a pc : Nat} {e : Event} {o : Option TState}
    (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.tcLd ds ta .s32x32b)) e o)
    (hk : ∃ a' vals sh', e.kind = .tc (.ld a' vals sh')) :
    ∃ vals, e = ⟨pc, .tc (.ld a vals .s32x32b)⟩ := by
  have hd : isTcData e = true := by
    obtain ⟨a', vals, sh', h⟩ := hk
    obtain ⟨pc', kd⟩ := e
    simp only at h
    subst h
    rfl
  rcases eventTmpl_tcLd_cases (A := A) (L := L) (g := g) (t := t) (ds := ds) (ta := ta)
    (sh := .s32x32b) with h | h | h <;> rw [h] at hf
  · rw [tcTmpl_tcLd_none (by intro s hs; cases hs)] at hf
    obtain ⟨vals, -, he⟩ := fires_tcLd_ofTmpl hr ha hd hf
    exact ⟨vals, he⟩
  · obtain ⟨o', hf⟩ := fires_thenWaitLd hf
    rw [tcTmpl_tcLd_none (by intro s hs; cases hs)] at hf
    obtain ⟨vals, -, he⟩ := fires_tcLd_ofTmpl hr ha hd hf
    exact ⟨vals, he⟩
  · simp only [Fires] at hf
    obtain ⟨rfl, -⟩ := hf
    obtain ⟨a', vals, sh', h⟩ := hk
    cases h

/-- **A `.32x32b` Tensor Memory store's event** is at the address its register holds. -/
theorem fires_tcSt_at {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ss : List Opnd} {ta a0 pc : Nat} {e : Event} {o : Option TState}
    (hr : t.regs ta = some (b32 a0)) (ha0 : a0 < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss .s32x32b)) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    a = a0 ∧ sh = .s32x32b := by
  have htr : (truncBits 32 (BitVec.ofNat 64 a0)).toNat = a0 := by
    simp only [truncBits, BitVec.toNat_ofNat]
    omega
  obtain ⟨u, hu, hf⟩ := fires_tcSt_core hf hk (by intro h; cases h)
  have hr' : u.regs ta = some (b32 a0) := by rw [hu]; exact hr
  simp only [tcTmpl, readBits_b32' hr'] at hf
  simp only [ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf
  split_ifs at hf <;> try (simp only [Fires] at hf; rw [hf.1] at hk; cases hk)
  cases hm : ss.mapM (readValue L g u 32) with
  | error f => simp only [hm] at hf; simp only [Fires] at hf; rw [hf.1] at hk; cases hk
  | ok vs =>
    simp only [hm] at hf
    split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
      simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq] at hk
    rw [htr] at hk
    exact ⟨hk.1.symm, hk.2.2.symm⟩

end PTX.Kernels.TmlFa4Fwd.Proof
