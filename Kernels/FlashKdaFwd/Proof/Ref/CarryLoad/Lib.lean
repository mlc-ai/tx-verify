-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Inv
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Lib

@[expose] public section

/-! # Tools of the CarryLoad phase

What the generated per-site lemmas (`Sites*.lean`) and the hand-written steps share. Nothing
here names a single site.

* `ldVal_same`: the value of a 32-bit load without extension is the value the four bytes
  rebuild to. (The machine's successor at the last carry load is written with `rebuild`, at the
  other 127 with `ldVal`; this makes them one form, `Conversion.ldNext0`.)
* `ldNext_run`, `ldNext_last`: the machine's successor at a carry load in the form
  `ldNext0 e f` ("the event is a read whose four bytes have a value `v`; the next state is
  `f v`"), from the generated equation of the site: for a load that a pointer run follows, once
  the run's condition is known to hold for every loaded value; and for the last load.
* `run_at`: the pointer run "move the base pointer by a constant, swizzle" behind a load,
  evaluated on the base pointer `sptr g a`: its condition holds whatever the load returned (the
  loaded value goes to another slot) and it leaves the pointer to the swizzled address.
* `one_eq`, `one_ne`, `two_ne`: reads of a slot file with one or two rewritten slots.
* `ldSite_pc`, `ldSite_sub`, `ldSite_last`, `ldSite_inj`, `ldSite_ne_fence`: the instruction
  (`765 + 5 j`) and the sub-step of the site of carry load `j`; different loads have different
  sites, none of them the fence.
* `kOf_range`, `carryBase_range`, `ldAddr_frame`: **the read of carry load `j` of a compute
  thread is four bytes of the FP32 state buffer** (offsets 32768 to 98304 of the window of the
  thread's block), at a multiple of four. The largest address is reached by the last lane of
  warp 3 at the load with the largest constant, and ends exactly at the end of the buffer.
* `dst_ne_base`, `ptr_ne_base`, `ptr_ne_dst`: the slots a load's transition writes (the carry
  register, the pointer of the next load) are not the slot of the base pointer.

Abbreviations: `S` is the shared base `P.sharedBase`; `sptr g a` is the generic pointer to
address `a` of the shared window of the thread's own block; `swzN` is the swizzle. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value} {e : Event} {a : Nat}

/-! ### The successor at a carry load -/

/-- The value of a 32-bit load without extension is the value its bytes rebuild to. -/
theorem ldVal_same (bs : List (Option Byte)) : ldVal .same 32 bs = rebuild 3 bs := by
  unfold ldVal extendLoaded
  cases rebuild 3 bs <;> rfl

/-- **A load whose pointer run always continues**: when the run's condition holds for every
loaded value `v` and the transition's state is `f' v`, the successor is `ldNext0 e f'`. -/
theorem ldNext_run {c : Value → Prop} {f f' : Value → D} {nx : Option (Option D)}
    (hnx : nx = ldNext e c f) (h : ∀ v, c v ∧ f v = f' v) : nx = ldNext0 e f' := by
  rw [hnx]
  unfold ldNext ldNext0
  split
  · split
    · rw [across_pos (h _).1, (h _).2]
    · rfl
  · rfl

/-- **The last load**, whose successor the machine writes with `rebuild`: the same form. -/
theorem ldNext_last {f : Value → D} {nx : Option (Option D)}
    (hnx : nx = (match e.kind with
      | .rd _ bs =>
        match rebuild 3 bs with
        | .ok v => some (some (f v))
        | .error _ => none
      | _ => none)) : nx = ldNext0 e f := by
  rw [hnx]
  unfold ldNext0
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | rd a bs =>
    simp only [ldVal_same]
    rfl
  | _ => rfl

/-- **The pointer run behind a carry load, on the base pointer.** The run "move `%rd4` by the
constant `k`, swizzle" (`hrun`: its lemma of `Thread/RunPtr.lean`), started in the file in
which the load has just written the value `v` into the slot `r` of a carry register: with the
base pointer `sptr g a` in the slot of `%rd4` and `a + k` inside the window, the run's condition
holds and the state after it has the pointer to the swizzled address of `a + k` in the slot
`ro`. -/
theorem run_at {cond : (Nat → Value) → Prop} {facts : (Nat → Value) → List (Nat × Value)}
    {ro r : Nat} {v : Value} {s s' : Site} (k : Nat)
    (hrun : ∀ {o c : Nat} {off : BitVec 64} {V : Nat → Value},
      V 2250 = .ptr 64 true (.shared o c) off → Rules.MoveOk off (k : Int) →
      cond V ∧ facts V = [(ro, .ptr 64 true (.shared o c)
        (Rules.swz (Rules.movedOff off (k : Int))))])
    (hr : r ≠ 2250) (hx : x 2250 = sptr g a) (hak : a + k < 2 ^ 32) :
    cond (valueOf ⟨s, w, p, valueEx x [(r, v)]⟩) ∧
      (⟨s', w, p, valueEx (valueEx x [(r, v)])
        (facts (valueOf ⟨s, w, p, valueEx x [(r, v)]⟩))⟩ : D) =
      ⟨s', w, p, valueEx (valueEx x [(r, v)]) [(ro, sptr g (swzN (a + k)))]⟩ := by
  have hV : valueOf ⟨s, w, p, valueEx x [(r, v)]⟩ 2250 = sptr g a := by
    rw [valueOf_opaque rfl]
    simp only [valueEx_apply, List.lookup, (beq_eq_false_iff_ne.mpr hr.symm)]
    exact hx
  obtain ⟨hc, hf⟩ := const_run k (fun h1 h2 => hrun h1 h2) hV hak
  exact ⟨hc, by rw [hf]⟩

/-! ### Reads of a rewritten slot file -/

/-- The rewritten slot. -/
theorem one_eq (x : Nat → Value) (r : Nat) (v : Value) : valueEx x [(r, v)] r = v := by
  simp only [valueEx_apply, List.lookup, beq_self_eq_true, Option.getD_some]

/-- Another slot. -/
theorem one_ne {x : Nat → Value} {r r' : Nat} {v : Value} (h : r' ≠ r) :
    valueEx x [(r, v)] r' = x r' := by
  simp only [valueEx_apply, List.lookup, (beq_eq_false_iff_ne.mpr h), Option.getD_none]

/-- A slot that neither of two rewritings touches. -/
theorem two_ne {x : Nat → Value} {r1 r2 r' : Nat} {v1 v2 : Value} (h1 : r' ≠ r1)
    (h2 : r' ≠ r2) : valueEx (valueEx x [(r1, v1)]) [(r2, v2)] r' = x r' := by
  rw [one_ne h2, one_ne h1]

/-! ### The sites -/

/-- The site of carry load `j` is at instruction `765 + 5 j`. -/
theorem ldSite_pc : ∀ j < 128, (ldSite j).pc = 765 + 5 * j := by decide +kernel

/-- The site after the last load is the proxy fence. -/
theorem ldSite_last : ldSite 128 = .fenceProxy 1 := rfl

/-- A carry load is the only event of its instruction. -/
theorem ldSite_sub {j : Nat} (hj : j < 128) : (ldSite j).sub = 0 := by
  simp only [ldSite, hj, ↓reduceDIte, Site.sub]

/-- Two carry loads with the same site are the same load. -/
theorem ldSite_inj {i j : Nat} (hi : i < 128) (hj : j < 128) (h : ldSite i = ldSite j) :
    i = j := by
  simp only [ldSite, hi, hj, ↓reduceDIte, Site.load.injEq, Fin.mk.injEq] at h
  omega

/-- The site of a carry load is not the proxy fence. -/
theorem ldSite_ne_fence {j : Nat} (hj : j < 128) : ldSite j ≠ .fenceProxy 1 := by
  simp only [ldSite, hj, ↓reduceDIte, ne_eq, reduceCtorEq, not_false_eq_true]

/-! ### The slots a load's transition writes -/

/-- The carry registers are the slots 2118 to 2245. -/
theorem dst_lt {j : Nat} (hj : j < 128) : 2118 ≤ dstReg j ∧ dstReg j < 2246 := by
  by_cases h : j < 96 <;> simp only [dstReg, h, ↓reduceIte] <;> omega

theorem dst_ne_base {j : Nat} (hj : j < 128) : dstReg j ≠ 2250 := by
  have := dst_lt hj
  omega

theorem ptr_ne_base (j : Nat) : ptrReg j ≠ 2250 := by
  unfold ptrReg
  omega

theorem ptr_ne_dst {i j : Nat} (hj : j < 128) : ptrReg i ≠ dstReg j := by
  have := dst_lt hj
  unfold ptrReg
  omega

/-! ### The addresses -/

/-- The constants are multiples of 32 between 32768 and 95008. -/
theorem kOf_range {j : Nat} (hj : j < 128) :
    32768 ≤ kOf j ∧ kOf j ≤ 95008 ∧ kOf j % 32 = 0 := by
  rw [kOf_eq j hj]
  omega

/-- The base pointer of the carry loads of a compute thread is a multiple of four at most
3292 bytes above the shared base. -/
theorem carryBase_range (hc : tid g < 128) :
    ∃ off, carryBase P g = P.sharedBase + off ∧ off ≤ 3292 ∧ off % 4 = 0 := by
  have hw := (warp_lt4_iff g).mpr hc
  have hl := lane_lt g
  exact ⟨_, rfl, by omega, by omega⟩

/-- **The read of carry load `j` of a compute thread is four bytes of the FP32 state buffer**
(offsets 32768 to 98304 of the window), at a multiple of four; and the address before the
swizzle is inside the window, which is the condition of the pointer run. -/
theorem ldAddr_frame (hpre : Pre P L mem0) (hc : tid g < 128) {j : Nat} (hj : j < 128) :
    P.sharedBase + 32768 ≤ ldAddr P g j ∧ ldAddr P g j + 4 ≤ P.sharedBase + 98304 ∧
      ldAddr P g j % 4 = 0 ∧ ldAddr P g j < 2 ^ 32 ∧ carryBase P g + kOf j < 2 ^ 32 := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  obtain ⟨off, ho, h1, h2⟩ := carryBase_range (P := P) hc
  obtain ⟨k1, k2, k3⟩ := kOf_range hj
  unfold ldAddr
  rw [ho]
  have l1 : P.sharedBase + 32768 ≤ swzN (P.sharedBase + off + kOf j) :=
    swzN_lo (by omega) (by omega)
  have l2 : swzN (P.sharedBase + off + kOf j) + 4 ≤ P.sharedBase + 98304 :=
    swzN_hi (by omega) (by omega) (by omega)
  have l3 : swzN (P.sharedBase + off + kOf j) % 4 = 0 := swzN_mod4 (by omega)
  exact ⟨l1, l2, l3, by omega, by omega⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.CarryLoad
