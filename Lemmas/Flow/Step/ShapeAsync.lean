-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.Step.ShapeRegs

@[expose] public section

/-! # Shape inversions for `cp.async` with a source-size register, TMA copies and mbarriers

A proof tool (promoted from the tml-fa4 loader's `Proof2/Lib/ShapeAsync.lean`):

* `shape_cpAsyncN`: a `cp.async` whose source size is a register the site's facts do not
  decide (a `selp` on a symbolic condition): its copy event with some source size, or undefined
  behaviour. `shape_cpAsync` needs the size's value.
* `shape_cpTensorAt`: a TMA tensor copy without multicast or cluster barrier whose barrier
  address reads as `m`: its issue event names `m`. `shape_cpTensor` leaves the barrier as an
  equation on `mbarLoc`.
* `mbarLoc_bits`: an mbarrier address register holding a 32-bit word whose sum with the offset
  is a multiple of 8 locates the object at `smLoc`. -/

namespace PTX.Flow
open PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
variable {t : TState} {pc : Nat} {e : Event} {o : Option TState} {P : Event → Prop}

/-- A `cp.async` copy whose addresses read as `d` and `s`: its copy event of the non-bulk
asynchronous group with some source size, or undefined behaviour. -/
theorem shape_cpAsyncN {db sb size : Nat} {doff soff : Int} {source : CpAsyncSource}
    {policy : Option Opnd} {d s : Loc}
    (hf : Fires pc (eventTmpl A L g t (.cpAsync db doff sb soff size source policy)) e o)
    (hd : effAddr L g t .shared db doff = .ok d) (hs : effAddr L g t .global sb soff = .ok s)
    (hP : ∀ n, P ⟨pc, .copy ⟨{ loc := s, size := n }, { loc := d, size := size }, .asyncGroup,
      .whole, none, true, none⟩⟩)
    (hub : ∀ f, P ⟨pc, .ub f⟩) : P e := by
  cases hn : cpAsyncSourceSize L g t size source with
  | ok n => exact shape_cpAsync hf hd hs hn (hP n) hub
  | error f =>
    simp only [eventTmpl, cpAsyncTmpl, hd, hs, hn, bind, Except.bind] at hf
    repeat' split at hf
    all_goals (simp only [ofExec, Fires] at hf; rw [hf.1]; exact hub _)

/-- A TMA tensor copy (no multicast, a barrier of the thread's CTA) whose barrier address reads
as `m`: its issue event on `m`, or undefined behaviour. -/
theorem shape_cpTensorAt {grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd}
    {cs : List Opnd} {lm : TensorMode} {pol : Option Opnd} {m : Loc}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor false grp dst off map cs mb moff none lm pol)) e o)
    (hm : mbarLoc L g t mb moff = .ok m)
    (hP : ∀ a s, s.mbar = m → P ⟨pc, .tensorIssue a s⟩) (hub : ∀ f, P ⟨pc, .ub f⟩) : P e :=
  shape_cpTensor hf (fun a s h => by
    simp only [Bool.false_eq_true, ↓reduceIte, hm, Except.ok.injEq] at h
    exact hP a s h.symm) hub

/-- An mbarrier address register holding a 32-bit word: the object at `smLoc` when the address
is a multiple of 8. -/
theorem mbarLoc_bits {r : Nat} {off : Int} {x : BitVec 64} (hr : t.regs r = some (.bits 32 x))
    (h8 : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % 8 = 0) :
    mbarLoc L g t r off = .ok (smLoc L g x off) := by
  simp [mbarLoc, effAddr, sharedEffAddr, readReg, readBits, hr, h8, smLoc, bind, Except.bind,
    pure, Except.pure]

/-- `mbarLoc_bits` with the register read as `readReg`, the form `site_read` closes. -/
theorem mbarLoc_reg {r : Nat} {off : Int} {x : BitVec 64} (hr : readReg t r = .ok (.bits 32 x))
    (h8 : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % 8 = 0) :
    mbarLoc L g t r off = .ok (smLoc L g x off) := by
  have : t.regs r = some (.bits 32 x) := by
    unfold readReg at hr
    cases h : t.regs r with
    | none => simp [h, throw, throwThe, MonadExceptOf.throw] at hr
    | some v =>
      simp only [h, pure, Except.pure, Except.ok.injEq] at hr
      rw [hr]
  exact mbarLoc_bits this h8

/-- A sum of a multiple of 8 and an offset that is one, modulo `2 ^ 32`. -/
theorem trunc_add_mod8 {x : BitVec 64} {off : Int} (hx : x.toNat % 8 = 0) (ho : off % 8 = 0) :
    (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % 8 = 0 := by
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

end PTX.Flow
