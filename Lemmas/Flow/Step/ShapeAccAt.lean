-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Flow.UbFree

@[expose] public section

/-! # Event shapes of weak loads and stores with their exact footprints

A proof tool. A role whose address registers are in its value table states each access's
location and width in its shape table: element `j` of a weak access of `n`-byte elements at the
register's word plus the instruction's offset (`smLoc` for a 32-bit shared address, the 64-bit
word for a global one), or undefined behaviour (a misaligned address, a value without bits).

* `RdAt L g x off n j e`, `WrAt L g x off n j e`: the shared read and write classes;
* `GWrAt x n e`: a global write of `n` bytes at the word `x`;
* `fires_rd_at`, `fires_wr_at`, `fires_gwr_at`: the inversion lemmas of `loadTmpl` and
  `storeTmpl` from the address register's value. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- Element `j` of a shared read of `n`-byte elements at the word `x` plus `off`, or undefined
behaviour. -/
def RdAt (L : Launch) (g : Nat) (x : BitVec 64) (off : Int) (n j : Nat) (e : Event) : Prop :=
  (∃ a bs, e.kind = .rd a bs ∧ a.loc = (smLoc L g x off).at (n * j) ∧ a.size = n) ∨
    ∃ f, e.kind = .ub f

/-- Element `j` of a shared write of `n`-byte elements at the word `x` plus `off`, or undefined
behaviour. -/
def WrAt (L : Launch) (g : Nat) (x : BitVec 64) (off : Int) (n j : Nat) (e : Event) : Prop :=
  (∃ a bs, e.kind = .wr a bs ∧ a.loc = (smLoc L g x off).at (n * j) ∧ a.size = n) ∨
    ∃ f, e.kind = .ub f

/-- A global write of `n` bytes at the 64-bit word `x`, or undefined behaviour. -/
def GWrAt (x : BitVec 64) (n : Nat) (e : Event) : Prop :=
  (∃ a bs, e.kind = .wr a bs ∧ a.loc = ⟨.global, 0, x.toNat⟩ ∧ a.size = n) ∨
    ∃ f, e.kind = .ub f

/-- **A weak shared load through a 32-bit address register**: element `j` at the register's word
plus the offset. -/
theorem fires_rd_at {t : TState} {w base pc n j : Nat} {ds : List Nat} {off off' : Int}
    {x : BitVec 64} {e : Event} {o : Option TState} (hr : t.regs base = some (.bits 32 x))
    (hoff : off = off') (hw : w / 8 = n) (hj : t.sub = j)
    (hf : Fires pc (loadTmpl A L g t .shared false w ds base off) e o) :
    RdAt L g x off' n j e := by
  subst hoff hw hj
  simp only [loadTmpl, effAddr_shared32 hr, elemAcc, bind, Except.bind, Bool.false_eq_true,
    ↓reduceIte] at hf
  by_cases hm : w / 8 = 0 ∨
      (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % (w / 8 * ds.length) ≠ 0
  · simp only [hm, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · simp only [hm, ↓reduceIte, pure, Except.pure, Fires] at hf
    obtain ⟨bs, -, he, -⟩ := hf
    exact .inl ⟨_, bs, congrArg Event.kind he, by simp [smLoc], rfl⟩

/-- **A weak shared store through a 32-bit address register**: element `j` at the register's
word plus the offset. -/
theorem fires_wr_at {t : TState} {w base pc n j : Nat} {srcs : List Opnd} {off off' : Int}
    {x : BitVec 64} {e : Event} {o : Option TState} (hr : t.regs base = some (.bits 32 x))
    (hoff : off = off') (hw : w / 8 = n) (hj : t.sub = j)
    (hf : Fires pc (storeTmpl L g t .shared w base off srcs) e o) :
    WrAt L g x off' n j e := by
  subst hoff hw hj
  simp only [storeTmpl, effAddr_shared32 hr, elemAcc, bind, Except.bind] at hf
  split_ifs at hf
  · simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · simp only [pure, Except.pure] at hf
    split at hf
    · simp only [Fires] at hf
      exact .inr ⟨_, congrArg Event.kind hf.1⟩
    · split at hf
      · simp only [Fires] at hf
        exact .inr ⟨_, congrArg Event.kind hf.1⟩
      · simp only [Fires] at hf
        exact .inl ⟨_, _, congrArg Event.kind hf.1, by simp [smLoc], rfl⟩

/-- **A weak global store of one element through a 64-bit address register** holding `x`. -/
theorem fires_gwr_at {t : TState} {w base pc n : Nat} {srcs : List Opnd}
    {x : BitVec 64} {e : Event} {o : Option TState} (hr : t.regs base = some (.bits 64 x))
    (hw : w / 8 = n) (hj : t.sub = 0)
    (hf : Fires pc (storeTmpl L g t .global w base 0 srcs) e o) : GWrAt x n e := by
  subst hw
  simp only [storeTmpl, effAddr_global_bits hr, elemAcc, bind, Except.bind] at hf
  split_ifs at hf
  · simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · simp only [pure, Except.pure] at hf
    split at hf
    · simp only [Fires] at hf
      exact .inr ⟨_, congrArg Event.kind hf.1⟩
    · split at hf
      · simp only [Fires] at hf
        exact .inr ⟨_, congrArg Event.kind hf.1⟩
      · simp only [Fires] at hf
        refine .inl ⟨_, _, congrArg Event.kind hf.1, ?_, rfl⟩
        simpa [Loc.at, hj, truncBits] using x.isLt

end
end PTX.Flow
