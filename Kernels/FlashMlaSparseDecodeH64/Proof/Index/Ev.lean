-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Mod8
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Flow.Step.ShapeAsync
public import Lemmas.Flow.UbFree

@[expose] public section

/-! # The index warp's events by state: the table

The event a state of the index warp fires is the event of its site (`Ev`): the `.nc` loads of
the two lengths and of the index pairs (an element `el` of a pair at its address register's
word: `ixAddr0`, `ixAddr1` for the first pairs, the table's `aptr` and `ixXad xa` for the next
ones), per block the poll of `valid_coord_free[slot]`
(`freeW`) with the parity word of the ring's parity (`ixParW`), the two butterfly shuffles, the
two elements of the lane's coordinate pair at `pairW + 221728 + 4 el` (`pairW`: the lane's row
`8 lane` of slot `slot` at `256 slot` above the shared base), the validity byte of lanes
`0 mod 4` at `byteW + 221696` (`byteW`: the slot's 8 bytes, byte `lane / 4`), the arrival
(count 1, no bytes) on `valid_coord_ready[slot]` (`readyW`), named barrier 12 of the whole CTA
(384 threads, so the event names no count) and the exit. An address- or data-reading event may
instead fault (`ub`). The obligations are `Shape.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- The shared words of the slot's mbarriers (`%r585`/`%r623`, `%r614`/`%r653`) and of the
stores (`%r612`/`%r651`, `%r613`/`%r652`). -/
abbrev freeW (L : Launch) (c : IxCtl) : BitVec 64 := addi (ixSlotB L c.slot) 222872
abbrev readyW (L : Launch) (c : IxCtl) : BitVec 64 := addi (ixSlotB L c.slot) 222840
abbrev pairW (L : Launch) (g : Nat) (c : IxCtl) : BitVec 64 :=
  add32 (ixRowB L g) (shl (ixSlotW c.slot) 8)
abbrev byteW (L : Launch) (g : Nat) (c : IxCtl) : BitVec 64 :=
  add32 (ixSlotB L c.slot) (shru (ixLane L g) 2)

/-- A `.nc` load, or undefined behaviour. -/
def NcEv (e : Event) : Prop := (∃ a bs, e.kind = .nc a bs) ∨ ∃ f, e.kind = .ub f

/-- A `.nc` read of element `el` (4 bytes) of the access at the global word `x`, or undefined
behaviour. -/
def NcAt (x : BitVec 64) (el : Nat) (e : Event) : Prop :=
  (∃ a bs, e.kind = .nc a bs ∧
    a.loc = (⟨.global, 0, (truncBits 64 x + BitVec.ofInt 64 0).toNat⟩ : Loc).at (4 * el) ∧
      a.size = 4) ∨ ∃ f, e.kind = .ub f

attribute [simp] NcAt

/-- A poll of the word `x` with the parity of the word `q`, or undefined behaviour. -/
def PollEv (L : Launch) (g : Nat) (x q : BitVec 64) (e : Event) : Prop :=
  (∃ ok, e.kind = .wait (smLoc L g x 0) ((truncBits 32 q).toNat % 2) ok true .cta) ∨
    ∃ f, e.kind = .ub f

/-- A butterfly shuffle, or undefined behaviour. -/
def ShflEv (e : Event) : Prop :=
  (∃ a b c r ok, e.kind = .shfl .bfly a b c r ok) ∨ ∃ f, e.kind = .ub f

/-- An `n`-byte write at `j` bytes above the word `x` plus `off`, or undefined behaviour. -/
def StoreEv (L : Launch) (g : Nat) (x : BitVec 64) (off : Int) (j n : Nat) (e : Event) : Prop :=
  (∃ a bs, e.kind = .wr a bs ∧ a.loc = (smLoc L g x off).at j ∧ a.size = n) ∨ ∃ f, e.kind = .ub f

/-- The event kind of each site. -/
def EvK (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .lenA | .lenB => NcEv e
  | .pre => NcAt (ixAddr0 P L g) d.el e
  | .pf => NcAt d.c.aptr d.el e
  | .xpre => NcAt (ixAddr1 P L g) d.el e
  | .xpf => NcAt (ixXad P L g d.c.xa) d.el e
  | .wA | .wB => PollEv L g (freeW L d.c) (ixParW d.c.par) e
  | .sA1 | .sA2 | .sB1 | .sB2 => ShflEv e
  | .stA | .stB => StoreEv L g (pairW L g d.c) 221728 (4 * d.el) 4 e
  | .bA | .bB => StoreEv L g (byteW L g d.c) 221696 0 1 e
  | .arrA | .arrB => e.kind = .arrive (smLoc L g (readyW L d.c) 0) 0 1 true .cta
  | .bar => e.kind = .bar 12 none .sync
  | .exit => e.kind = .exit

/-- **The event-shape table of the index warp**: the site's pc and kind. -/
def Ev (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  e.pc = d.site.pc ∧ EvK P L g d e

/-- The parity bit of a wait: the opposite of the ring's parity. -/
theorem parW_bit (p : Bool) : (truncBits 32 (ixParW p)).toNat % 2 = if p then 0 else 1 := by
  cases p <;> decide

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- A weak store through a 32-bit shared address register: a write at the register's word plus
the offset, `w / 8 * t.sub` bytes above, of `w / 8` bytes, or undefined behaviour. -/
theorem fires_store_el {t : TState} {w base pc : Nat} {off : Int} {srcs : List Opnd}
    {x : BitVec 64} {e : Event} {o : Option TState} (hr : t.regs base = some (.bits 32 x))
    (hf : Fires pc (storeTmpl L g t .shared w base off srcs) e o) :
    (∃ a bs, e.kind = .wr a bs ∧ a.loc = (smLoc L g x off).at (w / 8 * t.sub) ∧
      a.size = w / 8) ∨ ∃ f, e.kind = .ub f := by
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
        exact .inl ⟨_, _, congrArg Event.kind hf.1, rfl, rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
