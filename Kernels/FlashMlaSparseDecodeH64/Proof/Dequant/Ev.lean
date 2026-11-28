-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control.Machine
public import Lemmas.Flow.Step.SiteShape
public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Flow.UbFree

@[expose] public section

/-! # Warpgroup 2's events by state: the table

The event a state of warpgroup 2 fires is the event of its site (`Ev`): the `setmaxnreg`
(increase to 208), the two `.nc` length reads, the poll of `bar_q_utccp` with parity 0, per
block the polls of the slot's raw-ready barrier with the parity word and of its SV-done barrier
with the opposite parity word, the shared reads of the scale bytes (four 4-byte elements at
`%r2338 + 512 + 9216 r`) and the raw words (8 bytes at `%r2359 + 9216 r + 64 s`), the 32 chunk
stores of 16 bytes at the slot's dequantized buffer (`chunkW`: row `r`, step `s` at
`2048 r + 8192 s` above the thread's first chunk), the proxy fence, the arrivals (count 1, no
bytes) on the slot's dequant-ready and raw-free barriers, named barrier 12 of the whole CTA
(384 threads) and the exit. An address-reading event may instead fault (`ub`). The obligations
are `Shape*.lean`; `dq_open` (`ShapeBase.lean`) opens one site's obligation. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

/-- The shared words of the role's mbarriers (`%r2434`, and the loop's `%r2458`, `%r2461`,
`%r2783`, `%r2784` of the slot `b`). -/
abbrev qW (L : Launch) : BitVec 64 := addi (sbw L) 222784
abbrev rawW (L : Launch) (b : Bool) : BitVec 64 := addi (r2330W L b) 222808
abbrev svW (L : Launch) (b : Bool) : BitVec 64 := addi (r2330W L b) 222936
abbrev readyW (L : Launch) (b : Bool) : BitVec 64 := addi (r2330W L b) 222792
abbrev freeW (L : Launch) (b : Bool) : BitVec 64 := addi (r2330W L b) 222824
/-- The parity words of the raw-ready and SV-done polls (`%r2459`, `%r2462`) at parity `p`. -/
abbrev rawPar (p : Bool) : BitVec 64 := andi (zext16w (truncBits 16 (parB p))) 255
abbrev svPar (p : Bool) : BitVec 64 := andi (zext16w (xor16 (parB p))) 255
/-- The word of chunk `s` of row `r` (slot `b`): `%r2014`, and its 31 offsets `2048 r + 8192 s`
(`chunkOffs`). -/
def chunkW (L : Launch) (g : Nat) (b : Bool) (r : Fin 4) (s : Fin 8) : BitVec 64 :=
  if r.val = 0 ∧ s.val = 0 then r2014W L g b
  else addi (r2014W L g b) (Int.ofNat (2048 * r.val + 8192 * s.val))

/-- A poll of the word `x` with the parity of the word `q`, or undefined behaviour. -/
def PollEv (L : Launch) (g : Nat) (x q : BitVec 64) (e : Event) : Prop :=
  (∃ ok, e.kind = .wait (smLoc L g x 0) ((truncBits 32 q).toNat % 2) ok true .cta) ∨
    ∃ f, e.kind = .ub f

/-- The 32-bit word of the row's raw words (`%r2359` = `%r2338 + %r59`). -/
abbrev rawRowW (L : Launch) (g : Nat) (b : Bool) : BitVec 64 := add32 (r2338W L g b) (r59W L g)
/-- The offsets of row `r`'s scale vector (from `%r2338`) and of its raw word `s` (from
`%r2359`). -/
def scaleOff (r : Fin 4) : Int := 512 + 9216 * r.val
def rawOff (r : Fin 4) (s : Fin 8) : Int := 9216 * r.val + 64 * s.val

/-- A shared read of `n` bytes, element `j` of the access at the word `x` plus `off`, or undefined
behaviour. -/
def LoadEv (L : Launch) (g : Nat) (x : BitVec 64) (off : Int) (n j : Nat) (e : Event) : Prop :=
  (∃ a bs, e.kind = .rd a bs ∧ a.loc = (smLoc L g x off).at (n * j) ∧ a.size = n) ∨
    ∃ f, e.kind = .ub f

/-- A 16-byte write at the word `x`, or undefined behaviour. -/
def StoreEv (L : Launch) (g : Nat) (x : BitVec 64) (e : Event) : Prop :=
  (∃ a bs, e.kind = .wr a bs ∧ a.loc = smLoc L g x 0 ∧ a.size = 16) ∨ ∃ f, e.kind = .ub f

/-- The event kind of each site. -/
def EvK (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .smr => ∃ inst, e.kind = .setMaxReg true 208 inst
  | .lenA | .lenB => (∃ a bs, e.kind = .nc a bs) ∨ ∃ f, e.kind = .ub f
  | .wq => PollEv L g (qW L) (i32 0) e
  | .wraw => PollEv L g (rawW L d.sb) (rawPar d.pb) e
  | .wsv => PollEv L g (svW L d.sb) (svPar d.pb) e
  | .scale r => LoadEv L g (r2338W L g d.sb) (scaleOff r) 4 d.el e
  | .raw r s => LoadEv L g (rawRowW L g d.sb) (rawOff r s) 8 0 e
  | .store r s => StoreEv L g (chunkW L g d.sb r s) e
  | .fpx => e.kind = .fenceProxy (.async (some (.shared .cta))) none
  | .arrD => e.kind = .arrive (smLoc L g (readyW L d.sb) 0) 0 1 true .cta
  | .arrF => e.kind = .arrive (smLoc L g (freeW L d.sb) 0) 0 1 true .cta
  | .bar => e.kind = .bar 12 none .sync
  | .exit => e.kind = .exit

/-- **The event-shape table of warpgroup 2**: the site's pc and kind. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop := e.pc = d.site.pc ∧ EvK L g d e

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- A weak store of the first element through a 32-bit shared address register: a write at
the register's word of `w / 8` bytes, or undefined behaviour. -/
theorem fires_store_reg {t : TState} {w base pc : Nat} {srcs : List Opnd} {x : BitVec 64}
    {e : Event} {o : Option TState} (hr : t.regs base = some (.bits 32 x)) (hs : t.sub = 0)
    (hf : Fires pc (storeTmpl L g t .shared w base 0 srcs) e o) :
    (∃ a bs, e.kind = .wr a bs ∧ a.loc = smLoc L g x 0 ∧ a.size = w / 8) ∨
      ∃ f, e.kind = .ub f := by
  simp only [storeTmpl, effAddr_shared32 hr, hs, elemAcc, bind, Except.bind] at hf
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
        simp [smLoc, Loc.at]

/-- A weak shared load through a 32-bit address register: element `j` of the access at the
register's word plus the offset, or undefined behaviour. -/
theorem fires_load_ev {t : TState} {w base pc n j : Nat} {ds : List Nat} {off off' : Int}
    {x : BitVec 64} {e : Event} {o : Option TState} (hr : t.regs base = some (.bits 32 x))
    (hoff : off = off') (hw : w / 8 = n) (hj : t.sub = j)
    (hf : Fires pc (loadTmpl A L g t .shared false w ds base off) e o) :
    LoadEv L g x off' n j e := by
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

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
