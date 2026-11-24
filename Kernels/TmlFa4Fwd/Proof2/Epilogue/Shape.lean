-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Base
public import Lemmas.Flow.Ledger
public import Lemmas.Flow.Events
public import Lemmas.Flow.UbStop
public import Lemmas.Flow.ShflOps
public import Lemmas.Flow.Step.SiteShape

@[expose] public section

/-! # The output warp's events by state

The event a state of the output warp fires is the event of its site (`Ev`, `shape`): the
`setmaxnreg`, a read of global memory or undefined behaviour at a `word`, `q0` or `q1` site, a
shuffle or ballot at a scan site, a poll of stage `st`'s ready barrier with parity 0, a tensor
store of the stage or undefined behaviour, a bulk-group commit, a wait for the reads of all
but `1 - st` groups, an arrival of one unit on stage `st`'s free barrier, and the exit. Each
family of sites is proved by one call of `site_shape`. The machine stops exactly on a returned
value that is not a 32-bit word (`ret`, `stop_iff`, by `stop_cases`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- Stage `st`'s ready barrier (`sb + 208`, `sb + 216`) and free barrier (`sb + 224`,
`sb + 232`) of the thread's CTA. -/
def readyLoc (L : Launch) (g : Nat) (st : Fin 2) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + (208 + 8 * st.val)⟩
def freeLoc (L : Launch) (g : Nat) (st : Fin 2) : Loc :=
  ⟨.shared, g / L.block, L.sharedBase + (224 + 8 * st.val)⟩

/-- A tensor store, or undefined behaviour (which a store's template may fire, and which no
execution without undefined behaviour has). -/
def isStore (e : Event) : Bool :=
  match e.kind with | .tensorStore .. => true | .ub _ => true | _ => false

/-- A bulk-group commit; an arrival; a bulk-group read wait. -/
def isCommit (e : Event) : Bool := match e.kind with | .bulkCommit => true | _ => false
def isArrive (e : Event) : Bool := match e.kind with | .arrive .. => true | _ => false
def isWait (e : Event) : Bool := match e.kind with | .bulkWait .read _ => true | _ => false

/-- The bits of a value (`0` for a value of another kind). -/
def vbits : Value → BitVec 64
  | .bits _ x => x
  | _ => 0

/-- The partial sums of a state's scan: `0` the tile count, `5` the inclusive prefix. -/
def partialAt (L : Launch) (g : Nat) (d : D) (j : Nat) : BitVec 64 :=
  let lane := laneW L g
  let s1 := ps1 lane d.tl d.u1
  let s2 := psk lane s1 d.u2 1
  let s3 := psk lane s2 d.u4 3
  let s4 := psk lane s3 d.u8 7
  match j with
  | 0 => d.tl
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | 4 => s4
  | _ => psk lane s4 d.u16 15

/-- A ballot's predicate at a state: the lane's prefix of work is at most the CTA's tile. -/
def votePred (p : Params) (L : Launch) (g : Nat) (d : D) : Bool :=
  scmp .le .s (mad32 (prefixD L g d) (headsW p) (sub32 d.cur (mul32 d.tot (headsW p))))
    (ctaW L g)

/-- The address a read site reads: the lane's request, the loop round's, or the chosen request's
two offsets. -/
def rdAddr (p : Params) (L : Launch) (g : Nat) (d : D) : BitVec 64 :=
  match d.site with
  | .word .first | .word .second =>
    truncBits 64 (vbits (addrU p.cuQBase (laneW L g))) + BitVec.ofInt 64 0
  | .word _ => truncBits 64 (vbits (addrS p.cuQBase (reqOf L g d.grp))) + BitVec.ofInt 64 0
  | .q0 => truncBits 64 (vbits (addrS p.cuQBase (chosen d))) + BitVec.ofInt 64 0
  | .q1 => truncBits 64 (vbits (addrS p.cuQBase (chosen d))) + BitVec.ofInt 64 4
  | _ => 0

/-- The footprint of a read of the 32-bit word at global address `n`. -/
def wordAcc (n : Nat) : Acc := { loc := globalLoc n, size := 4 }

/-- A full-mask ballot or mode vote, as `MaskK voteClass` counts them. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof2.isFullVote (e : Event) : Bool :=
  (voteClass e.kind).any (·.mask == 2 ^ 32 - 1)

theorem any_mask (m : Nat) (q : VoteMode) (a : Bool) :
    (some (⟨m, q, a⟩ : WarpPart VoteMode Bool)).any (·.mask == m) = true := by
  rw [Option.any_some]; exact beq_self_eq_true m

theorem isFullVote_vote (pc : Nat) (a : Bool) (b : BitVec 32) :
    isFullVote ⟨pc, .vote (2 ^ 32 - 1) a b⟩ = true := by
  unfold isFullVote
  rw [show voteClass (Kind.vote (2 ^ 32 - 1) a b) = some ⟨2 ^ 32 - 1, .ballot, a⟩ from rfl]
  exact any_mask _ _ _

/-- The sites of a shuffle; of a ballot. -/
def Site.shfl : Site → Bool
  | .down _ | .up _ _ | .total _ | .pre _ | .tiles _ => true
  | _ => false
def Site.ballot : Site → Bool
  | .vote _ => true
  | _ => false

/-- The event-shape table of the output warp. -/
def Ev (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .start => ∃ inc n inst, e.kind = .setMaxReg inc n inst
  | .word _ | .q0 | .q1 =>
      (∃ bs, e.kind = .rd (wordAcc (rdAddr p L g d).toNat) bs) ∨ ∃ f, e.kind = .ub f
  | .down _ => ∃ recv ok, e.kind = .shfl .down (.bits 32 d.w) 1 31 recv ok
  | .up _ j => ∃ recv ok,
      e.kind = .shfl .up (.bits 32 (partialAt L g d j.val)) (2 ^ j.val) 0 recv ok
  | .total _ => ∃ recv ok, e.kind = .shfl .idx (.bits 32 (prefixD L g d)) 31 31 recv ok
  | .vote _ => ∃ b, e.kind = .vote (2 ^ 32 - 1) (votePred p L g d) b
  | .pre _ => ∃ recv ok,
      e.kind = .shfl .idx (.bits 32 (prefixD L g d)) (truncBits 32 (addi (popc d.bal) (-1))).toNat
        31 recv ok
  | .tiles _ => ∃ recv ok,
      e.kind = .shfl .idx (.bits 32 d.tl) (truncBits 32 (popc d.bal)).toNat 31 recv ok
  | .ready st => ∃ ok, e.kind = .wait (readyLoc L g st) 0 ok true .cta
  | .store _ _ => isStore e = true
  | .commit _ => e.kind = .bulkCommit
  | .drain st => e.kind = .bulkWait .read (if st = 0 then 1 else 0)
  | .free st => e.kind = .arrive (freeLoc L g st) 0 1 true .cta
  | .exit _ => e.kind = .exit

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

theorem sb_add (hp : Pre p L m) {k : Nat} (hk : k < 1024) :
    addi (BitVec.ofNat 64 L.sharedBase) k = BitVec.ofNat 64 (L.sharedBase + k) := by
  have hs := hp.shared.2.1
  apply BitVec.eq_of_toNat_eq
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  have h1 : ((k : Int) % ((2 ^ 64 : Nat) : Int)).toNat = k := by omega
  rw [h1]
  have : L.sharedBase + k < 2 ^ 32 := by omega
  simp only [Nat.mod_eq_of_lt (show L.sharedBase < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show L.sharedBase < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show L.sharedBase + k < 2 ^ 64 by omega), Nat.mod_eq_of_lt this]

theorem sb_addi (hp : Pre p L m) {k : Int} (h0 : 0 ≤ k) (hk : k < 1024) :
    addi (BitVec.ofNat 64 L.sharedBase) k = BitVec.ofNat 64 (L.sharedBase + k.toNat) := by
  have := sb_add hp (k := k.toNat) (by omega)
  rwa [Int.toNat_of_nonneg h0] at this

/-- An mbarrier address `sb + k` in a register, plus an offset. -/
theorem loc_off (hp : Pre p L m) {t : TState} {r k : Nat} {off : Int} (h0 : 0 ≤ off)
    (hk : k + off.toNat < 1024) (h8 : (L.sharedBase + (k + off.toNat)) % 8 = 0)
    (hr : t.regs r = some (b32 (L.sharedBase + k))) :
    mbarLoc L g t r off = .ok ⟨.shared, g / L.block, L.sharedBase + (k + off.toNat)⟩ := by
  have hs := hp.shared.2.1
  have hv : (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + k)) +
      BitVec.ofInt 64 off)).toNat = L.sharedBase + (k + off.toNat) := by
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
    omega
  simp only [mbarLoc, effAddr, sharedEffAddr, readReg, hr, b32, readBits, hv, h8,
    bind, Except.bind, pure, Except.pure, ↓reduceIte]

/-- A register's value at an address site, as `loc_off` reads it. -/
macro "ep_val" : tactic => `(tactic| (
  simp only [valueOf, values, valuesWrite, valuesStart, lookupLit, Option.getD_some,
    Option.getD_none]
  try rw [sb_addi ‹Pre _ _ _› (by decide) (by decide)]
  try rfl))

/-- The role's side conditions of `site_shape`: the CTA size, and the mbarrier addresses. -/
macro "ep_addr" : tactic => `(tactic| first
  | rw [‹Pre _ _ _›.block]
  | (apply loc_off ‹Pre _ _ _› (by decide)
     case hr => exact (PTX.Flow.regs_of_factsFrom ‹_› (by lit_mem)).trans (by ep_val)
     case hk => omega
     case h8 => have := ‹Pre _ _ _›.shared; omega)
  | (apply loc_off (k := 0) ‹Pre _ _ _› (by decide)
     case hr => exact (PTX.Flow.regs_of_factsFrom ‹_› (by lit_mem)).trans (by ep_val)
     case hk => omega
     case h8 => have := ‹Pre _ _ _›.shared; omega))

set_option hygiene false in
/-- The shape obligations of the sites of `s` that the theorem's `hs` admits. -/
macro "ep_shape" : tactic => `(tactic|
  site_shape s skip_by (simp at hs)
    unfolding [Ev, rdAddr, vbits]
    reg_vals [valueOf, values, valuesScan, valuesSelect, valuesSelect2, valuesWrite, valuesStart,
      partials, loopRegs, lanePreds, lookupLit]
    addr_by (ep_addr))

theorem shapeAt_scan (hp : Pre p L m) (d : D)
    (hs : (∃ k, d.site = .down k) ∨ (∃ k j, d.site = .up k j) ∨ ∃ k, d.site = .total k) :
    (code p L g ent).ShapeAt (Ev p L g) d := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  ep_shape

theorem shapeAt_select (hp : Pre p L m) (d : D)
    (hs : (∃ l, d.site = .vote l) ∨ (∃ l, d.site = .pre l) ∨ ∃ l, d.site = .tiles l) :
    (code p L g ent).ShapeAt (Ev p L g) d := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  ep_shape

theorem shapeAt_read (d : D)
    (hs : (∃ k, d.site = .word k) ∨ d.site = .q0 ∨ d.site = .q1) :
    (code p L g ent).ShapeAt (Ev p L g) d := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  ep_shape

theorem shapeAt_write (hp : Pre p L m) (d : D)
    (hs : (∃ st, d.site = .ready st) ∨ (∃ st b, d.site = .store st b) ∨
      (∃ st, d.site = .commit st) ∨ (∃ st, d.site = .drain st) ∨ (∃ st, d.site = .free st)) :
    (code p L g ent).ShapeAt (Ev p L g) d := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  ep_shape

theorem shapeAt_ends (d : D) (hs : d.site = .start ∨ ∃ l, d.site = .exit l) :
    (code p L g ent).ShapeAt (Ev p L g) d := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  ep_shape

set_option linter.unusedTactic false in
/-- **The event a state of the output warp fires is the event of its site.** -/
theorem shape (hp : Pre p L m) : (code p L g ent).Shape (Ev p L g) := by
  have h : ∀ d, (code p L g ent).ShapeAt (Ev p L g) d := by
    intro d
    cases hs : d.site <;> first
      | (refine @shapeAt_scan p L m g ent hp d ?_; simp [hs]; done)
      | (refine @shapeAt_select p L m g ent hp d ?_; simp [hs]; done)
      | (refine @shapeAt_read p L g ent d ?_; simp [hs]; done)
      | (refine @shapeAt_write p L m g ent hp d ?_; simp [hs]; done)
      | (refine @shapeAt_ends p L g ent d ?_; simp [hs]; done)
  exact @Code.Shape.of_at _ _ _ _ (code p L g ent) (Ev p L g) h

/-- The kind of value each site returns: a 32-bit word at a load or shuffle. -/
def ret (d : D) : RetKind :=
  match d.site with
  | .word _ | .q0 | .q1 | .down _ | .up _ _ | .total _ | .pre _ | .tiles _ => .word 32
  | _ => .none

/-- **The machine stops exactly on a returned value that is not a 32-bit word.** -/
theorem stop_iff (d : D) : ∀ {e : Event}, (code p L g ent).inv d → Ev p L g d e →
    ((code p L g ent).next d e = some none ↔ ¬ (ret d).accepts e) := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  stop_cases s unfolding [Ev]
    trans [ret, succ, word32, afterTotal, afterTiles, loopHead, scanExit, storeNext]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue
