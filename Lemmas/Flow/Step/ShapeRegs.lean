-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Ledger
public import Lemmas.Flow.Events
public import Lemmas.Flow.ShflOps
public import Lemmas.Flow.Next
public import Lemmas.Flow.Resource

@[expose] public section

/-! # Event shapes from register values

A proof tool (promoted from the tml-fa4 MMA warp's proof). Inversion lemmas for shape tables
by hand, beside the per-class lemmas of `site_shape` (`Step/SiteShape.lean`). Each states the
event an instruction fires from the values of its operand registers alone, so that a role's shape
proof reads the registers off its value table. Nothing here is specific to a kernel.

* `smLoc L g x off`: the shared location of a 32-bit address register holding `x` plus `off`.
* `fires_wait_reg`, `fires_commit_reg`: a poll and a Tensor Core commit name the object at their
  address register (or fault on a misaligned one).
* `fires_shfl_reg`, `fires_vote_reg`, `fires_load_reg`: a shuffle, a full-mask ballot, a global
  32-bit load.
* `fires_load_kind`, `fires_tcMma_kind`, `fires_elect_kind`, `fires_barImm`,
  `fires_tcResource_kind`: the kind of the event of a load, an MMA, an election, a `bar.sync` with
  immediate operands, and an allocation-permit or deallocation instruction. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.EventFrame

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- The shared location of the thread's CTA at a 32-bit register holding `x`, plus `off`. -/
def smLoc (L : Launch) (g : Nat) (x : BitVec 64) (off : Int) : Loc :=
  ⟨.shared, g / L.block, (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat⟩

/-- **A poll names the object at its address register, or faults on a misaligned one** (at a
site where no assumption widens the scope): a role that knows its barrier address is 8-byte
aligned learns that the poll fires a wait. -/
theorem fires_wait_reg_al {t : TState} {p base par : Nat} {off : Int} {acq : Bool}
    {sc : MbarScope} {pc : Nat} {e : Event} {o : Option TState} {x q : BitVec 64} {wx wq : Nat}
    (hA : A.any (·.clusterScopeMbar t.pc) = false)
    (hb : t.regs base = some (.bits wx x)) (hq : t.regs par = some (.bits wq q))
    (hf : Fires pc (eventTmpl A L g t (.mbarWait p base off (.reg par) acq sc)) e o) :
    (∃ ok, e.kind = .wait (smLoc L g x off) ((truncBits 32 q).toNat % 2) ok acq sc) ∨
      ∃ f, e.kind = .ub f ∧ (smLoc L g x off).addr % 8 ≠ 0 := by
  simp only [eventTmpl, widenMbarScope, hA, Bool.false_eq_true, ↓reduceIte, tmaTmpl, mbarLoc,
    effAddr, sharedEffAddr, readReg, hb, hq, readBits, bind, Except.bind, pure, Except.pure,
    ofExec] at hf
  split_ifs at hf with h
  · simp only [Fires] at hf
    obtain ⟨ok, hk, -⟩ := hf
    exact .inl ⟨ok, by rw [hk]; rfl⟩
  · simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1, h⟩

/-- A poll at a site where no assumption widens the scope names the object at its address
register and the parity bit of its parity register, or faults (a misaligned address). -/
theorem fires_wait_reg {t : TState} {p base par : Nat} {off : Int} {acq : Bool} {sc : MbarScope}
    {pc : Nat} {e : Event} {o : Option TState} {x q : BitVec 64} {wx wq : Nat}
    (hA : A.any (·.clusterScopeMbar t.pc) = false)
    (hb : t.regs base = some (.bits wx x)) (hq : t.regs par = some (.bits wq q))
    (hf : Fires pc (eventTmpl A L g t (.mbarWait p base off (.reg par) acq sc)) e o) :
    (∃ ok, e.kind = .wait (smLoc L g x off) ((truncBits 32 q).toNat % 2) ok acq sc) ∨
      ∃ f, e.kind = .ub f :=
  (fires_wait_reg_al hA hb hq hf).imp id fun ⟨f, hf, _⟩ => ⟨f, hf⟩

/-- A Tensor Core commit without a mask names the object at its address register, or faults. -/
theorem fires_commit_reg {t : TState} {group : CtaGroup} {base : Nat} {off : Int} {pc : Nat}
    {e : Event} {o : Option TState} {x : BitVec 64} {wx : Nat}
    (hb : t.regs base = some (.bits wx x))
    (hf : Fires pc (eventTmpl A L g t (.tcCommit group base off none)) e o) :
    (∃ s, e.kind = .tc (.commit s) ∧ s.mbar = smLoc L g x off ∧ s.group = group) ∨
      ∃ f, e.kind = .ub f := by
  simp only [eventTmpl, tcCommitTmpl, mbarClusterLoc, sharedEffAddr, readReg, hb, readBits,
    bind, Except.bind, pure, Except.pure] at hf
  split_ifs at hf
  · cases hs : TcCommit.resolve L group (g / L.block) (smLoc L g x off)
      (BitVec.ofNat 16 (2 ^ L.rankOfCta (smLoc L g x off).cta)) with
    | none =>
      simp only [smLoc] at hs
      simp only [hs, ofExec, throw, throwThe, MonadExceptOf.throw, Fires] at hf
      exact .inr ⟨_, congrArg Event.kind hf.1⟩
    | some s =>
      have hs' := hs
      simp only [smLoc] at hs
      simp only [hs, ofExec, Fires] at hf
      refine .inl ⟨s, by rw [hf.1], ?_⟩
      simp only [TcCommit.resolve] at hs'
      split_ifs at hs'
      cases hs'
      exact ⟨rfl, rfl⟩
  all_goals
    simp only [ofExec, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩

/-- A full-mask shuffle of a 32-bit word register. -/
theorem fires_shfl_reg {t : TState} {mode : ShflMode} {dst ar : Nat} {b c : Opnd} {pc : Nat}
    {e : Event} {o : Option TState} {x bv cv : BitVec 64} (hblk : L.block % 32 = 0)
    (hr : t.regs ar = some (.bits 32 x))
    (hb : readBits L g t 32 b = .ok bv) (hc : readBits L g t 32 c = .ok cv)
    (hf : Fires pc (eventTmpl A L g t
      (.warp ⟨.shfl mode, some (.int .b 32), [some dst], [.reg ar, b, c], some (.imm (-1))⟩))
      e o) :
    ∃ recv ok, e.kind = .shfl mode (.bits 32 x) bv.toNat cv.toNat recv ok := by
  change Fires _ (shflTmpl L g t mode dst none (.reg ar) b c (.imm (-1))) e o at hf
  obtain ⟨recv, ok, he⟩ := fires_shflTmpl (m := truncBits 32 (BitVec.ofInt 64 (-1)))
    (av := .bits 32 x) rfl (by simp [readValue, readReg, hr, pure, Except.pure]) hb hc
    (by decide) hblk rfl hf
  exact ⟨recv, ok, by rw [he]⟩

/-- A full-mask ballot of a predicate register. -/
theorem fires_vote_reg {t : TState} {dst a : Nat} {b : Bool} {pc : Nat} {e : Event}
    {o : Option TState} (hblk : L.block % 32 = 0) (hr : t.regs a = some (.pred b))
    (hf : Fires pc (eventTmpl A L g t
      (.warp ⟨.vote .ballot false, some (.int .b 32), [some dst], [.reg a], some (.imm (-1))⟩))
      e o) :
    ∃ bal, e.kind = .vote (2 ^ 32 - 1) b bal := by
  change Fires _ (voteTmpl L g t dst a false (.imm (-1))) e o at hf
  obtain ⟨bal, he⟩ := fires_voteTmpl (m := truncBits 32 (BitVec.ofInt 64 (-1))) (pv := b) rfl
    (by simp [readPred, readReg, hr, bind, Except.bind, pure, Except.pure]) (by decide) hblk hf
  exact ⟨bal, by rw [he]; simp⟩

/-- The footprint of a read of the 32-bit word at global address `n`. -/
def wordAcc (n : Nat) : Acc := { loc := ⟨.global, 0, n⟩, size := 4 }

/-- A global 32-bit load from a 64-bit address register reads the word at the address plus the
offset, or faults. -/
theorem fires_load_reg {t : TState} {dst base : Nat} {off : Int} {pc : Nat} {e : Event}
    {o : Option TState} {x : BitVec 64} (hs : t.sub = 0) (hr : t.regs base = some (.bits 64 x))
    (hf : Fires pc (loadTmpl A L g t .global false 32 [dst] base off) e o) :
    (∃ bs, e.kind = .rd (wordAcc (truncBits 64 x + BitVec.ofInt 64 off).toNat) bs) ∨
      ∃ f, e.kind = .ub f := by
  simp only [loadTmpl, effAddr, readBits, readReg, hr, bind, Except.bind, pure, Except.pure,
    elemAcc, hs, Bool.false_eq_true, ↓reduceIte] at hf
  split_ifs at hf
  all_goals first
    | (right
       simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
       exact ⟨_, congrArg Event.kind hf.1⟩)
    | (left
       simp only [Fires] at hf
       obtain ⟨bs, -, he, -⟩ := hf
       refine ⟨bs, ?_⟩
       rw [congrArg Event.kind he]
       simp [Loc.at, wordAcc])

/-- A load reads, or faults. -/
theorem fires_load_kind {t : TState} {sp : Space} {w : Nat} {ds : List Nat} {base : Nat}
    {off : Int} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (loadTmpl A L g t sp false w ds base off) e o) :
    (∃ a bs, e.kind = .rd a bs) ∨ ∃ f, e.kind = .ub f := by
  simp only [loadTmpl, Bool.false_eq_true, ↓reduceIte] at hf
  split at hf
  · simp only [Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · simp only [Fires] at hf
    obtain ⟨bs, -, he, -⟩ := hf
    exact .inl ⟨_, bs, congrArg Event.kind he⟩

/-- A template that fires a Tensor Core operation or faults. -/
def TcOrUb : Tmpl → Prop
  | .tc (.mma ..) _ => True
  | .ub _ => True
  | _ => False

theorem ofExec_tcOrUb {r : Exec Tmpl} (h : AllOk TcOrUb r) : TcOrUb (ofExec r) := by
  cases r with
  | error => trivial
  | ok m => exact h

/-- An MMA instruction fires an MMA, or faults. -/
theorem fires_tcMma_kind {t : TState} {m : TcMmaInstr} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.tcMma m)) e o) :
    (∃ d s acc ms, e.kind = .tc (.mma d s acc ms)) ∨ ∃ f, e.kind = .ub f := by
  have hm : TcOrUb (eventTmpl A L g t (.tcMma m)) := by
    simp only [eventTmpl, tcTmpl, mmaTmpl]
    split
    · simp only [mmaSmemTmpl]
      apply ofExec_tcOrUb
      repeat' first
        | (apply allOk_bind; intro _)
        | split
        | exact trivial
    · simp only [mmaTmemTmpl]
      apply ofExec_tcOrUb
      repeat' first
        | (apply allOk_bind; intro _)
        | split
        | exact trivial
    · trivial
  generalize eventTmpl A L g t (.tcMma m) = tm at hm hf
  cases tm <;> simp only [TcOrUb] at hm
  case tc k u =>
    cases k <;> simp only at hm
    simp only [Fires] at hf
    exact .inl ⟨_, _, _, _, congrArg Event.kind hf.1⟩
  case ub f =>
    simp only [Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩

/-- An election fires an election. -/
theorem fires_elect_kind {t : TState} {dst : Option Nat} {p : Nat} {mask : Opnd} {ty : Option DType}
    {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.elect, ty, [dst, some p], [], some mask⟩)) e o) :
    (∃ mk inst ld, e.kind = .elect mk inst ld) ∨ ∃ f, e.kind = .ub f := by
  simp only [eventTmpl, warpTmpl_elect, electTmpl] at hf
  split at hf
  · simp only [Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · split_ifs at hf
    · simp only [Fires] at hf
      obtain ⟨inst, ld, h, -⟩ := hf
      exact .inl ⟨_, _, _, congrArg Event.kind h⟩
    · simp only [Fires] at hf
      exact .inr ⟨_, congrArg Event.kind hf.1⟩

/-- A `bar.sync id, n` with immediate operands, `id < 16`, `n` a multiple of 32 other than zero and
the block size, arrives on `id` with count `n`. -/
theorem fires_barImm {t : TState} {id n : Nat} {al : Bool} {pc : Nat} {e : Event}
    {o : Option TState} (hid : id < 16) (hn : n < 2 ^ 31) (hn32 : n % 32 = 0) (hn0 : n ≠ 0)
    (hnb : n ≠ L.block)
    (hf : Fires pc (eventTmpl A L g t (.barSyncN (.imm id) (.imm n) al)) e o) :
    e.kind = .bar id (some n) .sync := by
  have hi : (truncBits 32 (BitVec.ofInt 64 (id : Int))).toNat = id := by
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  have hn' : (truncBits 32 (BitVec.ofInt 64 (n : Int))).toNat = n := by
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  simp only [eventTmpl, barTmpl, readBits, pure, Except.pure, hi, hn',
    show ¬ 16 ≤ id by omega, ↓reduceIte, hn32, hn0, hnb, or_self, true_and] at hf
  simp only [Fires] at hf
  exact congrArg Event.kind hf.1

/-- An allocation-permit or deallocation instruction fires its resource operation, or faults. -/
theorem fires_tcResource_kind {t : TState} {op : Op} {group : CtaGroup}
    (hm : ∀ {A : List Assumption},
    TmemTmpl group (eventTmpl A L g t op)) {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t op) e o) :
    (∃ dst act, e.kind = .tc (.resource group dst act)) ∨ ∃ f, e.kind = .ub f := by
  rcases fires_tmemTmpl hm hf with ⟨f, rfl⟩ | ⟨dst, act, rfl⟩
  · exact .inr ⟨f, rfl⟩
  · exact .inl ⟨dst, act, rfl⟩

end
end PTX.Flow
