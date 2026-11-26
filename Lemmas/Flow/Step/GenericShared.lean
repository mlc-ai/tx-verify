-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Havoc
public import Lemmas.Flow.Local
public import Lemmas.Flow.Step.ShapeRegs

@[expose] public section

/-! # Generic shared pointers: forming them and storing through them

A proof tool for a role that forms a generic pointer to its CTA's shared memory (`cvta.shared`,
pointer additions) and stores through it with a generic `st` (no state space):

* `SegU.set_live`: one local step that writes one register with its table value, between two
  liveness-filtered fact lists, or kills the thread;
* `exec_cvtaShared_or`: `cvta.shared` of a 64-bit word below `2 ^ 32` is the generic shared
  pointer of the thread's CTA at that byte, or (the thread or its CTA outside the launch) faults;
* `GenWrAt`, `fires_gen_wr_at`: element `j` of a weak generic store of `n`-byte elements through a
  generic shared pointer at byte `x` writes at byte `x + off + n j` of the thread's CTA, or is
  undefined behaviour;
* `fires_sym_rd_at`: a weak load at a shared variable's address reads at the variable's byte plus
  the offset. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **One local step writing the table value of `d`**, between the facts of two liveness lists
of one value table: every register live after the step was live before it or is `d`. A failing
step kills the thread. -/
theorem SegU.set_live {live : Nat → List Nat} {val : Nat → Value} {pc d : Nat} {op : Op}
    (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true) (hd : d ∉ live pc)
    (hlive : ∀ x ∈ live (pc + 1), x ∈ d :: live pc)
    (hex : ∀ t, At t pc (factsFrom (live pc) val) →
      execLocalA A L g t op = .ok (PTX.next (setReg t d (val d))) ∨
        ∃ f, execLocalA A L g t op = .error f) :
    SegU K A L g pc (factsFrom (live pc) val) (pc + 1) (factsFrom (live (pc + 1)) val) := by
  intro t ht
  rcases hex t ht with he | ⟨f, he⟩
  · refine .inl ⟨_, run_rtg (run_local hc hl ht he), ?_⟩
    have hs := At.set (v := val d) ht (not_mem_factsFrom hd)
    refine At.mono hs (holds_of_pointwise fun x hx => holds_mem hs.2.2.2.2 ?_)
    rcases List.mem_cons.mp (hlive x hx) with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_factsFrom h)
  · exact .inr (dead_of_error (ht.1 ▸ hc) hl ht.2.2.2.1 he)

/-- **`cvta.shared` of a word below `2 ^ 32`**: the generic shared pointer of the thread's CTA at
that byte, or a fault. -/
theorem exec_cvtaShared_or {t : TState} {d r x : Nat}
    (hr : t.regs r = some (.bits 64 (BitVec.ofNat 64 x))) (hx : x < 2 ^ 32)
    (hL : ∀ b ∈ A, b.localRule L g t (.addr (.cvta false (.shared .cta) 64 d (.reg r))) = none)
    (hA : Assumption.SegFreePc A t.pc) :
    execLocalA A L g t (.addr (.cvta false (.shared .cta) 64 d (.reg r))) =
        .ok (PTX.next (setReg t d
          (.ptr 64 true (.shared (g / L.block) (g / L.block)) (BitVec.ofNat 64 x)))) ∨
      ∃ f, execLocalA A L g t (.addr (.cvta false (.shared .cta) 64 d (.reg r))) = .error f := by
  by_cases hg : g < L.threads ∧ g / L.block < L.grid
  · exact .inl (exec_cvtaShared (cl := false) (toShared := false)
      (readSharedAddress_bits hr (.inr rfl) hg.1 hg.2 hx) rfl hL hA)
  · refine .inr ⟨.badValue, ?_⟩
    have h64 : x < 18446744073709551616 := by omega
    rw [hA.exec rfl, execLocalRule_of_none hL, execLocal_cvta (by rfl), execCvta_shared]
    have ht : truncBits 64 (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := truncBits_ofNat h64 le_rfl
    simp only [readSharedAddress, readValue, readReg, hr, ht, bind, Except.bind, pure,
      Except.pure, or_true, and_true, ite_true]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hg)]
    rfl

/-- Element `j` of a generic write of `n`-byte elements at byte `x + off` of the thread's CTA's
shared memory, or undefined behaviour. -/
def GenWrAt (L : Launch) (g : Nat) (x off n j : Nat) (e : Event) : Prop :=
  (∃ a bs, e.kind = .wr a bs ∧ a.loc = (⟨.shared, g / L.block, x + off⟩ : Loc).at (n * j) ∧
      a.size = n) ∨ ∃ f, e.kind = .ub f

/-- The location of a generic access through a generic shared pointer of the thread's CTA. -/
theorem accessLoc_genShared {t : TState} {m : MemAccess} {r x off : Nat} {loc : Loc}
    (hsp : m.space = none) (hb : m.addr.base = .reg r 64) (ho : m.addr.off = (off : Int))
    (hr : t.regs r = some (.ptr 64 true (.shared (g / L.block) (g / L.block))
      (BitVec.ofNat 64 x)))
    (hx : x < 2 ^ 32) (h : accessLoc L g t m = .ok loc) :
    loc = ⟨.shared, g / L.block, x + off⟩ := by
  have h64 : x < 18446744073709551616 := by omega
  have hx' : (BitVec.ofNat 64 x).toNat = x := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
  simp only [accessLoc, hsp, hb, ho, readReg, hr, readSharedAddress, readValue, bind,
    Except.bind, pure, Except.pure, hx', or_true, and_true, ite_true, hx, throw, throwThe,
    MonadExceptOf.throw] at h
  by_cases hg : g < L.threads ∧ g / L.block < L.grid
  · simp only [hg, and_self, ite_true] at h
    split_ifs at h with h1
    cases h
    rfl
  · simp only [hg, ite_false] at h
    cases h

/-- **A weak generic store through a generic shared pointer** (an access located by
`accessLoc`): element `t.sub` at the pointer's byte plus the instruction's offset. -/
theorem fires_gen_wr_at {t : TState} {m : MemAccess} {pc r x off n j : Nat} {e : Event}
    {o : Option TState}
    (hk : m.kind = .store) (hsem : m.sem = .weak) (hsp : m.space = none)
    (hb : m.addr.base = .reg r 64) (ho : m.addr.off = (off : Int))
    (hchk : (m.nc || m.hints.globalOnly || m.vec == 8 || (m.vec == 4 && m.elem.width == 64)) =
      false)
    (hr : t.regs r = some (.ptr 64 true (.shared (g / L.block) (g / L.block))
      (BitVec.ofNat 64 x)))
    (hx : x < 2 ^ 32) (hn : m.elem.width / 8 = n) (hj : t.sub = j)
    (hrule : m.rule = some .threadAccess) (hloc : m.locSpace? = none)
    (hf : Fires pc (eventTmpl A L g t (.mem m)) e o) : GenWrAt L g x off n j e := by
  subst hn hj
  simp only [eventTmpl] at hf
  unfold memTmpl at hf
  rw [hrule, hloc] at hf
  simp only [ite_true] at hf
  unfold accessTmpl at hf
  rw [hk, accessAcc_of_weak hsem] at hf
  simp only [hchk, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at hf
  cases hl : accessLoc L g t m with
  | error f =>
    simp only [hl] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩
  | ok loc =>
    obtain rfl := accessLoc_genShared hsp hb ho hr hx hl
    simp only [hl, elemAcc] at hf
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

/-- **A weak load at a shared variable's address** (`ld.shared [sym + off]`): element `t.sub`
at the variable's byte plus the offset, wrapped to the 32-bit window. -/
theorem fires_sym_rd_at {t : TState} {m : MemAccess} {pc o n j : Nat} {w : SharedWindow}
    {e : Event} {u : Option TState}
    (hk : m.kind = .load) (hsem : m.sem = .weak) (hsp : m.space = some (.shared w))
    (hb : m.addr.base = .sharedSym o) (hnc : m.nc = false)
    (hn : m.elem.width / 8 = n) (hj : t.sub = j)
    (hrule : m.rule = some .threadAccess) (hloc : m.locSpace? = none)
    (hf : Fires pc (eventTmpl A L g t (.mem m)) e u) :
    (∃ a bs, e.kind = .rd a bs ∧ a.loc = (⟨.shared, g / L.block,
      wrapAddr 32 (BitVec.ofNat 64 (L.sharedBase + o)) m.addr.off⟩ : Loc).at (n * j) ∧
      a.size = n) ∨ ∃ f, e.kind = .ub f := by
  subst hn hj
  simp only [eventTmpl] at hf
  unfold memTmpl at hf
  rw [hrule, hloc] at hf
  simp only [ite_true] at hf
  unfold accessTmpl at hf
  rw [hk, accessAcc_of_weak hsem] at hf
  simp only [accessLoc, hsp, hb, hnc, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
    Except.pure, elemAcc] at hf
  split_ifs at hf <;> simp only [throw, throwThe, MonadExceptOf.throw, Fires] at hf
  · exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · exact .inr ⟨_, congrArg Event.kind hf.1⟩
  · obtain ⟨bs, -, he, -⟩ := hf
    exact .inl ⟨_, bs, congrArg Event.kind he, rfl, rfl⟩

end
end PTX.Flow
