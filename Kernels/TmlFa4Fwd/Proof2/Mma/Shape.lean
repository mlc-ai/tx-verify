-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Mma.Machine
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Shape
public import Lemmas.Flow.Step.ShapeRegs

@[expose] public section

/-! # The MMA warp's events by state

The event a state of the MMA warp fires is the event of its site (`Ev`, `shape`): the named
barrier 2 with 416 threads, a read (the allocation's address word), a broadcast of the state's
word from lane 0, the scheduler's events as in the output warp (`Epilogue.Ev` of the scan state
at the corresponding site), a read of the request's offsets and used-K length, a poll of the
state's barrier with the state's parity, an election, an MMA, a commit to the state's barrier,
the permit relinquishment, the deallocation and the exit. A poll or commit whose address is not
aligned, a read, an MMA and the deallocation may instead fault (`ub`), which no execution
without undefined behaviour has. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (addrS laneW headsW chosen vbits)

noncomputable section
set_option maxRecDepth 100000

/-- The output warp's site of a scheduler site. -/
def Site.toE : Site → Epilogue.Site
  | .word k => .word k
  | .down k => .down k
  | .up k j => .up k j
  | .total k => .total k
  | .vote l => .vote l
  | .pre l => .pre l
  | .tiles l => .tiles l
  | _ => .start

/-- The address word and parity word of poll `k`. -/
def wtOp (L : Launch) (v : V) : Fin 10 → BitVec 64 × BitVec 64
  | 0 => (sbW L, i32 0)
  | 1 => (addi (sbW L) 32, i32 0)
  | 2 => (addi (sbW L) 8, i32 0)
  | 3 => (addi (slotAddr L v.slot) 32, v.kvp)
  | 4 => (addi (sbW L) 96, v.pp)
  | 5 => (addi (slotAddr L (slot1 v)) 32, kvp1 v)
  | 6 => (addi (sbW L) 104, v.pp)
  | 7 => (addi (slotAddr L v.slot) 32, v.kvp)
  | 8 => (addi (sbW L) 96, v.pp)
  | 9 => (addi (sbW L) 104, v.pp)

/-- The address word of the poll in PV block `b` (the second half of P). -/
def mwOp (L : Launch) (b : Fin 4) : BitVec 64 :=
  if b.val % 2 = 0 then addi (sbW L) 112 else addi (sbW L) 120

/-- The address word and offset of commit `c`. -/
def cmOp (L : Launch) (v : V) : Fin 12 → BitVec 64 × Int
  | 0 => (addi (sbW L) 80, 0)
  | 1 => (sbW L, 88)
  | 2 => (sbW L, 56)
  | 3 => (addi (sbW L) 80, 0)
  | 4 => (slotAddr L v.slot, 56)
  | 5 => (addi (sbW L) 88, 0)
  | 6 => (slotAddr L (slot1 v), 56)
  | 7 => (sbW L, 16)
  | 8 => (sbW L, 24)
  | 9 => (slotAddr L v.slot, 56)
  | 10 => (BitVec.ofNat 64 (L.sharedBase + 144), 0)
  | 11 => (sbW L, 152)

/-- The word broadcast `k` sends from lane 0. -/
def shSrc (L : Launch) (v : V) : Fin 14 → BitVec 64
  | 0 => ori (andi (shru (BitVec.ofNat 64 (L.sharedBase + 68608)) 4) 16320) 65536
  | 1 => i32 0
  | 2 => i32 128
  | 3 => i32 64
  | 4 => slotDesc L v.slot 67108864
  | 5 => i32 256
  | 6 => slotDesc L (slot1 v) 65536
  | 7 => i32 192
  | 8 => i32 384
  | 9 => i32 64
  | 10 => slotDesc L v.slot 67108864
  | 11 => i32 256
  | 12 => i32 192
  | 13 => i32 384

/-- The address a request read reads. -/
def reqAddr (p : Params) (v : V) : Site → BitVec 64
  | .q0 => truncBits 64 (vbits (addrS p.cuQBase (chosen v.sc))) + BitVec.ofInt 64 0
  | .q1 => truncBits 64 (vbits (addrS p.cuQBase (chosen v.sc))) + BitVec.ofInt 64 4
  | _ => truncBits 64 (vbits (addrS p.usedKBase (chosen v.sc))) + BitVec.ofInt 64 0

/-- The event-shape table of the MMA warp. -/
def Ev (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .bar1 | .bar2 _ => e.kind = .bar 2 (some 416) .sync
  | .ldAlloc => (∃ a bs, e.kind = .rd a bs) ∨ ∃ f, e.kind = .ub f
  | .bcast => ∃ recv ok,
      e.kind = .shfl .idx (.bits 32 (ori (andi (shru (addi (sbW L) 35840) 4) 16320) 65536)) 0 31
        recv ok
  | .word _ | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ =>
      Epilogue.Ev p L g { d.v.sc with site := d.site.toE } e
  | .q0 | .q1 | .uk =>
      (∃ bs, e.kind = .rd (wordAcc (reqAddr p d.v d.site).toNat) bs) ∨ ∃ f, e.kind = .ub f
  | .wt k =>
      (∃ ok, e.kind = .wait (smLoc L g (wtOp L d.v k).1 0)
        ((truncBits 32 (wtOp L d.v k).2).toNat % 2) ok true .cta) ∨ ∃ f, e.kind = .ub f
  | .mw b _ =>
      (∃ ok, e.kind = .wait (smLoc L g (mwOp L b) 0) ((truncBits 32 d.v.pp).toNat % 2) ok true
        .cta) ∨ ∃ f, e.kind = .ub f
  | .sh k => ∃ recv ok, e.kind = .shfl .idx (.bits 32 (shSrc L d.v k)) 0 31 recv ok
  | .eq _ | .ep _ | .ce _ =>
      (∃ inst ld, e.pc = d.site.pc ∧ e.kind = .elect (2 ^ 32 - 1) inst ld) ∨ ∃ f, e.kind = .ub f
  | .qk _ _ | .pv _ _ => (∃ a s acc ms, e.kind = .tc (.mma a s acc ms)) ∨ ∃ f, e.kind = .ub f
  | .cm c =>
      (∃ s, e.kind = .tc (.commit s) ∧ s.mbar = smLoc L g (cmOp L d.v c).1 (cmOp L d.v c).2 ∧
        s.group = .one) ∨ ∃ f, e.kind = .ub f
  | .relinq _ | .dealloc _ =>
      (∃ dst act, e.kind = .tc (.resource .one dst act)) ∨ ∃ f, e.kind = .ub f
  | .exit _ => e.kind = .exit

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

/-- A register's value at a state, as the table gives it. -/
theorem reg_of {d : D} {t : TState} {r : Nat} (h : At t d.site.pc (facts p L g ent d))
    (hr : r ∈ Flow.live d.site.pc) : t.regs r = some (valueOf p L g ent d r) :=
  holds_mem h.2.2.2.2 (mem_factsFrom hr)

/-- A register's value at a state is the bits the table gives it. -/
theorem reg_bits {s : Site} {v : V} {t : TState} {r w : Nat} {x : BitVec 64}
    (h : At t s.pc (facts p L g ent ⟨s, v⟩)) (hr : r ∈ Flow.live s.pc)
    (hv : valueOf p L g ent ⟨s, v⟩ r = .bits w x) : t.regs r = some (.bits w x) :=
  (reg_of (d := ⟨s, v⟩) h hr).trans (congrArg some hv)

theorem reg_pred {s : Site} {v : V} {t : TState} {r : Nat} {b : Bool}
    (h : At t s.pc (facts p L g ent ⟨s, v⟩)) (hr : r ∈ Flow.live s.pc)
    (hv : valueOf p L g ent ⟨s, v⟩ r = .pred b) : t.regs r = some (.pred b) :=
  (reg_of (d := ⟨s, v⟩) h hr).trans (congrArg some hv)

theorem readBits_reg {t : TState} {r w : Nat} {x : BitVec 64} (h : t.regs r = some (.bits w x)) :
    readBits L g t 32 (.reg r) = .ok (truncBits 32 x) := by
  simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure]

/-- An election with the immediate mask `-1` elects among the full warp, at its pc. -/
theorem elect_ev {t : TState} {dst : Option Nat} {pr : Nat} {ty : Option DType} {pc : Nat}
    {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.warp ⟨.elect, ty, [dst, some pr], [], some (.imm (-1))⟩)) e o) :
    (∃ inst ld, e.pc = pc ∧ e.kind = .elect (2 ^ 32 - 1) inst ld) ∨ ∃ f, e.kind = .ub f := by
  rcases fires_elect_mask (bits := truncBits 32 (BitVec.ofInt 64 (-1))) rfl hf with
    ⟨inst, ld, rfl⟩ | ⟨f, rfl⟩
  · exact .inl ⟨inst, ld, rfl, rfl⟩
  · exact .inr ⟨f, rfl⟩

set_option hygiene false in
/-- A shuffle site: its operand register from the table, the other operands immediates or
registers of the table. -/
macro "shfl_case" : tactic => `(tactic| first
  | exact fires_shfl_reg hblk (reg_bits h (by lit_mem) rfl) rfl rfl hf
  | exact fires_shfl_reg hblk (reg_bits h (by lit_mem) rfl)
      (readBits_reg (reg_bits h (by lit_mem) rfl)) rfl hf)

set_option hygiene false in
/-- The code of a literal site from its lookup. -/
macro "site_code" : tactic => `(tactic| (
  try dsimp only [Fin.reduceFinMk, Fin.isValue] at h hc hf ⊢
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))))

set_option maxHeartbeats 4000000 in
/-- **The event a state of the MMA warp fires is the event of its site.** -/
theorem shape (hp : Pre p L m) : (code p L g ent).Shape (Ev p L g) := by
  intro d t ins e o h hi hc hf
  replace h : At t d.site.pc (facts p L g ent d) := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  have hblk : L.block % 32 = 0 := by rw [hp.block]
  obtain ⟨site, v⟩ := d
  cases site with
  | wt k =>
    simp only [Ev]
    fin_cases k <;> site_code <;>
      refine fires_wait_reg (wx := 32) (wq := 32) ?_ (reg_bits h ?_ ?_) (reg_bits h ?_ ?_) hf <;>
      first | (rw [h.1]; decide) | lit_mem | rfl
  | mw b ld =>
    simp only [Ev]
    fin_cases b <;> cases ld <;> site_code <;>
      refine fires_wait_reg (wx := 32) (wq := 32) ?_ (reg_bits h ?_ ?_) (reg_bits h ?_ ?_) hf <;>
      first | (rw [h.1]; decide) | lit_mem | rfl
  | cm c =>
    simp only [Ev]
    fin_cases c <;> site_code <;>
      refine fires_commit_reg (wx := 32) (reg_bits h ?_ ?_) hf <;> first | lit_mem | rfl
  | sh k =>
    simp only [Ev]
    fin_cases k <;> site_code <;> shfl_case
  | bcast =>
    simp only [Ev]
    site_code
    shfl_case
  | eq b =>
    simp only [Ev]
    fin_cases b <;> site_code <;> exact elect_ev hf
  | ep b =>
    simp only [Ev]
    fin_cases b <;> site_code <;> exact elect_ev hf
  | ce c =>
    simp only [Ev]
    fin_cases c <;> site_code <;> exact elect_ev hf
  | qk b j =>
    simp only [Ev]
    fin_cases b <;> fin_cases j <;> site_code <;> exact fires_tcMma_kind hf
  | pv b j =>
    simp only [Ev]
    fin_cases b <;> fin_cases j <;> site_code <;> exact fires_tcMma_kind hf
  | bar1 =>
    simp only [Ev]
    site_code
    exact fires_barImm (by decide) (by decide) (by decide) (by decide) (by rw [hp.block]; decide) hf
  | bar2 l =>
    simp only [Ev]
    cases l <;> site_code <;>
      exact fires_barImm (by decide) (by decide) (by decide) (by decide) (by rw [hp.block]; decide)
        hf
  | relinq l =>
    simp only [Ev]
    cases l <;> site_code <;> exact fires_tcResource_kind tmemTmpl_relinquish hf
  | dealloc l =>
    simp only [Ev]
    cases l <;> site_code <;> exact fires_tcResource_kind tmemTmpl_dealloc hf
  | exit l =>
    simp only [Ev]
    cases l <;> site_code <;> (simp only [eventTmpl, Fires] at hf; exact congrArg Event.kind hf.1)
  | ldAlloc =>
    simp only [Ev]
    site_code
    change Fires _ (loadTmpl Assumptions.all L g t .shared false 32 [1179] 2535 312) e o at hf
    exact fires_load_kind hf
  | q0 =>
    simp only [Ev]
    site_code
    change Fires _ (loadTmpl Assumptions.all L g t .global false 32 [2538] 7881 0) e o at hf
    exact fires_load_reg h.2.1 (reg_bits h (by lit_mem) rfl) hf
  | q1 =>
    simp only [Ev]
    site_code
    change Fires _ (loadTmpl Assumptions.all L g t .global false 32 [2539] 7881 4) e o at hf
    exact fires_load_reg h.2.1 (reg_bits h (by lit_mem) rfl) hf
  | uk =>
    simp only [Ev]
    site_code
    change Fires _ (loadTmpl Assumptions.all L g t .global false 32 [2541] 7882 0) e o at hf
    exact fires_load_reg h.2.1 (reg_bits h (by lit_mem) rfl) hf
  | word k =>
    simp only [Ev, Site.toE, Epilogue.Ev, Epilogue.rdAddr]
    cases k <;> site_code
    · change Fires _ (loadTmpl Assumptions.all L g t .global false 32 [7193] 7877 0) e o at hf
      exact fires_load_reg h.2.1 (reg_bits h (by lit_mem) rfl) hf
    · change Fires _ (loadTmpl Assumptions.all L g t .global false 32 [7195] 7879 0) e o at hf
      exact fires_load_reg h.2.1 (reg_bits h (by lit_mem) rfl) hf
    · change Fires _ (loadTmpl Assumptions.all L g t .global false 32 [7209] 7884 0) e o at hf
      exact fires_load_reg h.2.1 (reg_bits h (by lit_mem) rfl) hf
    · change Fires _ (loadTmpl Assumptions.all L g t .global false 32 [7211] 7886 0) e o at hf
      exact fires_load_reg h.2.1 (reg_bits h (by lit_mem) rfl) hf
  | down k =>
    simp only [Ev, Site.toE, Epilogue.Ev]
    cases k <;> site_code <;> shfl_case
  | up k j =>
    simp only [Ev, Site.toE, Epilogue.Ev]
    cases k <;> fin_cases j <;> site_code <;> shfl_case
  | total k =>
    simp only [Ev, Site.toE, Epilogue.Ev]
    cases k <;> site_code <;> shfl_case
  | vote l =>
    simp only [Ev, Site.toE, Epilogue.Ev]
    cases l <;> site_code <;>
      exact fires_vote_reg hblk (reg_pred h (by lit_mem) rfl) hf
  | pre l =>
    simp only [Ev, Site.toE, Epilogue.Ev]
    cases l <;> site_code <;> shfl_case
  | tiles l =>
    simp only [Ev, Site.toE, Epilogue.Ev]
    cases l <;> site_code <;> shfl_case

/-- The kind of value each site returns into its registers: a 32-bit word at the loads and
shuffles the warp computes with. The read of the allocation's address is followed whatever it
returns (`ta`, read only by the deallocation). -/
def ret (d : D) : RetKind :=
  match d.site with
  | .word _ | .q0 | .q1 | .uk | .bcast | .down _ | .up _ _ | .total _ | .pre _ | .tiles _
  | .sh _ => .word 32
  | _ => .none

/-- **The machine stops exactly on a returned value that is not a 32-bit word**: the `stop_iff`
obligation of the role's fragment. -/
theorem stop_iff (d : D) : ∀ {e : Event}, (code p L g ent).inv d → Ev p L g d e →
    ((code p L g ent).next d e = some none ↔ ¬ (ret d).accepts e) := by
  obtain ⟨s, v⟩ := d
  stop_cases s unfolding [Ev, Site.toE, Epilogue.Ev]
    trans [ret, succ, word32, afterTotal, afterTiles, loopHead, scanExit, passStart, scAt]

/-- An event whose returned value has the site's kind does not stop the machine. -/
theorem next_ne_stop {d : D} {e : Event} (hev : Ev p L g d e) (hE : (ret d).accepts e) :
    (code p L g ent).next d e ≠ some none :=
  fun h => ((stop_iff d trivial hev).mp h) hE

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Mma
