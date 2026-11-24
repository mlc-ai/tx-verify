-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmGen
public import Kernels.InklingRelDecode.Proof.Thread.EvDFires

@[expose] public section

/-!
# Event shapes of the softmax region: the vocabulary

The softmax region's code machine (`Sm.code`, warps 0-3 of the default partition, from the
register increase at pc 574 to the exit at pc 2560) exports which state follows an event
(`Sm.next`). This file and the ones after it say what each event *is*, over the machine's
abstract states `Sm.D` and nothing else:

* `Sm.Fired L g d e o`: the event `e` fires from a concrete thread state of the abstract state
  `d`, with continuation `o`. It is `Flow.Machine.Fired` of the machine at `some d`; the machine's
  initial state is irrelevant to it (`Fired_iff`).
* `Sm.evPc d.site`: the source position the framework records in the events of the site. It is
  the site's own pc, hidden behind one definition; no statement mentions a literal pc.
* `Sm.Shape L g d e` (`EvSShape`): the event shape of state `d`, by site.

A shape theorem takes `Fired L g d e (some u)` and the site (`d.site = s`); a continuing event is
the only one a shape is about (a fault is undefined behaviour). The tools here are the one
unpacking of `Fired` (`fired_unpack`: the thread state, the invariant, the instruction that fires
the event), the facts that no assumption of the kernel changes the poll or the `tcgen05.ld`
template, and the register lookup through the state's table (`reg_at`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

/-- The source position of the events a site fires: the instruction's own position. -/
def evPc (s : Site) : Nat := s.pc

/-- The event `e` fires from a concrete thread state of the abstract state `d` of the softmax
region's code machine, continuing in `o` (`none` after a fault). -/
def Fired (L : Launch) (g : Nat) (d : D) (e : Event) (o : Option TState) : Prop :=
  ∃ t, (code asms L g d).AtD d t ∧ Inv L g d ∧
    Fires t.pc ((code asms L g d).tmpl (some d) t) e o

variable {L : Launch} {g : Nat}

/-- **What a fired event comes from**: a thread state with the abstract state's facts, at the
site's pc, whose instruction `ins` (the one the code has there) fires the event. -/
theorem fired_unpack {d : D} {e : Event} {o : Option TState} {ins : Instr}
    (hc : kernel.code[d.site.pc]? = some ins) (h : Fired L g d e o) :
    ∃ t, At t d.site.pc (facts L g d) ∧ Inv L g d ∧
      Fires d.site.pc (eventTmpl asms L g t ins.op) e o := by
  obtain ⟨t, ha, hinv, hf⟩ := h
  refine ⟨t, ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩, hinv, ?_⟩
  have hpc : t.pc = d.site.pc := ha.1
  rw [hpc] at hf
  simpa only [Code.tmpl, hc] using hf

/-- No assumption of the kernel widens the scope of an mbarrier poll or arrival. -/
theorem asms_noWiden (pc : Nat) : asms.any (·.clusterScopeMbar pc) = false := by
  simp only [asms, Assumptions.all]
  rfl

/-- No assumption of the kernel changes the `tcgen05.ld` template. -/
theorem asms_noLdWait (pc : Nat) : asms.any (·.tcLdWait pc) = false := by
  simp only [asms, Assumptions.all]
  rfl

/-- The registers a site reads are the table's: a register live at the site. -/
theorem reg_at {d : D} {t : TState} {r : Nat} (h : At t d.site.pc (facts L g d))
    (hl : r ∈ Flow.live d.site.pc) : t.regs r = some (valueOf L g d r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

/-- The footprint of a plain access of `size` bytes at the global address `a`. -/
abbrev globalAcc (a size : Nat) : Acc := { loc := ⟨.global, 0, a⟩, size := size }

/-- **A full-warp `shfl.sync.bfly` with lane mask 1 and clamp 31 of register `r`** fires a
shuffle whose operand is the register's value. -/
theorem fires_shfl_bfly1 {A : List Assumption} {t : TState} {d r : Nat}
    {p : Option Nat} {ty : Option DType} {mask : Opnd} {pc : Nat} {e : Event}
    {o : Option TState} {v : Value} (hr : t.regs r = some v)
    (hf : Fires pc (eventTmpl A L g t (.warp ⟨.shfl .bfly, ty, some d :: (p.map some).toList,
      [.reg r, .imm 1, .imm 31], some mask⟩)) e o)
    (hs : Execution.isShfl e = true) : ∃ recv ok, e = ⟨pc, .shfl .bfly v 1 31 recv ok⟩ := by
  have h0 : (truncBits 32 (BitVec.ofInt 64 1)).toNat = 1 := by decide
  have h31 : (truncBits 32 (BitVec.ofInt 64 31)).toNat = 31 := by decide
  have hp : (p.map some).toList.head?.join = p := by cases p <;> rfl
  simp only [eventTmpl] at hf
  rcases warpTmpl_shfl (L := L) (g := g) (t := t) (mode := .bfly) (ty := ty) (d := d)
    (ps := (p.map some).toList) (a := .reg r) (b := .imm 1) (c := .imm 31) (mask := mask) with
    h | h <;> rw [h] at hf
  swap
  · obtain ⟨epc, ek⟩ := e
    simp_all [Fires, Execution.isShfl]
  rw [hp] at hf
  simp only [shflTmpl, readValue, readReg, hr, readBits] at hf
  repeat' (split at hf)
  all_goals simp_all [Fires, pure, Except.pure, bind, Except.bind, Execution.isShfl]
  all_goals subst_vars
  all_goals aesop

/-- The launch's shared window: aligned, and it does not wrap in the 32-bit shared address space
(`Pre.sharedAlignment`, `Pre.sharedRange`). -/
def SharedOk (L : Launch) : Prop :=
  L.sharedBase % 1024 = 0 ∧ L.sharedBase + 213340 ≤ 2 ^ 18

theorem sharedOk_of_pre {P : Params} {mem0 : Mem0} (hpre : Pre P L mem0) : SharedOk L :=
  ⟨hpre.sharedAlignment, hpre.sharedRange⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
