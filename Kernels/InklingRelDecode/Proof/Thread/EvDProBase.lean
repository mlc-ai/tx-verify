-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAExit
public import Kernels.InklingRelDecode.Proof.Thread.ProBSpec
public import Kernels.InklingRelDecode.Proof.Thread.EvDFires

@[expose] public section

/-!
# Event shapes of the prologue: the vocabulary

The prologue machine (`ProA.code`, warps 0-3 of the default partition, from `setmaxnreg.inc` to the
`barrier.sync 1` before the softmax region) exports which state follows an event. This file and
the ones after it say what each event *is*, over the machine's abstract states `ProA.D`
(a `ProA.Site` and the data `ProA.Dat`: the inherited registers and parameter words, the loaded
words, the query values, the outcomes of the elections):

* `ProA.Fired L g d e o`: the event `e` fires from a concrete thread state of the abstract state
  `d`, continuing in `o`; `Fired_of_machine` ties it to `Flow.Machine.Fired` of the code machine;
* `ProA.evPc d.site`: the source position the framework records in the events of the site, the
  site's own pc hidden behind one definition;
* `ProA.SharedOk L`: the launch's shared window is aligned and below `2 ^ 18`
  (`Pre.sharedAlignment`, `Pre.sharedRange`), which the shared addresses of the prologue need.

The prologue's tables mention registers by number; the statements of the shape theorems do not:
they speak of barriers (`EvD.Bar`), the launch, and the data `Dat`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

/-- The source position of the events a site fires: the instruction's own position. -/
def evPc (s : Site) : Nat := s.pc

/-- The event `e` fires from a concrete thread state of the abstract state `d` of the prologue,
continuing in `o` (`none` after a fault). -/
def Fired (L : Launch) (g : Nat) (d : D) (e : Event) (o : Option TState) : Prop :=
  ∃ t, AtS L g d t ∧ Inv L g d ∧ ∃ ins, kernel.code[d.site.pc]? = some ins ∧
    Fires d.site.pc (eventTmpl asms L g t ins.op) e o

/-- The code machine's `Fired` at `some d` is `Fired`, whatever the machine's initial state. -/
theorem Fired_of_machine {L : Launch} {g : Nat} {P : Inh} {d : D} {e : Event}
    {o : Option TState} (h : (code L g P).toMachine.Fired (some d) e o) : Fired L g d e o := by
  obtain ⟨t, ⟨ha, hinv⟩, hf⟩ := h
  obtain ⟨ins, hc, -, -⟩ := site_ok hinv
  refine ⟨t, ha, hinv, ins, hc, ?_⟩
  have hpc : t.pc = d.site.pc := ha.1
  rw [hpc] at hf
  change Fires d.site.pc ((code L g P).tmpl (some d) t) e o at hf
  simpa only [Flow.Code.tmpl, hc] using hf

variable {L : Launch} {g : Nat} {d : D} {e : Event} {o : Option TState}

/-- **What a fired event comes from**: a thread state with the abstract state's facts, whose
instruction at the site's pc fires the event. -/
theorem fired_unpack (h : Fired L g d e o) :
    ∃ t ins, AtS L g d t ∧ Inv L g d ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl asms L g t ins.op) e o := by
  obtain ⟨t, ha, hi, ins, hc, hf⟩ := h
  exact ⟨t, ins, ha, hi, hc, hf⟩

/-- The registers a site reads are the table's: a register live at the site. -/
theorem reg_at {t : TState} {r : Nat} (h : AtS L g d t) (hl : r ∈ Flow.live d.site.pc) :
    t.regs r = some (valueOf L g d.dt r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

/-- No assumption of the kernel widens the scope of an mbarrier poll or arrival. -/
theorem asms_noWiden (pc : Nat) : asms.any (·.clusterScopeMbar pc) = false := by
  simp only [asms, Assumptions.all]
  rfl

/-- The launch's shared window: aligned to 1024 bytes and, with the kernel's 213340 bytes,
below `2 ^ 18` (`Pre.sharedAlignment`, `Pre.sharedRange`). -/
def SharedOk (L : Launch) : Prop :=
  L.sharedBase % 1024 = 0 ∧ L.sharedBase + 213340 ≤ 2 ^ 18

theorem sharedOk_of_pre {P : Params} {mem0 : Mem0} (hpre : Pre P L mem0) : SharedOk L :=
  ⟨hpre.sharedAlignment, hpre.sharedRange⟩

/-- The shared address register `%r205 + off` as `Value`: `sharedBase + off` modulo `2 ^ 32`. -/
theorem wAdd32_smem (L : Launch) (off : Int) (h : 0 ≤ off) :
    wAdd32 (wSmem L) (BitVec.ofInt 64 off) =
      BitVec.ofNat 64 ((L.sharedBase + off.toNat) % 2 ^ 32) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
  have l : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  simp only [wSmem, l, truncBits_ofNat _ _ (by omega : 32 ≤ 64), wAdd32_ofNat, Nat.add_zero,
    Int.toNat_natCast]
  exact congrArg (BitVec.ofNat 64) (by omega)

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
