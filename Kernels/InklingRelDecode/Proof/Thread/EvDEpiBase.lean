-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiEntry
public import Kernels.InklingRelDecode.Proof.Thread.EvDFires

@[expose] public section

/-!
# Event shapes of the epilogue: the vocabulary

The epilogue machine (`Epi.code`, warps 0-3 of the default partition, from the poll of `o_final`
to the return) exports which state follows an event (`Epi.next`). This file and the ones after it
say what each event *is*, over the machine's abstract states `Epi.D` and nothing else:

* `Epi.Fired L g d e o`: the event `e` fires from a concrete thread state of the abstract state
  `d`, with continuation `o`. It is `Flow.Machine.Fired` of the machine at `some d`; the machine's
  initial state is irrelevant to it (`Fired_of`).
* `Epi.evPc d.site`: the source position the framework records in the events of the site. It is
  the site's own pc, hidden behind one definition; no statement mentions a literal pc.
* `Epi.Shape L g d e`: the event shape of state `d`, by site (`EvDEpiSync`, `EvDEpiStore`).

The statements say what the events are in terms of `Prm` (the registers of the softmax region
that the epilogue carries), `D.word`/`D.lseWord` (the stored words) and `D.o` (the words the
Tensor Memory load returns): what `Prm` means for the launch is `EvDEpiMeans`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

/-- The source position of the events a site fires: the instruction's own position. -/
def evPc (s : Site) : Nat := s.pc

/-- The event `e` fires from a concrete thread state of the abstract state `d` of the epilogue's
code machine, continuing in `o` (`none` after a fault or the return). -/
def Fired (L : Launch) (g : Nat) (d : D) (e : Event) (o : Option TState) : Prop :=
  ∃ t, (code asms L g d).AtD d t ∧ Inv d ∧
    Fires t.pc ((code asms L g d).tmpl (some d) t) e o

variable {L : Launch} {g : Nat}

/-- **What a fired event comes from**: a thread state with the abstract state's facts, at the
site's pc, whose instruction `ins` fires the event. -/
theorem fired_unpack {d : D} {e : Event} {o : Option TState} (h : Fired L g d e o) :
    ∃ t ins, At t d.site.pc (facts d) ∧ Inv d ∧ kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl asms L g t ins.op) e o := by
  obtain ⟨t, ha, hinv, hf⟩ := h
  obtain ⟨ins, hc, -, -⟩ := site_ok_all hinv
  refine ⟨t, ins, ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩, hinv, hc, ?_⟩
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
theorem reg_at {d : D} {t : TState} {r : Nat} (h : At t d.site.pc (facts d))
    (hl : r ∈ Flow.live d.site.pc) : t.regs r = some (valueOf d r) :=
  holds_mem h.2.2.2.2 (Flow.mem_factsFrom hl)

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
