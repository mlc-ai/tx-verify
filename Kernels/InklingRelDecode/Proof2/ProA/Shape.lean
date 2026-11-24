-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.ProA.Steps
public import Kernels.InklingRelDecode.Proof.Thread.EvDProLoad
public import Kernels.InklingRelDecode.Proof.Thread.EvDProStore
public import Kernels.InklingRelDecode.Proof.Thread.EvDProCopy

@[expose] public section

/-! # The prologue's events by state

The event a state of the prologue fires (`Ev`, `shape`), by site family: the three request words
and the six block-table words are four-byte reads at the address register's word
(`Proof.ProA.loadAddr`), the query loads two-byte reads, the broadcasts a full-warp
`shfl.sync.idx` of the thread's warp index from lane 0, the elections `elect.sync` over the full
mask, and the CTA barriers `bar.sync 0, 128` and `barrier.sync 1`. The other sites have no entry
yet (`True`): no reference invariant reads them so far.

A concrete state of a family state is one of the flat machine's state it regroups
(`fired_old`), so the flat machine's per-family shape lemmas (`Proof/Thread/EvDPro*`) give the
entries. -/

namespace PTX.Kernels.InklingRelDecode.Proof2.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode
open PTX.Kernels.InklingRelDecode.Proof.ProA (Dat Inh loadAddr)

noncomputable section
set_option maxRecDepth 100000

/-- The event-shape table of the prologue. -/
def Ev (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .ld _ | .lb _ _ => ∃ bs : List (Option Byte), bs.length = 4 ∧
      e = ⟨d.site.pc, .rd (Proof.EvD.wordAcc ⟨.global, 0, loadAddr L g d.dt d.site.old⟩) bs⟩
  | .ldq _ => ∃ bs : List (Option Byte), bs.length = 2 ∧
      e = ⟨d.site.pc, .rd { loc := ⟨.global, 0, loadAddr L g d.dt d.site.old⟩, size := 2 } bs⟩
  | .psh _ => ∃ recv ok, e = ⟨d.site.pc, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩
  | .el _ | .pel _ _ => ∃ inst leader, e = ⟨d.site.pc, .elect 4294967295 inst leader⟩
  | _ => True

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **A concrete state of a family state is a concrete state of the flat state it regroups.** -/
theorem fired_old {P : Inh} {d : D} (hx : d.site ≠ .exit) {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code L g P).AtD d t) (hi : (code L g P).inv d)
    (hc : kernel.code[(code L g P).pc d]? = some ins)
    (hf : Fires ((code L g P).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    Proof.ProA.Fired L g d.old e o := by
  have hpc : d.site.pc = d.site.old.pc := pc_old _ hx
  refine ⟨t, ⟨hat.1.trans hpc, hat.2.1.trans (sub_old _), hat.2.2.1, hat.2.2.2.1, ?_⟩, hi, ins,
    hpc ▸ hc, hpc ▸ hf⟩
  have := hat.2.2.2.2
  simp only at this
  rw [hpc] at this
  exact this

/-- **An event a state of the prologue fires and continues after is its shape.** -/
theorem shape (P : Inh) {d : D} (hx : d.site ≠ .exit) {t u : TState} {ins : Instr} {e : Event}
    (hat : (code L g P).AtD d t) (hi : (code L g P).inv d)
    (hc : kernel.code[(code L g P).pc d]? = some ins)
    (hf : Fires ((code L g P).pc d) (eventTmpl Assumptions.all L g t ins.op) e (some u)) :
    Ev L g d e := by
  have hF := fired_old hx hat hi hc hf
  obtain ⟨s, dt⟩ := d
  cases s with
  | ld k =>
    obtain ⟨bs, hl, he⟩ := Proof.ProA.shape_ld32 hF
      (by fin_cases k <;> simp only [D.old] <;> decide)
    exact ⟨bs, hl, by rw [he]; congr 1; exact (pc_old _ hx).symm⟩
  | lb b h =>
    obtain ⟨bs, hl, he⟩ := Proof.ProA.shape_ld32 hF
      (by fin_cases b <;> fin_cases h <;> simp only [D.old] <;> decide)
    exact ⟨bs, hl, by rw [he]; congr 1; exact (pc_old _ hx).symm⟩
  | ldq k =>
    obtain ⟨bs, hl, he⟩ := Proof.ProA.shape_ldq k.isLt hF (by fin_cases k <;> rfl)
    exact ⟨bs, hl, by rw [he]; congr 1; exact (pc_old _ hx).symm⟩
  | psh b =>
    obtain ⟨r, ok, he⟩ := Proof.ProA.shape_psh hF (by fin_cases b <;> simp [D.old, Site.old,
      blockOld])
    exact ⟨r, ok, by rw [he]; congr 1; exact (pc_old _ hx).symm⟩
  | el i =>
    obtain ⟨a, b, he⟩ := Proof.ProA.shape_el (i := i.val) (by omega) hF (by fin_cases i <;> rfl)
    exact ⟨a, b, by rw [he]; congr 1; exact (pc_old _ hx).symm⟩
  | pel b j =>
    obtain ⟨a, c, he⟩ := Proof.ProA.shape_el (i := 12 + 4 * b.val + j.val) (by omega) hF
      (by fin_cases b <;> fin_cases j <;> rfl)
    exact ⟨a, c, by rw [he]; congr 1; exact (pc_old _ hx).symm⟩
  | _ => trivial

end
end PTX.Kernels.InklingRelDecode.Proof2.ProA
