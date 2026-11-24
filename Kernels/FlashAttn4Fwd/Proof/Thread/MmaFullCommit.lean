-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaFullCommitElect
public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc
public import Lemmas.Execution.ShapeExecution

@[expose] public section

/-! # The MMA warp's commits name barriers of its own CTA

A commit fired at a state of the MMA role is the event of the state's commit site (`commit_site`):
`tcgen05.commit` with the multicast mask 3 on a barrier of the thread's CTA (`cSpec`, from the
site's register facts, `MmaEvents.commit_event`). Its targets are the barrier at that address in
both CTAs of the pair, so a target that is barrier `b` of CTA `c` names `b` of the thread's own
CTA, and `c`'s pair leader is the thread's CTA, since commit sites are reached on the leader CTA
only (`Inv.i`). A commit site is a site of the elected lane, before which the run invariant
records a full-mask election that returned the thread's lane (`Counts.elected`).

**The premise** (`CommitRun`): every commit event is fired by a thread of warp 12 from a state of
the MMA role's machine that satisfies the role's run invariant (`Counts`) over the thread's events
before it and the role's state invariant (`Inv`), with the state's register facts, at the
instruction of its site. The composition of the thread machine provides it.

**The fields** (`commit_fbar`; `sFull_commit` and `oFull_commit` are the fields
`SFullFacts.s_commit` and `OFullFacts.o_commit`): a commit notifying barrier `b` of CTA `c` is a
thread's of warp 12 of `c`'s pair leader, after a full-mask election that returned its lane, and
names `b` of its own CTA. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The MMA role's run at the commits**: every commit event is fired by a thread of warp 12 from
a state of the MMA role with the role's run invariant over the thread's earlier events, the state
invariant and the state's register facts, at the instruction of the state's site. -/
def CommitRun (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {sp : TcCommit.Spec}, X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩ →
    warpOf L g = 12 ∧ ∃ (d : D) (t : TState) (ins : Instr) (o : Option TState),
      Counts L g d ((X.tr g).take k) ∧ Inv L g d ∧ Holds t.regs (facts L g d) ∧
      kernel.code[d.site.pc]? = some ins ∧
      Fires d.site.pc (eventTmpl asms L g t ins.op) ⟨pc, .tc (.commit sp)⟩ o

/-- **A commit at an MMA state is its commit site's**, with the site's specification. -/
theorem commit_site (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} {sp : TcCommit.Spec}
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) (hk : e.kind = .tc (.commit sp)) :
    ∃ c, d.site = .commit c ∧ sp = cSpec L g (bar L g (cBar L d c)) := by
  have hev := site_event hpre hg h hc hf
  cases hcb : commitBar L d with
  | none =>
    have := commitsTo_none hev hcb sp.mbar
    simp [commitsTo_of_kind hk] at this
  | some b =>
    obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp only [commitBar, reduceCtorEq] at hcb
    case commit c =>
      simp only [Ev] at hev
      rw [hk] at hev
      cases hev
      exact ⟨c, rfl, rfl⟩

/-- **A commit notifying barrier `b` of CTA `c`** is a thread's of warp 12 of `c`'s pair leader,
after a full-mask election that returned its lane, and names `b` of its own CTA. -/
theorem commit_fbar (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hR : CommitRun L X) {g k pc c : Nat} {sp : TcCommit.Spec} {r : Fin 16} {b : FBar}
    (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (ht : TcCommit.target sp r = some (b.loc L c)) :
    warpOf L g = 12 ∧ leadCta c = ctaOf L g ∧ LeadAt L X g k ∧
      sp.mbar = b.loc L (ctaOf L g) := by
  have hg := event_thread_lt hX he
  obtain ⟨hw, d, t, ins, o, hJ, hi, h, hc, hf⟩ := hR he
  obtain ⟨cc, hs, rfl⟩ := commit_site hpre hg h hc hf rfl
  have hr0 : rank L g = 0 := (hi.i (by rw [hs]; trivial)).2
  obtain ⟨e', hm, inst, hk⟩ := hJ.elected (by rw [hs]; rfl)
  simp only [TcCommit.target, cSpec] at ht
  obtain ⟨hcond, ht⟩ := Option.ite_none_right_eq_some.mp ht
  have hloc : (cBar L d cc).loc L (g / L.block / 2 * 2 + r.val) = b.loc L c := by
    simpa only [Option.some.injEq, FBar.loc, bar] using ht
  obtain ⟨rfl, rfl⟩ := FBar.loc_inj hloc
  refine ⟨hw, ?_, ?_, rfl⟩
  · have hr := hcond.1
    simp only [rank] at hr0
    simp only [leadCta, ctaOf]
    omega
  · obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hm
    have hjk : j < k := by
      have := hj
      rw [List.length_take] at this
      omega
    refine ⟨j, hjk, e'.pc, inst, ?_⟩
    show (X.tr g)[j]? = _
    rw [← List.getElem?_take_of_lt (j := k) hjk, List.getElem?_eq_getElem hj, hget, ← hk]

/-- **The field `SFullFacts.s_commit`.** -/
theorem sFull_commit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hR : CommitRun L X) {g k pc c st : Nat} {sp : TcCommit.Spec} {r : Fin 16}
    (_ : g < L.threads) (hst : st < 2) (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (ht : TcCommit.target sp r = some (sFullBar L c st)) :
    warpOf L g = 12 ∧ leadCta c = ctaOf L g ∧ LeadAt L X g k ∧
      sp.mbar = sFullBar L (ctaOf L g) st := by
  rw [show sFullBar L c st = sFullBar L c (⟨st, hst⟩ : Fin 2) from rfl, sFullBar_eq] at ht
  rw [show sFullBar L (ctaOf L g) st = sFullBar L (ctaOf L g) (⟨st, hst⟩ : Fin 2) from rfl,
    sFullBar_eq]
  exact commit_fbar hpre hX hR he ht

/-- **The field `OFullFacts.o_commit`.** -/
theorem oFull_commit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hR : CommitRun L X) {g k pc c st : Nat} {sp : TcCommit.Spec} {r : Fin 16}
    (_ : g < L.threads) (hst : st < 2) (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (ht : TcCommit.target sp r = some (oFullBar L c st)) :
    warpOf L g = 12 ∧ leadCta c = ctaOf L g ∧ LeadAt L X g k ∧
      sp.mbar = oFullBar L (ctaOf L g) st := by
  rw [show oFullBar L c st = oFullBar L c (⟨st, hst⟩ : Fin 2) from rfl, oFullBar_eq] at ht
  rw [show oFullBar L (ctaOf L g) st = oFullBar L (ctaOf L g) (⟨st, hst⟩ : Fin 2) from rfl,
    oFullBar_eq]
  exact commit_fbar hpre hX hR he ht

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
