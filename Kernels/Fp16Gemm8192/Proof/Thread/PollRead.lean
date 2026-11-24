-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaLeader
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcPoll
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcQuery
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked

@[expose] public section

/-! # A successful response poll is followed by a read of the response buffer

A thread polls its CTA's response barrier only at its response wait (`clc_wait_site`), the
successful
poll leads to the load of the response (`clc_ok_next`), and the load reads the sixteen bytes of the
response buffer (`clcLoad_read`): from the instruction and the register that holds the buffer's
address, whatever the bytes are. So a successful response poll that is not the thread's last event
is
followed by that read (`poll_read_thm`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

/-- A thread state at the load of its response, by role. -/
def ThreadD.AtClcLoad : ThreadD → Prop
  | .inl _ => False
  | .inr (.loader l) => l.site = .clcLoad
  | .inr (.mma m) => m.site = .clcLoad
  | .inr (.sched s) => s.site = .clcLoad
  | .inr (.cons c) => c.site = .clcLoad

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- An acquire load of sixteen bytes at an aligned shared address fires a read of them. -/
theorem fires_ldAcquire128_rd {A : List Assumption} {t : TState}
    {d base : Nat} {pc : Nat} {e : Event} {o : Option TState} {loc : Loc}
    (hd : effAddr L g t .shared base 0 = .ok loc) (hsub : t.sub = 0) (hal : loc.addr % 16 = 0)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .load, space := some (.shared .cta), sem := .acquire, scope := some .cta,
        elem := .int .b 128, addr := ⟨.reg base 32, 0⟩, dsts := [some d] })) e o) :
    ∃ a bs, e.kind = .rd a bs ∧ a.loc = loc ∧ a.size = 16 := by
  have hm := memTmpl_acquire (A := A) (L := L) (g := g) (t := t) (sp := .shared) (base := base)
    (w := 32) (d := d)
    (a := { kind := .load, space := some (.shared .cta), sem := .acquire, scope := some .cta,
            elem := .int .b 128, addr := ⟨.reg base 32, 0⟩, dsts := [some d] })
    rfl rfl rfl rfl rfl rfl
  simp only [eventTmpl, hm, DType.width, acquireLoadTmpl, loadTmpl, hd, hsub, bind,
    Except.bind] at hf
  have helem : elemAcc loc (128 / 8) [d].length 0 = .ok { loc := loc.at (128 / 8 * 0), size :=
    128 / 8 } := by
    unfold elemAcc
    have hne : ¬ (128 / 8 = 0 ∨ loc.addr % (128 / 8 * [d].length) ≠ 0) := by
      simp only [List.length_singleton]
      omega
    simp only [hne, ↓reduceIte]
    rfl
  simp only [helem, Bool.false_eq_true, ↓reduceIte, Fires] at hf
  obtain ⟨bs, -, he, -⟩ := hf
  exact ⟨_, bs, by rw [he], by simp [Loc.at], by norm_num⟩

namespace Loader

theorem clcLoad_read (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hs : d.site = .clcLoad) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ a bs, e.kind = .rd a bs ∧ a.loc = respLoc L g ∧ a.size = 16 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  obtain ⟨site, m, n, q, cp, resp, x⟩ := d
  simp only at hs
  subst hs
  code_at hc
  subst hc
  have hr : t.regs 814 = some (b32 (L.sharedBase + 144)) :=
    (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by loader_values))
  exact fires_ldAcquire128_rd (effAddr_b32 hr (by omega)) hat.2.1 (by simp only; omega) hf

end Loader

namespace Mma

theorem clcLoad_read (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hs : d.site = .clcLoad) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ a bs, e.kind = .rd a bs ∧ a.loc = respLoc L g ∧ a.size = 16 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs
  subst hs
  code_at hc
  subst hc
  have hr : t.regs 851 = some (b32 (L.sharedBase + 144)) :=
    (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by mma_values))
  exact fires_ldAcquire128_rd (effAddr_b32 hr (by omega)) hat.2.1 (by simp only; omega) hf

end Mma

namespace Scheduler

theorem clcLoad_read (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hs : d.site = .clcLoad) (hat : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ a bs, e.kind = .rd a bs ∧ a.loc = respLoc L g ∧ a.size = 16 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  obtain ⟨site, ap, cp, resp, x⟩ := d
  simp only at hs
  subst hs
  code_at hc
  subst hc
  have hr : t.regs 640 = some (b32 (L.sharedBase + 144)) :=
    (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by sched_values))
  exact fires_ldAcquire128_rd (effAddr_b32 hr (by omega)) hat.2.1 (by simp only; omega) hf

end Scheduler

namespace Consumer

theorem clcLoad_read (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hs : d.site = .clcLoad) (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ a bs, e.kind = .rd a bs ∧ a.loc = respLoc L g ∧ a.size = 16 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs
  subst hs
  code_at hc
  subst hc
  have hr : t.regs 142 = some (b32 (L.sharedBase + 144)) :=
    (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by cons_values))
  exact fires_ldAcquire128_rd (effAddr_b32 hr (by omega)) hat.2.1 (by simp only; omega) hf

end Consumer

/-- A thread state at the load of its response fires a read of the response buffer. -/
theorem clcLoad_read {d : ThreadD} (hpre : Pre P L mem0) (hd : d.AtClcLoad) {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hat : (code L g).AtD d t)
    (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) :
    ∃ a bs, e.kind = .rd a bs ∧ a.loc = respLoc L g ∧ a.size = 16 := by
  rcases d with p | (l | m | s | c)
  · exact hd.elim
  · exact Loader.clcLoad_read hpre hd hat hc hf
  · exact Mma.clcLoad_read hpre hd hat hc hf
  · exact Scheduler.clcLoad_read hpre hd hat hc hf
  · exact Consumer.clcLoad_read hpre hd hat hc hf

/-- A thread's event on its CTA's response barrier is fired at its response wait. -/
theorem clc_wait_site (hpre : Pre P L mem0) (hg : g < L.threads) {d : ThreadD} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hat : (code L g).AtD d t)
    (hinv : (code L g).inv d) (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl Prod L g t ins.op) e o) {p : Nat} {ok acq : Bool}
    {sc : MbarScope} (hk : e.kind = .wait (clcResp L g) p ok acq sc) : d.AtClcWait := by
  rcases d with p' | (l | m | s | c)
  · exact (fires_notWait (eventTmpl_notWait (Prologue.code_notPoll p'.site hc)) hf _ _ _ _ _
    hk).elim
  · exact ((Loader.clc_sites hpre hg hat hc hf).1 p ok acq sc hk).1
  · exact ((Mma.clc_sites hpre hinv.1 hat hc hf).1 p ok acq sc hk).1
  · exact ((Scheduler.clc_sites hpre hg hinv.1 hat hc hf).1 p ok acq sc hk).1
  · exact ((Consumer.clc_sites hpre hg hinv.1 hat.2.2.2.2 hc hf).1 p ok acq sc hk).1

/-- A successful response poll of a thread at its response wait leads to its response load. -/
theorem clc_ok_next {d : ThreadD} (hd : d.AtClcWait) {m : Loc} {p pc : Nat} {acq : Bool}
    {sc : MbarScope} :
    ∃ d', (code L g).next d ⟨pc, .wait m p true acq sc⟩ = some (some d') ∧ d'.AtClcLoad := by
  rcases d with p' | (l | m' | s | c)
  · exact hd.elim
  · obtain ⟨s, m1, n, q, cp, r, x⟩ := l
    simp only [ThreadD.AtClcWait] at hd
    subst hd
    exact ⟨.inr (.loader ⟨.clcLoad, m1, n, q, cp, r, x⟩), by simp [code, Loader.next], rfl⟩
  · obtain ⟨s, w, q, fp, ap, cp, r, x⟩ := m'
    simp only [ThreadD.AtClcWait] at hd
    subst hd
    exact ⟨.inr (.mma ⟨.clcLoad, w, q, fp, ap, cp, r, x⟩), by simp [code, Mma.next], rfl⟩
  · obtain ⟨s, ap, cp, r, x⟩ := s
    simp only [ThreadD.AtClcWait] at hd
    subst hd
    exact ⟨.inr (.sched ⟨.clcLoad, ap, 1 - cp, r, x⟩), by simp [code, Scheduler.next], rfl⟩
  · obtain ⟨s, mm, n, m', n', cp, ap, r, x, acc, base⟩ := c
    simp only [ThreadD.AtClcWait] at hd
    subst hd
    exact ⟨.inr (.cons ⟨.clcLoad, mm, n, m', n', cp, ap, r, x, acc, base⟩),
      by simp [code, Consumer.next], rfl⟩

/-- **A successful poll of a thread's response barrier is followed by the read of the response
buffer.** A successful poll that is not the thread's last event is followed by an event that reads
the sixteen bytes of the CTA's response buffer. -/
theorem poll_read_thm {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads) {j pc p : Nat} {acq : Bool}
    {sc : MbarScope} (he : X.get (g, j) = some ⟨pc, .wait (clcResp L g) p true acq sc⟩)
    (hj : j + 1 < (X.tr g).length) :
    ∃ pcr a bs, X.get (g, j + 1) = some ⟨pcr, .rd a bs⟩ ∧ a.loc = respLoc L g ∧ a.size = 16 := by
  rcases (Frame.trace (fun _ => sound hpre) hX hg).fired he with ⟨σ, -, hσ, -⟩ | ⟨-, hub⟩
  · rcases σ with _ | d
    · exact absurd hσ (tracked hpre hX g j hg)
    obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
    have hd : d.AtClcWait :=
      clc_wait_site hpre hg hat hinv hc hf (p := p) (ok := true) (acq := acq) (sc := sc) rfl
    obtain ⟨d', hn, hd'⟩ := clc_ok_next (L := L) (g := g) hd (m := clcResp L g) (p := p) (pc := pc)
      (acq := acq) (sc := sc)
    have hσ' : Frame.stateAt (code L) X g (j + 1) = some (some d') := by
      have he0 : (X.tr g)[j]? = some ⟨pc, .wait (clcResp L g) p true acq sc⟩ := he
      have hσ0 : Frame.stateAt (code L) X g j = some (some d) := hσ
      rw [Frame.stateAt_succ he0, hσ0]
      exact hn
    obtain ⟨⟨epc, ek⟩, he'⟩ : ∃ e, X.get (g, j + 1) = some e := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨t', ins', o', hat', hinv', hc', hf'⟩ :=
      Frame.fired_site (fun _ => sound hpre) hX he' hσ'
    obtain ⟨a, bs, hk, ha, hs⟩ := clcLoad_read hpre hd' hat' hc' hf'
    simp only at hk
    subst hk
    exact ⟨epc, a, bs, he', ha, hs⟩
  · obtain ⟨pc', f, h⟩ := hub
    simp at h

end
end PTX.Kernels.Fp16Gemm8192.Proof
