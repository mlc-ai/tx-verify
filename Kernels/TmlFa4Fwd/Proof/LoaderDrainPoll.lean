-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderEntry
public import Kernels.TmlFa4Fwd.Flow.Code.Part029
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Flow.LoadShared

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

structure DrainWaitSite where
  pc : Nat
  result : Nat
  base : Nat
  phase : Nat

/-- The three KV release waits and warp 14's additional Q wait at the end of the loader. -/
def drainWaitSite : Fin 4 → DrainWaitSite
  | 0 => ⟨1866, 9619, 2288, 7180⟩
  | 1 => ⟨1877, 9620, 2289, 2290⟩
  | 2 => ⟨1888, 9621, 2291, 2292⟩
  | 3 => ⟨1893, 9622, 2305, 7192⟩

/-- A loader wait has the decoded CTA acquire, a success exit and a retry backedge. -/
def LoaderWaitCode (s : DrainWaitSite) : Prop :=
  kernel.code[s.pc]? = some ⟨none, .mbarWait s.result s.base 0 (.reg s.phase) true .cta⟩ ∧
    kernel.code[s.pc + 1]? = some ⟨some (s.result, false), .bra (s.pc + 3) true⟩ ∧
    kernel.code[s.pc + 2]? = some ⟨none, .bra s.pc true⟩

/-- The decoded wait instructions of one loader drain site. -/
theorem drainWaitCode (i : Fin 4) : LoaderWaitCode (drainWaitSite i) := by
  let actual (j : Fin 4) :=
    let s := drainWaitSite j
    (kernel.code[s.pc]?, kernel.code[s.pc + 1]?, kernel.code[s.pc + 2]?)
  let expected (j : Fin 4) : Option Instr × Option Instr × Option Instr :=
    let s := drainWaitSite j
    (some ⟨none, .mbarWait s.result s.base 0 (.reg s.phase) true .cta⟩,
     some ⟨some (s.result, false), .bra (s.pc + 3) true⟩,
     some ⟨none, .bra s.pc true⟩)
  have hTable : List.ofFn actual = List.ofFn expected := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hEntry := congrArg (fun row => row[i.val]?) hTable
  simp only [List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.some.injEq, actual, expected,
    Prod.mk.injEq] at hEntry
  exact hEntry

/-- The four loader waits are within the straight-line loader model. -/
theorem drainWaitRange :
    ∀ i : Fin 4, 174 ≤ (drainWaitSite i).pc ∧ (drainWaitSite i).pc + 3 < 1901 := by
  decide

/-- A loader poll is a CTA acquire on the decoded address and parity. -/
theorem loaderWaitTemplate {l : Launch} {g : Nat} {t : TState} (site : DrainWaitSite)
    (hCode : LoaderWaitCode site) (hBounds : 174 ≤ site.pc ∧ site.pc + 3 < 1906)
    {addr phase : Nat} (hAddr : addr < 2 ^ 32) (hAlign : addr % 8 = 0) (hPhase : phase < 2)
    (hpc : t.pc = site.pc) (hf : t.fault = none)
    (hBase : t.regs site.base = some (b32 addr))
    (hPar : t.regs site.phase = some (b32 phase)) :
    out kernel Assumptions.all l g t = .ev
      (.wait ⟨.shared, g / l.block, addr⟩ phase
        (fun ok => next (setReg t site.result (.pred ok))) true .cta) := by
  let loc : Loc := ⟨.shared, g / l.block, addr⟩
  have hc := hCode.1
  rw [← hpc] at hc
  rw [loaderOutCore (by omega) (by omega), out_event hf hc rfl rfl]
  have hEff : effAddr l g t .shared site.base 0 = .ok loc := by
    simpa only [Nat.cast_zero, Nat.add_zero, loc] using
      (effAddr_b32_off (g := g) (L := l) (off := 0) hBase (by omega))
  have hLoc : mbarLoc l g t site.base 0 = .ok loc := by
    simp [mbarLoc, hEff, loc, hAlign, bind, Except.bind, pure, Except.pure]
  have hPhase32 : phase < 2 ^ 32 := by omega
  have hPhase64 : phase < 2 ^ 64 := by omega
  change t.regs site.phase = some (b32 phase) at hPar
  have hBits : readBits l g t 32 (.reg site.phase) = .ok (BitVec.ofNat 64 phase) := by
    simp only [readBits, readReg, hPar, b32, bind, Except.bind, pure, Except.pure,
      truncBits_ofNat hPhase32 (by decide)]
  change Out.ev (eventTmpl [] l g t (.mbarWait site.result site.base 0 (.reg site.phase)
    true .cta)) = _
  simp [eventTmpl, widenMbarScope, tmaTmpl, hLoc, hBits, toNat_ofNat_lt hPhase64, hPhase,
    bind, Except.bind, pure, Except.pure, ofExec, loc]

theorem loaderAfterWait {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (site : DrainWaitSite) (hCode : LoaderWaitCode site)
    (hRange : 174 ≤ site.pc ∧ site.pc + 3 < 1906) (ok : Bool)
    (ht : At t (site.pc + 1) ((site.result, .pred ok) :: F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (if ok then site.pc + 3 else site.pc) F := by
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    hCode.2.1 ok ht ht.2.2.2.2.1 (by simp)
  have htPc : t.pc = site.pc + 1 := ht.1
  obtain ⟨huAll, _⟩ := loaderLinear (regs := []) (n := 1) (by omega) (by omega) htPc
    (by simp) rfl hu
  cases ok
  · have hPc : u.pc = site.pc + 2 := hU.1
    let v := { u with pc := site.pc }
    have hBack : run kernel [] l g 1 u = some v := by
      apply run_local hCode.2.2 rfl hU
      rw [execLocalA_nil]
      rfl
    obtain ⟨hLocal, _⟩ := loaderLinear (regs := []) (n := 1) (by omega) (by omega) hPc
      (by simp) rfl hBack
    exact ⟨v, run_rtg (run_comp huAll hLocal), rfl, hU.2.1, hU.2.2.1, hU.2.2.2.1,
      hU.2.2.2.2.2⟩
  · exact ⟨u, run_rtg huAll, hU.mono hU.2.2.2.2.2⟩

section
variable {l : Launch} {g addr phase : Nat} {t : TState} {F : List (Nat × Value)}
    (site : DrainWaitSite) (hCode : LoaderWaitCode site)
    (hRange : 174 ≤ site.pc ∧ site.pc + 3 < 1906) (hAddr : addr < 2 ^ 32) (hAlign : addr % 8 = 0)
    (hPhase : phase < 2) (hFresh : ∀ pair ∈ F, pair.1 ≠ site.result)
    (hBase : (site.base, b32 addr) ∈ F) (hPar : (site.phase, b32 phase) ∈ F) (ht : At t site.pc F)
include site hCode hRange hAddr hAlign hPhase hFresh hBase hPar ht

/-- Every terminated suffix at a loader poll has a finite sequence of failures followed by the
first successful observation. Both paths retain the operand facts of the polling state. -/
theorem loaderWaitTraceInPrefix {events : List Event} {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t events ending)
    (hProgress : ending = none ∨ ∃ e ∈ events, site.pc < e.pc) :
    let ev : Bool → Event := fun ok =>
      ⟨site.pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩
    ∃ n u rest, events = List.replicate n (ev false) ++ (ev true :: rest) ∧
      At u (site.pc + 3) F ∧ Run kernel Assumptions.all l g u rest ending := by
  dsimp only
  let loc : Loc := ⟨.shared, g / l.block, addr⟩
  induction events generalizing t with
  | nil =>
    rcases hProgress with hDone | ⟨e, he, _⟩
    · rw [hDone] at hr
      cases hr
    · cases he
  | cons e tail ih =>
    have hOut := loaderWaitTemplate (l := l) (g := g) site hCode hRange hAddr hAlign hPhase
      ht.1 ht.2.2.2.1
      (holds_mem ht.2.2.2.2 hBase) (holds_mem ht.2.2.2.2 hPar)
    let cont := fun ok => next (setReg t site.result (.pred ok))
    let tmpl := Tmpl.wait loc phase cont true .cta
    have hn : Next kernel Assumptions.all l g t t tmpl := ⟨.refl, hOut⟩
    obtain ⟨v, hf, hNext⟩ := hn.continuing_event (by
      rintro ⟨ok, _, hEq⟩
      cases hEq) hr
    obtain ⟨ok, rfl, hEq⟩ := hf
    obtain rfl := Option.some.inj hEq
    have hAt : At (cont ok) (site.pc + 1) ((site.result, .pred ok) :: F) := ht.set hFresh
    obtain ⟨u, hu, hU⟩ := loaderAfterWait site hCode hRange ok hAt
    have hAdvance : ending = none ∨ ∃ e ∈ tail, site.pc < e.pc := by
      apply hProgress.imp_right
      rintro ⟨e, he, hPc⟩
      refine ⟨e, (List.mem_cons.mp he).resolve_left ?_, hPc⟩
      intro h
      subst e
      exact Nat.lt_irrefl _ (ht.1 ▸ hPc)
    have hMore : tail ≠ [] := by
      intro h
      rw [h] at hNext hAdvance
      rcases hAdvance with hDone | ⟨e, he, _⟩
      · rw [hDone] at hNext
        cases hNext
      · cases he
    have hSuffix := hNext.after_local_nonempty hu hMore
    cases ok
    · obtain ⟨n, v, rest, he, hv, hRest⟩ := ih hU hSuffix hAdvance
      refine ⟨n + 1, v, rest, ?_, hv, hRest⟩
      simp only [ht.1, he, List.replicate_succ, List.cons_append, loc]
    · exact ⟨0, u, tail, by simp [ht.1, loc], hU, hSuffix⟩

/-- The terminated loader wait retains its existing interface. -/
theorem loaderWaitTrace {events : List Event} (hr : Run kernel Assumptions.all l g t events none) :
    let ev : Bool → Event := fun ok =>
      ⟨site.pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩
    ∃ n u rest, events = List.replicate n (ev false) ++ (ev true :: rest) ∧
      At u (site.pc + 3) F ∧ Run kernel Assumptions.all l g u rest none :=
  loaderWaitTraceInPrefix site hCode hRange hAddr hAlign hPhase hFresh hBase hPar ht hr (.inl rfl)

/-- A prefix containing a later event has passed the loader's wait, even if the
thread has not reached its terminal instruction. -/
theorem loaderWaitBeforeEvent {events : List Event} {outcome : Option TState} {later : Event}
    (hr : Run kernel Assumptions.all l g t events outcome) (hSeen : later ∈ events)
    (hLater : later.pc ≠ site.pc) :
    let ev : Bool → Event := fun ok =>
      ⟨site.pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩
    ∃ n rest, events = List.replicate n (ev false) ++ (ev true :: rest) ∧ later ∈ rest := by
  dsimp only
  let loc : Loc := ⟨.shared, g / l.block, addr⟩
  induction events generalizing t with
  | nil => cases hSeen
  | cons e tail ih =>
    have hOut := loaderWaitTemplate (l := l) (g := g) site hCode hRange hAddr hAlign hPhase
      ht.1 ht.2.2.2.1 (holds_mem ht.2.2.2.2 hBase) (holds_mem ht.2.2.2.2 hPar)
    let cont := fun ok => next (setReg t site.result (.pred ok))
    let tmpl := Tmpl.wait loc phase cont true .cta
    have hn : Next kernel Assumptions.all l g t t tmpl := ⟨.refl, hOut⟩
    obtain ⟨v, hf, hNext⟩ := hn.continuing_event (by
      rintro ⟨ok, _, hEq⟩
      cases hEq) hr
    obtain ⟨ok, rfl, hEq⟩ := hf
    obtain rfl := Option.some.inj hEq
    have hTail := (List.mem_cons.mp hSeen).resolve_left fun h =>
      hLater ((congrArg Event.pc h).trans ht.1)
    cases ok
    · have hAt : At (cont false) (site.pc + 1) ((site.result, .pred false) :: F) :=
        ht.set hFresh
      obtain ⟨u, hu, hU⟩ := loaderAfterWait site hCode hRange false hAt
      have hSuffix := hNext.after_local_nonempty hu (List.ne_nil_of_mem hTail)
      obtain ⟨n, rest, he, hMem⟩ := ih hU hSuffix hTail
      refine ⟨n + 1, rest, ?_, hMem⟩
      simp only [ht.1, he, List.replicate_succ, List.cons_append, loc]
    · exact ⟨0, tail, by simp [ht.1, loc], hTail⟩
end

/-- A completed drain suffix consists of the retry events and the successful CTA acquire. -/
theorem drainWaitTrace {l : Launch} {g addr phase : Nat} {t : TState} {F : List (Nat × Value)}
    (i : Fin 4) (hAddr : addr < 2 ^ 32) (hAlign : addr % 8 = 0) (hPhase : phase < 2)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (drainWaitSite i).result)
    (hBase : ((drainWaitSite i).base, b32 addr) ∈ F)
    (hPar : ((drainWaitSite i).phase, b32 phase) ∈ F)
    (ht : At t (drainWaitSite i).pc F) {events : List Event}
    (hr : Run kernel Assumptions.all l g t events none) :
    let ev : Bool → Event := fun ok =>
      ⟨(drainWaitSite i).pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩
    ∃ n u rest, events = List.replicate n (ev false) ++ (ev true :: rest) ∧
      At u ((drainWaitSite i).pc + 3) F ∧ Run kernel Assumptions.all l g u rest none := by
  have hRange := drainWaitRange i
  exact loaderWaitTrace (drainWaitSite i) (drainWaitCode i) ⟨hRange.1, by omega⟩
    hAddr hAlign hPhase hFresh hBase hPar ht hr

end
end PTX.Kernels.TmlFa4Fwd.Loader
